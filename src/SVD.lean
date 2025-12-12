/-
Copyright (c) 2025 FLYWHEEL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aleksandar Markovski

# Singular Value Decomposition

Singular values σᵢ(A) := √λᵢ(Aᴴ A). Standard factorisation A = UΣVᴴ.

## References

[1] Horn, R.A. & Johnson, C.R. (2012). Matrix Analysis, 2nd ed.
    Cambridge University Press. Ch. 7 (Positive Definite Matrices).
[2] Golub, G.H. & Van Loan, C.F. (2013). Matrix Computations, 4th ed.
    Johns Hopkins University Press. §2.5.
[3] Mathlib4 spectral theorem: `Matrix.IsHermitian.spectral_theorem`

## Implementation Notes

We build SVD from the spectral decomposition of the Gram matrix Aᴴ A which
is postive semidefinite hence admits real non-negative eigenvalues. The left
singular vectors are then constructed via polar decomposition (CFC.sqrt).
-/

import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Complex.Order
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.UnitaryGroup

open Matrix Polynomial
open scoped ComplexOrder MatrixOrder

namespace Matrix.SVD

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- σᵢ(A) := √λᵢ(Aᴴ A). Well-defined since Aᴴ A ≽ 0. -/
noncomputable def singularValues (A : Matrix n n ℂ) : n → ℝ :=
  fun i => Real.sqrt ((posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues i)

theorem singularValues_nonneg (A : Matrix n n ℂ) (i : n) : 0 ≤ singularValues A i :=
  Real.sqrt_nonneg _

theorem singularValues_sq (A : Matrix n n ℂ) (i : n) :
    (singularValues A i) ^ 2 = (posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues i := by
  unfold singularValues
  rw [Real.sq_sqrt]
  exact PosSemidef.eigenvalues_nonneg (posSemidef_conjTranspose_mul_self A) i

/-! ### Sorted Values

Antitone ordering σ₀ ≥ σ₁ ≥ ... via eigenvalues₀ from Mathlib.
-/

/-- Sorted singular values. Index 0 is largest (cf. Horn & Johnson Thm 7.3.5). -/
noncomputable def singularValues₀ (A : Matrix n n ℂ) : Fin (Fintype.card n) → ℝ :=
  fun k => Real.sqrt ((posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues₀ k)

/-- Sorted singular values are non-negative. -/
theorem singularValues₀_nonneg (A : Matrix n n ℂ) (k : Fin (Fintype.card n)) :
    0 ≤ singularValues₀ A k :=
  Real.sqrt_nonneg _

/-- Sorted singular values are antitone (decreasing): σ₀ ≥ σ₁ ≥ ⋯ ≥ σₙ₋₁. -/
theorem singularValues₀_antitone (A : Matrix n n ℂ) : Antitone (singularValues₀ A) := by
  intro k₁ k₂ hk
  unfold singularValues₀
  apply Real.sqrt_le_sqrt
  exact (posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues₀_antitone hk

/-- Equivalence between sorted and unsorted singular values via the canonical bijection.
    singularValues A i = singularValues₀ A ((Fintype.equivOfCardEq ...).symm i) -/
theorem singularValues_eq_singularValues₀ (A : Matrix n n ℂ) (i : n) :
    singularValues A i =
      singularValues₀ A ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm i) := by
  unfold singularValues singularValues₀
  -- eigenvalues i = eigenvalues₀ ((Fintype.equivOfCardEq ...).symm i) by Mathlib definition
  rfl

/-- The squared sorted singular values equal the sorted eigenvalues of Aᴴ * A. -/
theorem singularValues₀_sq (A : Matrix n n ℂ) (k : Fin (Fintype.card n)) :
    (singularValues₀ A k) ^ 2 = (posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues₀ k := by
  unfold singularValues₀
  rw [Real.sq_sqrt]
  -- Use eigenvalues_nonneg via the equivalence: eigenvalues i = eigenvalues₀ (equiv.symm i)
  -- So eigenvalues₀ k = eigenvalues (equiv k)
  have h_psd := posSemidef_conjTranspose_mul_self A
  have h_herm := h_psd.isHermitian
  -- eigenvalues₀ k ≥ 0 follows from eigenvalues being nonneg at equiv k
  let i := (Fintype.equivOfCardEq (Fintype.card_fin _) : Fin (Fintype.card n) ≃ n) k
  have hi : h_herm.eigenvalues₀ k = h_herm.eigenvalues i := by
    simp only [i, Matrix.IsHermitian.eigenvalues, Equiv.symm_apply_apply]
  rw [hi]
  exact h_psd.eigenvalues_nonneg i

/-! ### Singular Values of Zero Matrix -/

-- This section is probably overkill for just proving that sv(0) = 0
-- but I wanted to make sure all the plumbing was correct.
-- Feel free to golf these proofs.

/-- Helper: The characteristic polynomial of the zero matrix is X^n. -/
private lemma matrix_charpoly_zero : (0 : Matrix n n ℂ).charpoly = X ^ Fintype.card n := by
  rw [charpoly, charmatrix]
  simp only [map_zero, sub_zero]
  have h_scalar : scalar n (X : ℂ[X]) = diagonal (fun _ => X) := by rfl
  rw [h_scalar, det_diagonal]
  simp only [Finset.prod_const, Finset.card_univ]

/-- Helper: The eigenvalues₀ of the zero matrix are all zero.
    Proof: charpoly(0) = X^n, whose roots are all 0. -/
private theorem eigenvalues₀_zero (hZ : IsHermitian (0 : Matrix n n ℂ)) : hZ.eigenvalues₀ = 0 := by
  funext k
  have h_roots := hZ.roots_charpoly_eq_eigenvalues₀
  rw [matrix_charpoly_zero] at h_roots
  have h_roots_Xn : (X ^ Fintype.card n : Polynomial ℂ).roots =
      Multiset.replicate (Fintype.card n) 0 := by
    simp only [Polynomial.roots_pow, Polynomial.roots_X, Multiset.nsmul_singleton]
  rw [h_roots_Xn] at h_roots
  have h_all_zero : ∀ x ∈ Multiset.map (RCLike.ofReal ∘ hZ.eigenvalues₀) Finset.univ.val,
      x = (0 : ℂ) := by
    intro x hx
    rw [← h_roots] at hx
    simp only [Multiset.mem_replicate, ne_eq] at hx
    exact hx.2
  have h_k_zero : (RCLike.ofReal (hZ.eigenvalues₀ k) : ℂ) = 0 := by
    apply h_all_zero
    simp only [Multiset.mem_map, Finset.mem_val, Function.comp_apply]
    exact ⟨k, Finset.mem_univ k, rfl⟩
  simp only [Pi.zero_apply]
  exact RCLike.ofReal_injective h_k_zero

/-- Singular values of zero matrix are all zero. -/
theorem singularValues₀_zero : singularValues₀ (0 : Matrix n n ℂ) = 0 := by
  unfold singularValues₀
  funext k
  simp only [Pi.zero_apply]
  -- 0ᴴ * 0 = 0, so we need eigenvalues₀ of zero matrix
  have h_psd := posSemidef_conjTranspose_mul_self (0 : Matrix n n ℂ)
  have h_herm_zero : IsHermitian (0 : Matrix n n ℂ) := isHermitian_zero
  -- Use eigenvalues_eq_eigenvalues_iff to relate eigenvalues via charpoly
  have h_eig_eq := IsHermitian.eigenvalues_eq_eigenvalues_iff h_psd.isHermitian h_herm_zero
  have h_eig_rel : h_psd.isHermitian.eigenvalues = h_herm_zero.eigenvalues := by
    rw [h_eig_eq]
    simp only [conjTranspose_zero, zero_mul]
  -- eigenvalues₀ k = eigenvalues (equiv k)
  have h_eig_zero := eigenvalues₀_zero h_herm_zero
  have h_target_zero : h_psd.isHermitian.eigenvalues₀ k = 0 := by
    have h1 : h_psd.isHermitian.eigenvalues₀ k =
              h_psd.isHermitian.eigenvalues ((Fintype.equivOfCardEq (Fintype.card_fin _)) k) := by
      simp only [IsHermitian.eigenvalues, Equiv.symm_apply_apply]
    have h2 : h_herm_zero.eigenvalues₀ k =
              h_herm_zero.eigenvalues ((Fintype.equivOfCardEq (Fintype.card_fin _)) k) := by
      simp only [IsHermitian.eigenvalues, Equiv.symm_apply_apply]
    rw [h1]
    have h3 := congrFun h_eig_rel ((Fintype.equivOfCardEq (Fintype.card_fin _)) k)
    rw [h3, ← h2, h_eig_zero, Pi.zero_apply]
  rw [h_target_zero, Real.sqrt_zero]

/-! ### Singular Vectors -/

-- Naming convention: left vs right is confusing. Here's how I remember it:
-- - rightUnitary V: eigenvectors of A^H A ("right" because Av = σ u)
-- - leftUnitary U: eigenvectors of A A^H ("left" because A^H u = σ v)
-- If anyone has a better mnemonic please share!

/-- The right singular vectors V: an orthonormal basis of eigenvectors of Aᴴ * A.
    These form a unitary matrix where column i is the eigenvector for σᵢ². -/
noncomputable def rightUnitary (A : Matrix n n ℂ) : unitaryGroup n ℂ :=
  (posSemidef_conjTranspose_mul_self A).isHermitian.eigenvectorUnitary

/-- The left singular vectors U: an orthonormal basis of eigenvectors of A * Aᴴ.
    These form a unitary matrix where column i is the eigenvector for σᵢ². -/
noncomputable def leftUnitary (A : Matrix n n ℂ) : unitaryGroup n ℂ :=
  (posSemidef_self_mul_conjTranspose A).isHermitian.eigenvectorUnitary

/-- The diagonal matrix Σ containing the singular values along its diagonal. -/
noncomputable def singularDiagonal (A : Matrix n n ℂ) : Matrix n n ℂ :=
  diagonal (Complex.ofReal ∘ singularValues A)

-- CFC = continuous functional calculus. Took me a while to figure out what this was.
-- See: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Basic.html

/-- The square root of Aᴴ*A, which is positive semidefinite by construction.
    This matrix P = √(Aᴴ*A) is central to polar decomposition: A = U*P. -/
noncomputable def sqrtConjTransposeMulSelf (A : Matrix n n ℂ) : Matrix n n ℂ :=
  CFC.sqrt (conjTranspose A * A)

/-- The square root of Aᴴ*A is positive semidefinite. -/
theorem sqrtConjTransposeMulSelf_isPosSemidef (A : Matrix n n ℂ) :
    (sqrtConjTransposeMulSelf A).PosSemidef := by
  unfold sqrtConjTransposeMulSelf
  exact (CFC.sqrt_nonneg (Aᴴ * A)).posSemidef

/-- The square root of Aᴴ*A is Hermitian (since it's PosSemidef). -/
theorem sqrtConjTransposeMulSelf_isHermitian (A : Matrix n n ℂ) :
    (sqrtConjTransposeMulSelf A).IsHermitian :=
  (sqrtConjTransposeMulSelf_isPosSemidef A).isHermitian

/-- Squaring √(Aᴴ*A) recovers Aᴴ*A. -/
theorem sqrtConjTransposeMulSelf_sq (A : Matrix n n ℂ) :
    (sqrtConjTransposeMulSelf A) ^ 2 = conjTranspose A * A := by
  unfold sqrtConjTransposeMulSelf
  have h : (0 : Matrix n n ℂ) ≤ Aᴴ * A := (posSemidef_conjTranspose_mul_self A).nonneg
  exact CFC.sq_sqrt (Aᴴ * A) h

/-- √(Aᴴ*A) * √(Aᴴ*A) = Aᴴ*A. -/
theorem sqrtConjTransposeMulSelf_mul_self (A : Matrix n n ℂ) :
    sqrtConjTransposeMulSelf A * sqrtConjTransposeMulSelf A = conjTranspose A * A := by
  unfold sqrtConjTransposeMulSelf
  have h : (0 : Matrix n n ℂ) ≤ Aᴴ * A := (posSemidef_conjTranspose_mul_self A).nonneg
  exact CFC.sqrt_mul_sqrt_self (Aᴴ * A) h

-- Polar decomposition: A = U·P where P = √(A*A) is psd and U unitary

/-- Key computational lemma: Vᴴ * (Aᴴ * A) * V = diag(eigenvalues). -/
theorem svd_action (A : Matrix n n ℂ) :
    let V : Matrix n n ℂ := rightUnitary A
    let eig := (posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues
    Vᴴ * (Aᴴ * A) * V = diagonal (Complex.ofReal ∘ eig) := by
  intro V eig
  have h_spectral : Aᴴ * A = V * diagonal (Complex.ofReal ∘ eig) * Vᴴ :=
    (posSemidef_conjTranspose_mul_self A).isHermitian.spectral_theorem
  have hVV : Vᴴ * V = 1 := mem_unitaryGroup_iff'.mp (rightUnitary A).2
  calc Vᴴ * (Aᴴ * A) * V
      = Vᴴ * (V * diagonal (Complex.ofReal ∘ eig) * Vᴴ) * V := by simp only [h_spectral]
    _ = Vᴴ * V * diagonal (Complex.ofReal ∘ eig) * Vᴴ * V := by simp only [Matrix.mul_assoc]
    _ = 1 * diagonal (Complex.ofReal ∘ eig) * Vᴴ * V := by rw [hVV]
    _ = diagonal (Complex.ofReal ∘ eig) * Vᴴ * V := by rw [one_mul]
    _ = diagonal (Complex.ofReal ∘ eig) * (Vᴴ * V) := by simp only [Matrix.mul_assoc]
    _ = diagonal (Complex.ofReal ∘ eig) * 1 := by rw [hVV]
    _ = diagonal (Complex.ofReal ∘ eig) := by rw [mul_one]

/-- Corollary: (A*V)ᴴ * (A*V) = diag(σ²). -/
theorem conjTranspose_AV_mul_AV (A : Matrix n n ℂ) :
    let V : Matrix n n ℂ := rightUnitary A
    let eig := (posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues
    (A * V)ᴴ * (A * V) = diagonal (Complex.ofReal ∘ eig) := by
  intro V eig
  rw [conjTranspose_mul]
  calc Vᴴ * Aᴴ * (A * V)
      = Vᴴ * (Aᴴ * A) * V := by simp only [Matrix.mul_assoc]
    _ = diagonal (Complex.ofReal ∘ eig) := svd_action A

-- For σᵢ ≠ 0, left singular vector uᵢ = (1/σᵢ)(A·vᵢ)

/-- The (i,j) entry of (A*V)ᴴ*(A*V) equals inner product of cols i and j. -/
lemma AV_conjTranspose_mul_AV_apply (A : Matrix n n ℂ) (i j : n) :
    let V : Matrix n n ℂ := rightUnitary A
    let AV := A * V
    (AVᴴ * AV) i j = ∑ k, star (AV k i) * AV k j := by
  simp only [conjTranspose_apply, mul_apply]

/-- Columns of A*V are orthogonal: for i ≠ j, the inner product is 0. -/
lemma AV_columns_orthogonal (A : Matrix n n ℂ) (i j : n) (hij : i ≠ j) :
    let V : Matrix n n ℂ := rightUnitary A
    let AV := A * V
    ∑ k, star (AV k i) * AV k j = 0 := by
  intro V AV
  have h2 := conjTranspose_AV_mul_AV A
  simp only at h2
  have h1 : (AVᴴ * AV) i j = ∑ k, star (AV k i) * AV k j := by
    simp only [conjTranspose_apply, mul_apply]
  rw [h1.symm, h2, diagonal_apply, Function.comp_apply, if_neg hij]

/-- Squared norm of column i of A*V equals σᵢ² (using singularValues). -/
lemma AV_column_norm_sq (A : Matrix n n ℂ) (i : n) :
    let V : Matrix n n ℂ := rightUnitary A
    let AV := A * V
    ∑ k, star (AV k i) * AV k i = Complex.ofReal ((singularValues A i) ^ 2) := by
  intro V AV
  have h2 := conjTranspose_AV_mul_AV A
  simp only at h2
  have h1 : (AVᴴ * AV) i i = ∑ k, star (AV k i) * AV k i := by
    simp only [conjTranspose_apply, mul_apply]
  simp only [singularValues]
  rw [h1.symm, h2, diagonal_apply_eq, Function.comp_apply]
  congr 1
  rw [Real.sq_sqrt]
  exact (posSemidef_conjTranspose_mul_self A).eigenvalues_nonneg i

/-- For σᵢ ≠ 0, the i-th left singular vector is (1/σᵢ) · (column i of A·V).
    This vector has unit norm and is orthogonal to other left singular vectors. -/
noncomputable def leftSingularVectorNonzero (A : Matrix n n ℂ) (i : n)
    (_ : singularValues A i ≠ 0) : n → ℂ :=
  let AV := A * (rightUnitary A : Matrix n n ℂ)
  fun k => (Complex.ofReal (singularValues A i))⁻¹ * AV k i

/-- The inner product of left singular vectors for i ≠ j is 0. -/
theorem leftSingularVectorNonzero_orthogonal (A : Matrix n n ℂ) (i j : n)
    (hi : singularValues A i ≠ 0) (hj : singularValues A j ≠ 0) (hij : i ≠ j) :
    ∑ k, star (leftSingularVectorNonzero A i hi k) * (leftSingularVectorNonzero A j hj k) = 0 := by
  unfold leftSingularVectorNonzero
  have h_orth := AV_columns_orthogonal A i j hij
  simp only [star_mul', RCLike.star_def, map_inv₀, Complex.conj_ofReal]
  have factor : ∀ k : n,
      ((Complex.ofReal (singularValues A i) : ℂ))⁻¹ *
        (starRingEnd ℂ) ((A * (rightUnitary A : Matrix n n ℂ)) k i) *
        (((Complex.ofReal (singularValues A j) : ℂ))⁻¹ * (A * (rightUnitary A : Matrix n n ℂ)) k j) =
      ((Complex.ofReal (singularValues A i) : ℂ))⁻¹ * ((Complex.ofReal (singularValues A j) : ℂ))⁻¹ *
        ((starRingEnd ℂ) ((A * (rightUnitary A : Matrix n n ℂ)) k i) * (A * (rightUnitary A : Matrix n n ℂ)) k j) := by
    intro k; ring
  conv_lhs => arg 2; ext k; rw [factor k]
  rw [← Finset.mul_sum]
  have h_star_eq : ∀ k : n, (starRingEnd ℂ) ((A * (rightUnitary A : Matrix n n ℂ)) k i) =
      star ((A * (rightUnitary A : Matrix n n ℂ)) k i) := fun _ => rfl
  simp_rw [h_star_eq, h_orth, mul_zero]

/-- The squared norm (inner product with self) of a left singular vector is 1.
    This uses: ‖uᵢ‖² = (1/σᵢ)² · ‖column i of A*V‖² = (1/σᵢ)² · σᵢ² = 1 -/
theorem leftSingularVectorNonzero_inner_self (A : Matrix n n ℂ) (i : n)
    (hi : singularValues A i ≠ 0) :
    ∑ k, star (leftSingularVectorNonzero A i hi k) * (leftSingularVectorNonzero A i hi k) = 1 := by
  unfold leftSingularVectorNonzero
  have h_norm := AV_column_norm_sq A i
  simp only [star_mul', RCLike.star_def, map_inv₀, Complex.conj_ofReal]
  have factor : ∀ k : n,
      ((Complex.ofReal (singularValues A i) : ℂ))⁻¹ *
        (starRingEnd ℂ) ((A * (rightUnitary A : Matrix n n ℂ)) k i) *
        (((Complex.ofReal (singularValues A i) : ℂ))⁻¹ * (A * (rightUnitary A : Matrix n n ℂ)) k i) =
      ((Complex.ofReal (singularValues A i) : ℂ))⁻¹ * ((Complex.ofReal (singularValues A i) : ℂ))⁻¹ *
        ((starRingEnd ℂ) ((A * (rightUnitary A : Matrix n n ℂ)) k i) * (A * (rightUnitary A : Matrix n n ℂ)) k i) := by
    intro k; ring
  conv_lhs => arg 2; ext k; rw [factor k]
  rw [← Finset.mul_sum]
  have h_star_eq : ∀ k : n, (starRingEnd ℂ) ((A * (rightUnitary A : Matrix n n ℂ)) k i) =
      star ((A * (rightUnitary A : Matrix n n ℂ)) k i) := fun _ => rfl
  simp_rw [h_star_eq, h_norm]
  -- Now: (σᵢ⁻¹)² · σᵢ² = 1
  have hi' : (Complex.ofReal (singularValues A i) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact hi
  have h_sq_eq : (Complex.ofReal ((singularValues A i) ^ 2) : ℂ) =
      ((Complex.ofReal (singularValues A i) : ℂ)) * ((Complex.ofReal (singularValues A i) : ℂ)) := by
    rw [sq, Complex.ofReal_mul]
  rw [h_sq_eq]
  field_simp

/-- When σᵢ = 0, column i of A*V is the zero vector.
    This follows from ||(A*V)[:,i]||² = σᵢ² = 0. -/
lemma AV_column_zero_of_singularValue_zero (A : Matrix n n ℂ) (i : n)
    (hi : singularValues A i = 0) :
    ∀ k, (A * (rightUnitary A : Matrix n n ℂ)) k i = 0 := by
  intro k
  -- The sum ∑ k, star(AV k i) * (AV k i) = σᵢ² = 0
  have h_sum := AV_column_norm_sq A i
  simp only at h_sum
  rw [hi] at h_sum
  simp only [sq, mul_zero, Complex.ofReal_zero] at h_sum
  -- Each term star(z) * z = |z|² ≥ 0
  let AV := (A * (rightUnitary A : Matrix n n ℂ))
  -- star(z) * z = normSq(z) for complex numbers
  have h_eq_normSq : ∀ j, star (AV j i) * AV j i = Complex.normSq (AV j i) := by
    intro j
    have h1 : star (AV j i) = (starRingEnd ℂ) (AV j i) := rfl
    rw [h1]
    have h2 : (starRingEnd ℂ) (AV j i) * AV j i = AV j i * (starRingEnd ℂ) (AV j i) := mul_comm _ _
    rw [h2]
    rw [mul_comm]
    exact Complex.normSq_eq_conj_mul_self.symm
  -- The sum of normSq values = 0
  have h_sum_normSq_complex : ∑ j, (Complex.normSq (AV j i) : ℂ) = 0 := by
    conv_lhs => rw [← Finset.sum_congr rfl (fun j _ => h_eq_normSq j)]
    exact h_sum
  -- Extract as a real sum
  have h_sum_normSq : ∑ j, Complex.normSq (AV j i) = 0 := by
    have h_real : (∑ j, Complex.normSq (AV j i) : ℂ) = (∑ j, Complex.normSq (AV j i) : ℝ) := by
      rw [Complex.ofReal_sum]
    rw [h_real] at h_sum_normSq_complex
    exact Complex.ofReal_injective h_sum_normSq_complex
  -- Sum of nonneg = 0 implies each = 0
  have h_each_zero := @Finset.sum_eq_zero_iff_of_nonneg n ℝ _ _ (fun j => Complex.normSq (AV j i))
    Finset.univ _ (fun j _ => Complex.normSq_nonneg _)
  rw [h_each_zero] at h_sum_normSq
  have hk := h_sum_normSq k (Finset.mem_univ k)
  change Complex.normSq (AV k i) = 0 at hk
  exact Complex.normSq_eq_zero.mp hk

/-! ### EuclideanSpace Bridge for Orthonormal Basis Extension

Constructing the unitary U for full SVD.
-/

set_option linter.unusedSectionVars false in
/-- Inner product on EuclideanSpace matches our sum formula for star-multiplication. -/
lemma inner_euclidean_eq_sum (x y : n → ℂ) :
    @inner ℂ (EuclideanSpace ℂ n) _
      ((WithLp.equiv 2 (n → ℂ)).symm x)
      ((WithLp.equiv 2 (n → ℂ)).symm y)
    = ∑ i, star (x i) * y i := by
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply]
  have h1 : ∀ i, ((WithLp.equiv 2 (n → ℂ)).symm x).ofLp i = x i := fun _ => rfl
  have h2 : ∀ i, ((WithLp.equiv 2 (n → ℂ)).symm y).ofLp i = y i := fun _ => rfl
  simp_rw [h1, h2, ← Complex.star_def, mul_comm]

/-- Left singular vector as EuclideanSpace element. -/
noncomputable def leftSingularVectorEuclidean (A : Matrix n n ℂ) (i : n)
    (hi : singularValues A i ≠ 0) : EuclideanSpace ℂ n :=
  (WithLp.equiv 2 (n → ℂ)).symm (leftSingularVectorNonzero A i hi)

/-- Extended function for all indices: uses left singular vector when σᵢ ≠ 0, else 0.
    The 0 values will be replaced by the orthonormal basis extension. -/
noncomputable def leftSingularVectorExtended (A : Matrix n n ℂ) : n → EuclideanSpace ℂ n :=
  fun i => if h : singularValues A i ≠ 0
           then leftSingularVectorEuclidean A i h
           else 0

/-- The set of indices with nonzero singular values. -/
def nonzeroSingularIndices (A : Matrix n n ℂ) : Set n :=
  {i | singularValues A i ≠ 0}

/-- The left singular vectors restricted to nonzero singular value indices form an orthonormal set. -/
theorem leftSingularVectorExtended_orthonormal_on_nonzero (A : Matrix n n ℂ) :
    Orthonormal ℂ ((nonzeroSingularIndices A).restrict (leftSingularVectorExtended A)) := by
  rw [orthonormal_iff_ite]
  intro ⟨i, hi⟩ ⟨j, hj⟩
  simp only [Set.restrict_apply, nonzeroSingularIndices, Set.mem_setOf_eq] at hi hj ⊢
  have hi' : (if h : singularValues A i ≠ 0 then leftSingularVectorEuclidean A i h else 0)
            = leftSingularVectorEuclidean A i hi := dif_pos hi
  have hj' : (if h : singularValues A j ≠ 0 then leftSingularVectorEuclidean A j h else 0)
            = leftSingularVectorEuclidean A j hj := dif_pos hj
  simp only [leftSingularVectorExtended]
  rw [hi', hj']
  simp only [leftSingularVectorEuclidean]
  rw [inner_euclidean_eq_sum]
  by_cases h : i = j
  · subst h
    simp only [↓reduceIte]
    exact leftSingularVectorNonzero_inner_self A i hi
  · have hij' : (⟨i, hi⟩ : {i : n | singularValues A i ≠ 0}) ≠ ⟨j, hj⟩ := by
      intro heq; apply h; exact Subtype.ext_iff.mp heq
    simp only [Subtype.mk.injEq, h, ↓reduceIte]
    exact leftSingularVectorNonzero_orthogonal A i j hi hj h

/-- Extend the orthonormal left singular vectors to a full orthonormal basis. -/
noncomputable def extendedONB (A : Matrix n n ℂ) :
    OrthonormalBasis n ℂ (EuclideanSpace ℂ n) :=
  ((leftSingularVectorExtended_orthonormal_on_nonzero A).exists_orthonormalBasis_extension_of_card_eq
    finrank_euclideanSpace).choose

/-- The extended ONB agrees with left singular vectors on nonzero singular value indices. -/
theorem extendedONB_spec (A : Matrix n n ℂ) :
    ∀ i, i ∈ nonzeroSingularIndices A → (extendedONB A) i = leftSingularVectorExtended A i :=
  ((leftSingularVectorExtended_orthonormal_on_nonzero A).exists_orthonormalBasis_extension_of_card_eq
    finrank_euclideanSpace).choose_spec

/-- Convert an orthonormal basis of EuclideanSpace to a matrix (column j = basis vector j). -/
noncomputable def onbToMatrix (b : OrthonormalBasis n ℂ (EuclideanSpace ℂ n)) : Matrix n n ℂ :=
  fun i j => (b j) i

set_option linter.unusedSectionVars false in
/-- The inner product of columns equals the inner product of basis vectors. -/
lemma onbToMatrix_inner (b : OrthonormalBasis n ℂ (EuclideanSpace ℂ n)) (i j : n) :
    (star (onbToMatrix b) * onbToMatrix b) i j =
    @inner ℂ (EuclideanSpace ℂ n) _ (b i) (b j) := by
  simp only [mul_apply, star_apply, onbToMatrix]
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply]
  congr 1
  ext k
  simp only [star, ← Complex.star_def, mul_comm]

/-- A matrix built from an orthonormal basis is unitary. -/
theorem onbToMatrix_mem_unitaryGroup (b : OrthonormalBasis n ℂ (EuclideanSpace ℂ n)) :
    onbToMatrix b ∈ unitaryGroup n ℂ := by
  rw [mem_unitaryGroup_iff']
  ext i j
  rw [onbToMatrix_inner, one_apply]
  have h_on : Orthonormal ℂ b := b.orthonormal
  rw [orthonormal_iff_ite] at h_on
  exact h_on i j

/-- The constructed unitary matrix U for SVD.
    Columns are: left singular vectors for σᵢ ≠ 0, orthonormal extension for σᵢ = 0. -/
noncomputable def constructedU (A : Matrix n n ℂ) : unitaryGroup n ℂ :=
  ⟨onbToMatrix (extendedONB A), onbToMatrix_mem_unitaryGroup _⟩

/-- Column j of constructed U equals the left singular vector when σⱼ ≠ 0. -/
theorem constructedU_column_eq (A : Matrix n n ℂ) (j : n) (hj : singularValues A j ≠ 0) :
    (fun i => (constructedU A : Matrix n n ℂ) i j) = leftSingularVectorNonzero A j hj := by
  ext i
  simp only [constructedU, onbToMatrix]
  have hj_mem : j ∈ nonzeroSingularIndices A := hj
  have h_spec := extendedONB_spec A j hj_mem
  have h_expand : leftSingularVectorExtended A j = leftSingularVectorEuclidean A j hj := dif_pos hj
  rw [h_spec, h_expand]
  simp only [leftSingularVectorEuclidean]
  rfl

/-- Key relationship: A * V = U * Σ (where U = constructedU).
    This is the core equation that makes SVD work:
    - For σⱼ ≠ 0: column j of A*V equals σⱼ times column j of U (by definition of U)
    - For σⱼ = 0: column j of A*V is zero, and σⱼ * column j of U is also zero -/
theorem AV_eq_constructedU_mul_sigma (A : Matrix n n ℂ) :
    A * (rightUnitary A : Matrix n n ℂ) =
    (constructedU A : Matrix n n ℂ) * diagonal (Complex.ofReal ∘ singularValues A) := by
  ext i j
  simp only [mul_apply, diagonal_apply, Function.comp_apply]
  -- RHS simplifies: ∑ x, U i x * (if x = j then σ x else 0) = U i j * σ j
  have h_rhs : ∑ x, (constructedU A : Matrix n n ℂ) i x *
               (if x = j then Complex.ofReal (singularValues A x) else 0) =
               (constructedU A : Matrix n n ℂ) i j * Complex.ofReal (singularValues A j) := by
    rw [Finset.sum_eq_single j]
    · simp only [↓reduceIte]
    · intro b _ hbj; simp only [hbj, ↓reduceIte, mul_zero]
    · intro hj_not_mem; exact absurd (Finset.mem_univ j) hj_not_mem
  rw [h_rhs]
  by_cases hj : singularValues A j ≠ 0
  · -- Case σⱼ ≠ 0: (A*V)ᵢⱼ = σⱼ * Uᵢⱼ
    have h_col := constructedU_column_eq A j hj
    have h_U_eq : (constructedU A : Matrix n n ℂ) i j = leftSingularVectorNonzero A j hj i := by
      exact congrFun h_col i
    rw [h_U_eq]
    simp only [leftSingularVectorNonzero]
    -- Uᵢⱼ = (1/σⱼ) * (A*V)ᵢⱼ, so σⱼ * Uᵢⱼ = (A*V)ᵢⱼ
    have hj' : (Complex.ofReal (singularValues A j) : ℂ) ≠ 0 := by
      simp only [ne_eq, Complex.ofReal_eq_zero]; exact hj
    -- LHS is (A * V) i j by definition
    simp only [mul_apply]
    field_simp
  · -- Case σⱼ = 0: both sides are 0
    push_neg at hj
    have h_AV_zero := AV_column_zero_of_singularValue_zero A j hj
    simp only [hj, Complex.ofReal_zero, mul_zero]
    -- LHS: ∑ x, A i x * V x j = (A * V) i j = 0
    have h_lhs : ∑ x, A i x * (rightUnitary A : Matrix n n ℂ) x j =
                 (A * (rightUnitary A : Matrix n n ℂ)) i j := rfl
    rw [h_lhs, h_AV_zero i]

/-! ### Main Decomposition Theorem -/

/-- **Singular Value Decomposition (Existence Form)**:
    Any square complex matrix A can be decomposed as A = U * Σ * Vᴴ
    where:
    - U is unitary (the left singular vectors)
    - V is unitary (the right singular vectors)
    - Σ is diagonal with non-negative real entries (the singular values)

    This follows from the spectral theorem applied to the positive semidefinite
    matrices Aᴴ * A and A * Aᴴ.

    **Proof Strategy:**
    1. V = eigenvectors of Aᴴ*A (rightUnitary)
    2. σᵢ = √(eigenvalues of Aᴴ*A) (singularValues)
    3. Construct U such that A*V = U*Σ
       - For σᵢ ≠ 0: uᵢ = (1/σᵢ)*A*vᵢ
       - For σᵢ = 0: uᵢ is any orthonormal extension
    4. Verify A = U*Σ*Vᴴ -/
theorem svd_decomposition (A : Matrix n n ℂ) :
    ∃ (U V : unitaryGroup n ℂ) (σ : n → ℝ),
      (∀ i, 0 ≤ σ i) ∧
      A = (U : Matrix n n ℂ) * diagonal (Complex.ofReal ∘ σ) * star (V : Matrix n n ℂ) := by
  -- Use V from spectral decomposition of Aᴴ*A
  -- Use U constructed by extending orthonormal left singular vectors
  use constructedU A, rightUnitary A, singularValues A
  constructor
  · intro i; exact Real.sqrt_nonneg _
  · -- Main equation: A = U * Σ * Vᴴ
    -- From AV_eq_constructedU_mul_sigma: A * V = U * Σ
    -- Multiply both sides by Vᴴ: A * V * Vᴴ = U * Σ * Vᴴ
    -- Since V is unitary: V * Vᴴ = I, so A = U * Σ * Vᴴ
    have h_AV := AV_eq_constructedU_mul_sigma A
    have h_V_unitary : (rightUnitary A : Matrix n n ℂ) * star (rightUnitary A : Matrix n n ℂ) = 1 :=
      mem_unitaryGroup_iff.mp (rightUnitary A).2
    calc A = A * 1 := by rw [mul_one]
      _ = A * ((rightUnitary A : Matrix n n ℂ) * star (rightUnitary A : Matrix n n ℂ)) := by rw [h_V_unitary]
      _ = (A * (rightUnitary A : Matrix n n ℂ)) * star (rightUnitary A : Matrix n n ℂ) := by rw [mul_assoc]
      _ = ((constructedU A : Matrix n n ℂ) * diagonal (Complex.ofReal ∘ singularValues A)) *
          star (rightUnitary A : Matrix n n ℂ) := by rw [h_AV]
      _ = (constructedU A : Matrix n n ℂ) * diagonal (Complex.ofReal ∘ singularValues A) *
          star (rightUnitary A : Matrix n n ℂ) := by rw [mul_assoc]

/-! ### Properties of Singular Values -/

/-- The eigenvalues of A * Aᴴ equal the eigenvalues of Aᴴ * A.
    This is a direct consequence of `charpoly_mul_comm` which states that
    (A * B).charpoly = (B * A).charpoly for any square matrices A, B.
    Combined with `eigenvalues_eq_eigenvalues_iff` for Hermitian matrices,
    this gives pointwise equality of eigenvalues. -/
theorem eigenvalues_self_mul_conjTranspose_eq_conjTranspose_mul_self (A : Matrix n n ℂ) :
    (posSemidef_self_mul_conjTranspose A).isHermitian.eigenvalues =
    (posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues := by
  rw [IsHermitian.eigenvalues_eq_eigenvalues_iff]
  exact charpoly_mul_comm A Aᴴ

/-- The singular values of Aᴴ equal the singular values of A.

    **Proof outline:**
    - singularValues(Aᴴ) = sqrt(eigenvalues((Aᴴ)ᴴ * Aᴴ)) = sqrt(eigenvalues(A * Aᴴ))
    - singularValues(A) = sqrt(eigenvalues(Aᴴ * A))
    - By `charpoly_mul_comm`: (A * Aᴴ).charpoly = (Aᴴ * A).charpoly
    - For Hermitian matrices with equal charpoly, eigenvalues are equal pointwise
    - Therefore singularValues(Aᴴ) = singularValues(A) -/
theorem singularValues_conjTranspose (A : Matrix n n ℂ) :
    singularValues (conjTranspose A) = singularValues A := by
  ext i
  simp only [singularValues]
  -- Goal: sqrt(eigenvalues((Aᴴ)ᴴ * Aᴴ) i) = sqrt(eigenvalues(Aᴴ * A) i)
  -- Since (Aᴴ)ᴴ = A, this becomes: sqrt(eigenvalues(A * Aᴴ) i) = sqrt(eigenvalues(Aᴴ * A) i)

  -- Step 1: (Aᴴ)ᴴ * Aᴴ = A * Aᴴ (by conjTranspose_conjTranspose)
  have h_matrix_eq : conjTranspose (conjTranspose A) * conjTranspose A = A * conjTranspose A := by
    rw [conjTranspose_conjTranspose]

  -- Step 2: eigenvalues of (Aᴴ)ᴴ * Aᴴ = eigenvalues of A * Aᴴ (same matrix!)
  have h1 : (posSemidef_conjTranspose_mul_self (Aᴴ)).isHermitian.eigenvalues i =
            (posSemidef_self_mul_conjTranspose A).isHermitian.eigenvalues i := by
    have h_charpoly : (conjTranspose (conjTranspose A) * conjTranspose A).charpoly =
                      (A * conjTranspose A).charpoly := by
      rw [h_matrix_eq]
    have := IsHermitian.eigenvalues_eq_eigenvalues_iff
        (posSemidef_conjTranspose_mul_self (Aᴴ)).isHermitian
        (posSemidef_self_mul_conjTranspose A).isHermitian
    rw [this.mpr h_charpoly]

  -- Step 3: eigenvalues of A * Aᴴ = eigenvalues of Aᴴ * A (by charpoly_mul_comm)
  have h2 : (posSemidef_self_mul_conjTranspose A).isHermitian.eigenvalues i =
            (posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues i := by
    exact congrFun (eigenvalues_self_mul_conjTranspose_eq_conjTranspose_mul_self A) i

  rw [h1, h2]

/-! ### Helper lemmas for characteristic polynomial similarity invariance -/

/-- Scalar matrices commute with all matrices. -/
private lemma scalar_mul_eq_mul_scalar' (M : Matrix n n (Polynomial ℂ)) (x : Polynomial ℂ) :
    M * scalar n x = scalar n x * M := by
  have h : Commute (scalar n x) M := Matrix.scalar_commute x (fun r' => mul_comm x r') M
  exact h.symm.eq

/-- The characteristic matrix expressed as scalar minus map. -/
private lemma charmatrix_eq_scalar_sub_map (M : Matrix n n ℂ) :
    M.charmatrix = scalar n Polynomial.X - M.map Polynomial.C := by
  ext i j
  simp only [charmatrix_apply, sub_apply, scalar_apply, diagonal, of_apply, map_apply]

/-- Ring homomorphism map preserves inverses for invertible matrices. -/
private lemma map_inv_of_isUnit {R S : Type*} [CommRing R] [CommRing S]
    (M : Matrix n n R) (f : R →+* S) (hM : IsUnit M.det) :
    (M⁻¹).map f = (M.map f)⁻¹ := by
  have h1 : M.map f = f.mapMatrix M := by ext; simp [RingHom.mapMatrix_apply]
  have h2 : M⁻¹.map f = f.mapMatrix M⁻¹ := by ext; simp [RingHom.mapMatrix_apply]
  have hMf : IsUnit (M.map f).det := by
    rw [h1, ← RingHom.map_det f M]
    exact hM.map f
  rw [h1, h2]
  symm
  apply Matrix.inv_eq_right_inv
  rw [← RingHom.map_mul, mul_nonsing_inv M hM]
  simp

/-- IsUnit lifts through polynomial C map. -/
private lemma isUnit_det_map_C (P : Matrix n n ℂ) (hP : IsUnit P.det) :
    IsUnit (P.map Polynomial.C).det := by
  have h := RingHom.map_det (Polynomial.C (R := ℂ)) P
  have h2 : P.map Polynomial.C = Polynomial.C.mapMatrix P := by
    ext; simp [RingHom.mapMatrix_apply]
  rw [h2, ← h]
  exact hP.map _

/-- Determinant is invariant under similarity. -/
private lemma det_conj_of_isUnit' {R : Type*} [CommRing R] (M P : Matrix n n R) (hP : IsUnit P.det) :
    (P * M * P⁻¹).det = M.det := by
  rw [det_mul, det_mul]
  rw [mul_comm P.det M.det, mul_assoc]
  have h : P.det * P⁻¹.det = 1 := by
    rw [det_nonsing_inv]
    rw [Ring.mul_inverse_cancel _ hP]
  rw [h, mul_one]

/-- Determinant is invariant under similarity (complex matrices). -/
private lemma det_conj_of_isUnit (M P : Matrix n n ℂ) (hP : IsUnit P.det) :
    (P * M * P⁻¹).det = M.det := det_conj_of_isUnit' M P hP

/-- The characteristic matrix transforms under similarity. -/
private lemma charmatrix_conj_of_isUnit (M P : Matrix n n ℂ) (hP : IsUnit P.det) :
    (P * M * P⁻¹).charmatrix = (P.map Polynomial.C) * M.charmatrix * (P.map Polynomial.C)⁻¹ := by
  rw [charmatrix_eq_scalar_sub_map, charmatrix_eq_scalar_sub_map]
  rw [Matrix.map_mul, Matrix.map_mul]
  rw [map_inv_of_isUnit P Polynomial.C hP]
  have h_scalar_central : (P.map Polynomial.C) * scalar n Polynomial.X * (P.map Polynomial.C)⁻¹ =
      scalar n Polynomial.X := by
    rw [scalar_mul_eq_mul_scalar' (P.map Polynomial.C) Polynomial.X]
    rw [mul_assoc, mul_nonsing_inv (P.map Polynomial.C) (isUnit_det_map_C P hP)]
    rw [mul_one]
  have h_rhs : (P.map Polynomial.C) * (scalar n Polynomial.X - M.map Polynomial.C) *
      (P.map Polynomial.C)⁻¹ =
      (P.map Polynomial.C) * scalar n Polynomial.X * (P.map Polynomial.C)⁻¹ -
      (P.map Polynomial.C) * M.map Polynomial.C * (P.map Polynomial.C)⁻¹ := by
    rw [mul_sub, sub_mul]
  rw [h_rhs, h_scalar_central]

/-- **Characteristic polynomial is invariant under similarity**:
    For any invertible P, charpoly(P * M * P⁻¹) = charpoly(M). -/
theorem charpoly_conj_of_isUnit (M P : Matrix n n ℂ) (hP : IsUnit P.det) :
    (P * M * P⁻¹).charpoly = M.charpoly := by
  unfold charpoly
  rw [charmatrix_conj_of_isUnit M P hP]
  have hPC := isUnit_det_map_C P hP
  exact det_conj_of_isUnit' M.charmatrix (P.map Polynomial.C) hPC

/-- For unitary matrices, star U = U⁻¹. -/
private lemma unitary_star_eq_inv (U : unitaryGroup n ℂ) :
    star (U : Matrix n n ℂ) = (U : Matrix n n ℂ)⁻¹ := by
  have h : (U : Matrix n n ℂ) * star (U : Matrix n n ℂ) = 1 := mem_unitaryGroup_iff.mp U.2
  symm
  exact Matrix.inv_eq_right_inv h

/-- Unitary matrices have unit determinant (|det U| = 1). -/
private lemma unitary_det_isUnit (U : unitaryGroup n ℂ) : IsUnit (U : Matrix n n ℂ).det := by
  have h : (U : Matrix n n ℂ) * star (U : Matrix n n ℂ) = 1 := mem_unitaryGroup_iff.mp U.2
  have hdet : (U : Matrix n n ℂ).det * star ((U : Matrix n n ℂ).det) = 1 := by
    have star_eq : star (U : Matrix n n ℂ) = (U : Matrix n n ℂ)ᴴ := star_eq_conjTranspose _
    calc (U : Matrix n n ℂ).det * star ((U : Matrix n n ℂ).det)
        = (U : Matrix n n ℂ).det * (U : Matrix n n ℂ)ᴴ.det := by rw [det_conjTranspose]
      _ = (U : Matrix n n ℂ).det * (star (U : Matrix n n ℂ)).det := by rw [star_eq]
      _ = ((U : Matrix n n ℂ) * star (U : Matrix n n ℂ)).det := by rw [det_mul]
      _ = (1 : Matrix n n ℂ).det := by rw [h]
      _ = 1 := det_one
  exact IsUnit.of_mul_eq_one _ hdet

/-- Characteristic polynomial is invariant under unitary conjugation. -/
theorem charpoly_unitary_conj (M : Matrix n n ℂ) (U : unitaryGroup n ℂ) :
    ((U : Matrix n n ℂ) * M * star (U : Matrix n n ℂ)).charpoly = M.charpoly := by
  rw [unitary_star_eq_inv U]
  exact charpoly_conj_of_isUnit M (U : Matrix n n ℂ) (unitary_det_isUnit U)

/-! ### Eigenvalues of squared matrices and Hermitian singular values -/

/-- For Hermitian A, Aᴴ * A = A². -/
private lemma hermitian_conjTranspose_mul_self_eq_sq {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    conjTranspose A * A = A ^ 2 := by
  rw [hA.eq, sq]

/-- Eigenvalues of Aᴴ*A equal eigenvalues of A² for Hermitian A (pointwise). -/
private lemma eigenvalues_conjTranspose_mul_self_eq_sq {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    (posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues =
    (hA.pow 2).eigenvalues := by
  have h_eq := hermitian_conjTranspose_mul_self_eq_sq hA
  apply (IsHermitian.eigenvalues_eq_eigenvalues_iff _ _).mpr
  rw [h_eq]

/-- Eigenvalues of A² equal (λᵢ)² as multisets (Hermitian A). -/
private lemma eigenvalues_sq_multiset (A : Matrix n n ℂ) (hA : A.IsHermitian) :
    Multiset.map ((hA.pow 2).eigenvalues ·) Finset.univ.val =
    Multiset.map (fun i => (hA.eigenvalues i) ^ 2) Finset.univ.val := by
  -- Step 1: Get spectral decomposition A = U * diag(λ) * U*
  let U := hA.eigenvectorUnitary
  let eig := hA.eigenvalues

  have h_spectral : A = (U : Matrix n n ℂ) * diagonal (Complex.ofReal ∘ eig) * star (U : Matrix n n ℂ) :=
    hA.spectral_theorem

  -- Step 2: A² = U * diag(λ²) * U*
  have h_sq : A ^ 2 = (U : Matrix n n ℂ) * diagonal (fun j => (Complex.ofReal (eig j)) ^ 2) * star (U : Matrix n n ℂ) := by
    rw [sq, h_spectral]
    have hUU : star (U : Matrix n n ℂ) * (U : Matrix n n ℂ) = 1 := mem_unitaryGroup_iff'.mp U.2
    calc (U : Matrix n n ℂ) * diagonal (Complex.ofReal ∘ eig) * star (U : Matrix n n ℂ) *
        ((U : Matrix n n ℂ) * diagonal (Complex.ofReal ∘ eig) * star (U : Matrix n n ℂ))
        = (U : Matrix n n ℂ) * diagonal (Complex.ofReal ∘ eig) *
          (star (U : Matrix n n ℂ) * (U : Matrix n n ℂ)) *
          diagonal (Complex.ofReal ∘ eig) * star (U : Matrix n n ℂ) := by simp only [Matrix.mul_assoc]
      _ = (U : Matrix n n ℂ) * diagonal (Complex.ofReal ∘ eig) * 1 *
          diagonal (Complex.ofReal ∘ eig) * star (U : Matrix n n ℂ) := by rw [hUU]
      _ = (U : Matrix n n ℂ) * (diagonal (Complex.ofReal ∘ eig) *
          diagonal (Complex.ofReal ∘ eig)) * star (U : Matrix n n ℂ) := by simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = (U : Matrix n n ℂ) * diagonal (fun j => (Complex.ofReal (eig j)) ^ 2) *
          star (U : Matrix n n ℂ) := by
        congr 1; congr 1
        rw [diagonal_mul_diagonal]
        congr 1; ext j; simp only [Function.comp_apply, sq]

  -- Step 3: By unitary conjugation invariance, charpoly(A²) = charpoly(diag(λ²))
  have h_charpoly_eq : (A ^ 2).charpoly = (diagonal (fun j => (Complex.ofReal (eig j)) ^ 2)).charpoly := by
    rw [h_sq]
    exact charpoly_unitary_conj _ U

  -- Step 4: Compute roots of both charpolys
  have h_roots_A_sq : (A ^ 2).charpoly.roots = Multiset.map (Complex.ofReal ∘ (hA.pow 2).eigenvalues) Finset.univ.val :=
    (hA.pow 2).roots_charpoly_eq_eigenvalues

  have h_roots_diag : (diagonal (fun j => (Complex.ofReal (eig j)) ^ 2)).charpoly.roots =
      Finset.univ.val.map (fun j => (Complex.ofReal (eig j)) ^ 2) := by
    rw [charpoly_diagonal]
    have hne : ∏ i : n, (X - C ((Complex.ofReal (eig i)) ^ 2)) ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]
      intro i _
      exact X_sub_C_ne_zero _
    rw [Polynomial.roots_prod _ _ hne]
    simp only [roots_X_sub_C, Multiset.bind_singleton]

  -- Step 5: Since charpolys are equal, roots are equal
  have h_roots_eq : Multiset.map (Complex.ofReal ∘ (hA.pow 2).eigenvalues) Finset.univ.val =
      Finset.univ.val.map (fun j => (Complex.ofReal (eig j)) ^ 2) := by
    rw [← h_roots_A_sq, ← h_roots_diag, h_charpoly_eq]

  -- Step 6: Use that (ofReal r)² = ofReal (r²) to rewrite RHS
  have h_rhs_eq : Finset.univ.val.map (fun j => (Complex.ofReal (eig j)) ^ 2) =
      Finset.univ.val.map (fun j => Complex.ofReal ((eig j) ^ 2)) := by
    congr 1; ext j; simp only [Complex.ofReal_pow]

  rw [h_rhs_eq] at h_roots_eq

  -- Step 7: Use injectivity of ofReal to extract multiset equality
  have key : Multiset.map (Complex.ofReal ∘ (hA.pow 2).eigenvalues) Finset.univ.val =
             Multiset.map (Complex.ofReal ∘ (fun j => (hA.eigenvalues j) ^ 2)) Finset.univ.val := h_roots_eq

  simp only [← Multiset.map_map] at key
  exact Multiset.map_injective Complex.ofReal_injective key

/-- For a Hermitian matrix, the multiset of singular values equals the multiset of absolute
    values of eigenvalues. Note: pointwise equality does NOT hold in general because
    singular values are sorted decreasingly (all positive), while eigenvalues are sorted
    decreasingly by value (can be negative), so the orderings may differ.

    **Proof**: Uses helper lemmas `hermitian_conjTranspose_mul_self_eq_sq`,
    `eigenvalues_conjTranspose_mul_self_eq_sq`, and `eigenvalues_sq_multiset`
    defined above in the charpoly invariance machinery. -/
theorem singularValues_hermitian_multiset (A : Matrix n n ℂ) (hA : A.IsHermitian) :
    Multiset.map (singularValues A) Finset.univ.val =
    Multiset.map (|hA.eigenvalues ·|) Finset.univ.val := by
  -- Step 1: Rewrite singularValues in terms of eigenvalues(A²)
  have h_sv_eq : ∀ i, singularValues A i = Real.sqrt ((hA.pow 2).eigenvalues i) := by
    intro i
    simp only [singularValues]
    rw [eigenvalues_conjTranspose_mul_self_eq_sq hA]

  -- Step 2: Rewrite LHS using h_sv_eq
  have h_lhs : Multiset.map (singularValues A) Finset.univ.val =
      Multiset.map (fun i => Real.sqrt ((hA.pow 2).eigenvalues i)) Finset.univ.val := by
    congr 1; ext i; exact h_sv_eq i

  rw [h_lhs]

  -- Step 3: Use eigenvalues_sq_multiset: eigenvalues(A²) as multiset = λ² as multiset
  have h_eig_sq := eigenvalues_sq_multiset A hA

  -- Step 4: Reformulate using Multiset.map_map
  have h1 : Multiset.map (fun i => Real.sqrt ((hA.pow 2).eigenvalues i)) Finset.univ.val =
      Multiset.map Real.sqrt (Multiset.map (fun i => (hA.pow 2).eigenvalues i) Finset.univ.val) := by
    rw [Multiset.map_map]; rfl

  have h2 : Multiset.map (fun i => Real.sqrt ((hA.eigenvalues i) ^ 2)) Finset.univ.val =
      Multiset.map Real.sqrt (Multiset.map (fun i => (hA.eigenvalues i) ^ 2) Finset.univ.val) := by
    rw [Multiset.map_map]; rfl

  rw [h1, h_eig_sq, ← h2]

  -- Step 5: Apply Real.sqrt_sq_eq_abs: √(λ²) = |λ|
  congr 1; ext i
  exact Real.sqrt_sq_eq_abs _

/-! ### Eigenvalues of diagonal matrices -/

/-- For a diagonal matrix with real entries sorted decreasingly, eigenvalues equal the entries.

    The key insight is that `eigenvalues` is defined via sorting the roots of charpoly,
    and for a diagonal matrix `diagonal(d)`, the roots are exactly `{d_i | i}`.
    If `d` is already sorted decreasingly (via `eigenvalues₀_antitone`), then
    sorting is the identity, so `eigenvalues = d` pointwise.

    The formal proof uses:
    1. `charpoly_diagonal`: charpoly(diagonal(d)) = ∏(X - d_i)
    2. `sort_roots_charpoly_eq_eigenvalues₀`: sorted roots = eigenvalues₀
    3. `Antitone.ofFn_sorted`: antitone function gives sorted list
    4. `List.eq_of_perm_of_sorted`: two sorted lists with same elements are equal -/
private lemma eigenvalues_diagonal_of_sorted (f : Fin (Fintype.card n) → ℝ) (h_antitone : Antitone f) :
    let equiv := (Fintype.equivOfCardEq (Fintype.card_fin _) : Fin (Fintype.card n) ≃ n)
    let D := diagonal (Complex.ofReal ∘ f ∘ equiv.symm)
    ∀ (hD : D.IsHermitian), hD.eigenvalues₀ = f := by
  intro equiv D hD
  -- Strategy: Use that eigenvalues₀ = sorted roots of charpoly, and for diagonal matrices
  -- with antitone entries, sorting is the identity.
  --
  -- Key chain of equalities:
  -- 1. D.charpoly = ∏ i, (X - C (ofReal (f (equiv.symm i))))  [charpoly_diagonal]
  -- 2. D.charpoly.roots = multiset of {ofReal (f (equiv.symm i)) | i}
  -- 3. After mapping re and sorting by ≥: List.ofFn f
  -- 4. But sorted roots = List.ofFn eigenvalues₀  [sort_roots_charpoly_eq_eigenvalues₀]
  -- 5. By List.ofFn_inj: eigenvalues₀ = f

  -- Use sort_roots_charpoly_eq_eigenvalues₀ from Mathlib
  have h_sort_eq := hD.sort_roots_charpoly_eq_eigenvalues₀

  -- The charpoly of diagonal is product of (X - entries)
  have h_charpoly := charpoly_diagonal (Complex.ofReal ∘ f ∘ equiv.symm)

  -- Compute roots of the diagonal charpoly
  have h_roots : D.charpoly.roots = Finset.univ.val.map (fun i => Complex.ofReal (f (equiv.symm i))) := by
    rw [h_charpoly, Polynomial.roots_prod]
    simp only [Polynomial.roots_X_sub_C, Multiset.bind_singleton, Function.comp_apply]
    rw [Finset.prod_ne_zero_iff]
    exact fun i _ => Polynomial.X_sub_C_ne_zero _

  -- Map re over the roots gives values in the range of f ∘ equiv.symm
  have h_roots_re : D.charpoly.roots.map Complex.re = (Finset.univ : Finset n).val.map (f ∘ equiv.symm) := by
    rw [h_roots]
    simp only [Multiset.map_map, Function.comp_apply, Complex.ofReal_re]

  -- Convert to Fin indexing using the equivalence
  have h_multiset_eq : (Finset.univ : Finset n).val.map (f ∘ equiv.symm) = (Finset.univ : Finset (Fin (Fintype.card n))).val.map f := by
    rw [← Multiset.map_map]
    congr 1
    ext x
    simp

  -- The entries are antitone, so List.ofFn f is sorted by ≥
  have h_f_sorted : (List.ofFn f).Sorted (· ≥ ·) := h_antitone.ofFn_sorted

  -- Sort of an already-sorted list is itself
  have h_sort_id : (D.charpoly.roots.map Complex.re).sort (· ≥ ·) = List.ofFn f := by
    rw [h_roots_re, h_multiset_eq]
    -- Finset.univ.val.map f = List.ofFn f as a Multiset
    have h_eq : ((Finset.univ : Finset (Fin (Fintype.card n))).val.map f : Multiset ℝ) = ↑(List.ofFn f) := by
      simp only [Fin.univ_val_map]
    rw [h_eq, Multiset.coe_sort]
    -- Sorting a sorted list returns itself
    have h_pw : List.Pairwise (fun a b => decide (a ≥ b) = true) (List.ofFn f) := by
      simp only [decide_eq_true_iff]
      exact h_f_sorted
    exact (List.ofFn f).mergeSort_of_pairwise h_pw

  -- Combine with sort_roots_charpoly_eq_eigenvalues₀
  have h_eq_lists : List.ofFn hD.eigenvalues₀ = List.ofFn f := by
    simp only [RCLike.re_eq_complex_re] at h_sort_eq
    rw [← h_sort_eq, h_sort_id]

  -- Extract function equality from list equality
  exact List.ofFn_injective h_eq_lists

lemma eigenvalues_sq {A : Matrix n n ℂ} (hA : A.PosSemidef) (i : n) :
    (hA.isHermitian.pow 2).eigenvalues i = (hA.isHermitian.eigenvalues i) ^ 2 := by
  /-
  Proof for PSD matrices using spectral theorem:
  1. A = U * diag(λ) * U* where U = eigenvectorUnitary, λ = eigenvalues
  2. A² = U * diag(λ²) * U*
  3. By charpoly_unitary_conj: charpoly(A²) = charpoly(diag(λ²))
  4. charpoly(diag(λ²)) = ∏ i, (X - C(λᵢ²))
  5. For PSD: λᵢ ≥ 0, sorted decreasingly, so λᵢ² are also sorted decreasingly
  6. By eigenvalues_eq_of_charpoly_eq: eigenvalues match pointwise
  -/
  -- Get the eigenvector unitary from spectral theorem
  let U := hA.isHermitian.eigenvectorUnitary
  let eig := hA.isHermitian.eigenvalues

  -- Step 1: Express A using spectral theorem
  have h_spectral : A = (U : Matrix n n ℂ) *
      diagonal (Complex.ofReal ∘ eig) * star (U : Matrix n n ℂ) := by
    have := hA.isHermitian.spectral_theorem
    simp only [Unitary.conjStarAlgAut_apply] at this
    exact this

  -- Step 2: A² = U * D² * U*
  have h_sq : A ^ 2 = (U : Matrix n n ℂ) *
      diagonal (fun j => (Complex.ofReal (eig j)) ^ 2) * star (U : Matrix n n ℂ) := by
    rw [pow_two, h_spectral]
    -- (U * D * U*) * (U * D * U*) = U * D * (U* * U) * D * U* = U * D * D * U* = U * D² * U*
    have hUU : star (U : Matrix n n ℂ) * (U : Matrix n n ℂ) = 1 :=
      mem_unitaryGroup_iff'.mp U.2
    calc (U : Matrix n n ℂ) * diagonal (Complex.ofReal ∘ eig) * star (U : Matrix n n ℂ) *
        ((U : Matrix n n ℂ) * diagonal (Complex.ofReal ∘ eig) * star (U : Matrix n n ℂ))
        = (U : Matrix n n ℂ) * diagonal (Complex.ofReal ∘ eig) *
          (star (U : Matrix n n ℂ) * (U : Matrix n n ℂ)) *
          diagonal (Complex.ofReal ∘ eig) * star (U : Matrix n n ℂ) := by
            simp only [Matrix.mul_assoc]
      _ = (U : Matrix n n ℂ) * diagonal (Complex.ofReal ∘ eig) * 1 *
          diagonal (Complex.ofReal ∘ eig) * star (U : Matrix n n ℂ) := by rw [hUU]
      _ = (U : Matrix n n ℂ) * (diagonal (Complex.ofReal ∘ eig) *
          diagonal (Complex.ofReal ∘ eig)) * star (U : Matrix n n ℂ) := by
            simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = (U : Matrix n n ℂ) * diagonal (fun j => (Complex.ofReal (eig j)) ^ 2) *
          star (U : Matrix n n ℂ) := by
        congr 1; congr 1
        rw [diagonal_mul_diagonal]
        congr 1
        ext j
        simp only [Function.comp_apply, sq]

  -- Step 3: charpoly(A²) = charpoly(D²) by unitary conjugation invariance
  have h_charpoly_eq : (A ^ 2).charpoly =
      (diagonal (fun j => (Complex.ofReal (eig j)) ^ 2)).charpoly := by
    rw [h_sq]
    exact charpoly_unitary_conj _ U

  -- Step 4: charpoly of diagonal = product of (X - entries)
  have h_charpoly_diag : (diagonal (fun j => (Complex.ofReal (eig j)) ^ 2)).charpoly =
      ∏ j, (Polynomial.X - Polynomial.C ((Complex.ofReal (eig j)) ^ 2)) := by
    exact charpoly_diagonal _

  -- Step 5: Relate to real diagonal for eigenvalues
  -- The eigenvalues of D² (as a Hermitian matrix) are eig²
  -- Need to show (A²).eigenvalues i = eigᵢ² using charpoly equality

  -- For PSD matrices, eigenvalues are non-negative and sorted decreasingly
  have h_nonneg : ∀ j, 0 ≤ eig j := fun j => PosSemidef.eigenvalues_nonneg hA j

  -- The diagonal matrix with entries eig² is Hermitian
  let D_sq := diagonal (fun j => (Complex.ofReal (eig j)) ^ 2)
  have h_D_herm : D_sq.IsHermitian := by
    rw [IsHermitian, diagonal_conjTranspose]
    congr 1
    ext j
    show star ((↑(hA.isHermitian.eigenvalues j) : ℂ) ^ 2) = (↑(hA.isHermitian.eigenvalues j)) ^ 2
    rw [star_pow]
    congr 1
    exact Complex.conj_ofReal _

  -- By eigenvalues_eq_eigenvalues_iff: matrices with same charpoly have same eigenvalues
  have h_eigenvalues_eq : (hA.isHermitian.pow 2).eigenvalues = h_D_herm.eigenvalues := by
    rw [IsHermitian.eigenvalues_eq_eigenvalues_iff]
    exact h_charpoly_eq

  -- Now we need: h_D_herm.eigenvalues i = (eig i)²
  -- Use eigenvalues_diagonal_of_sorted: for diagonal with sorted entries, eigenvalues₀ = entries
  have h_D_eigenvalues : h_D_herm.eigenvalues i = (eig i) ^ 2 := by
    -- eig₀ = eigenvalues₀ is antitone
    let eig₀ := hA.isHermitian.eigenvalues₀
    have h_eig₀_antitone := hA.isHermitian.eigenvalues₀_antitone

    -- eig₀² is also antitone (since eig₀ ≥ 0 from PSD)
    have h_eig₀_nonneg : ∀ j, 0 ≤ eig₀ j := by
      intro j
      have := hA.eigenvalues_nonneg ((Fintype.equivOfCardEq (Fintype.card_fin _)) j)
      simp only [IsHermitian.eigenvalues] at this
      simp at this
      exact this
    have h_eig₀_sq_antitone : Antitone (fun j => (eig₀ j) ^ 2) := by
      intro x y hxy
      rw [sq_le_sq, abs_of_nonneg (h_eig₀_nonneg y), abs_of_nonneg (h_eig₀_nonneg x)]
      exact h_eig₀_antitone hxy

    -- The diagonal matrix D_sq = diagonal(ofReal ∘ eig²) matches diagonal(ofReal ∘ eig₀² ∘ equiv.symm)
    -- where eig i = eig₀ (equiv.symm i), so (eig i)² = (eig₀ (equiv.symm i))²

    -- By eigenvalues_diagonal_of_sorted: eigenvalues₀ of D_sq = eig₀²
    -- And eigenvalues i = eigenvalues₀ (equiv.symm i) = (eig₀ (equiv.symm i))² = (eig i)²

    -- The key step uses that D_sq matches the structure expected by eigenvalues_diagonal_of_sorted
    -- D_sq = diagonal (fun j => (ofReal (eig j))²)
    --      = diagonal (fun j => ofReal ((eig j)²))  -- since (ofReal x)² = ofReal (x²)
    --      = diagonal (ofReal ∘ (fun j => (eig j)²))
    --      = diagonal (ofReal ∘ (fun j => (eig₀ (equiv.symm j))²))
    --      = diagonal (ofReal ∘ (fun j => (eig₀)² (equiv.symm j)))
    --      = diagonal (ofReal ∘ (eig₀)² ∘ equiv.symm)

    -- This matches eigenvalues_diagonal_of_sorted with f = (eig₀)²
    -- So h_D_herm.eigenvalues₀ = (eig₀)²
    -- And h_D_herm.eigenvalues i = h_D_herm.eigenvalues₀ (equiv.symm i) = (eig₀ (equiv.symm i))² = (eig i)²

    have h_D_eq : D_sq = diagonal (Complex.ofReal ∘ (fun j => (eig₀ j)^2) ∘
        (Fintype.equivOfCardEq (Fintype.card_fin _)).symm) := by
      simp only [D_sq, eig, eig₀]
      congr 1
      ext j
      simp only [Function.comp_apply, IsHermitian.eigenvalues]
      norm_cast

    have h_eigval₀ := eigenvalues_diagonal_of_sorted (fun j => (eig₀ j)^2) h_eig₀_sq_antitone
    specialize h_eigval₀ (h_D_eq ▸ h_D_herm)
    -- h_eigval₀ : (h_D_eq ▸ h_D_herm).eigenvalues₀ = fun j => (eig₀ j)²

    simp only [IsHermitian.eigenvalues]
    -- Goal: eigenvalues₀ (equiv.symm i) = (eig₀ (equiv.symm i))²
    -- Use h_eigval₀ after handling the dependent type rewrite

    -- Key insight: h_D_eq is essentially a definitional equality after unfolding let bindings
    -- The eigenvalues₀ only depends on the matrix, and the matrices are definitionally equal
    have key : h_D_herm.eigenvalues₀ = fun j => (eig₀ j)^2 := by
      convert h_eigval₀ using 2
    rw [key]
    -- Goal: (fun j => eig₀ j ^ 2) (equiv.symm i) = eig i ^ 2
    -- Since eig i = eig₀ (equiv.symm i), this is eig₀ (equiv.symm i) ^ 2 = eig₀ (equiv.symm i) ^ 2
    simp only [eig, eig₀, IsHermitian.eigenvalues]

  rw [h_eigenvalues_eq, h_D_eigenvalues]

/-- For a positive semidefinite matrix, singular values equal eigenvalues. -/
theorem singularValues_posSemidef (A : Matrix n n ℂ) (hA : A.PosSemidef) (i : n) :
    singularValues A i = hA.isHermitian.eigenvalues i := by
  dsimp [singularValues]
  have h_sq : conjTranspose A * A = A^2 := by
    rw [hA.isHermitian.eq, pow_two]
  have h_charpoly : (conjTranspose A * A).charpoly = (A^2).charpoly := by
    rw [h_sq]
  have h_eq : (posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues i = (hA.isHermitian.pow 2).eigenvalues i := by
    apply congr_fun
    exact (IsHermitian.eigenvalues_eq_eigenvalues_iff _ _).mpr h_charpoly
  rw [h_eq]
  rw [eigenvalues_sq hA]
  rw [Real.sqrt_sq]
  exact PosSemidef.eigenvalues_nonneg hA i

/-- The eigenvalues of √(Aᴴ*A) are the singular values of A.
    This follows from the spectral theorem: if Aᴴ*A has eigenvalues λᵢ ≥ 0,
    then √(Aᴴ*A) has eigenvalues √λᵢ, which are exactly the singular values.

    **Proof strategy:**
    1. Let B = √(Aᴴ*A), which is PosSemidef
    2. B² = Aᴴ*A (by CFC.sq_sqrt)
    3. eigenvalues(B²) = eigenvalues(Aᴴ*A) (same matrix, same eigenvalues)
    4. For PSD B: eigenvalues(B²) i = (eigenvalues(B) i)² (by eigenvalues_sq)
    5. Therefore: (eigenvalues(B) i)² = eigenvalues(Aᴴ*A) i
    6. Taking sqrt: eigenvalues(B) i = √(eigenvalues(Aᴴ*A) i) = singularValues A i
       (using eigenvalues(B) i ≥ 0 for PSD B)
-/
theorem sqrtConjTransposeMulSelf_eigenvalues (A : Matrix n n ℂ) (i : n) :
    (sqrtConjTransposeMulSelf_isHermitian A).eigenvalues i = singularValues A i := by
  -- Let B = sqrt(Aᴴ*A) and let hB be the proof that B is PosSemidef
  let B := sqrtConjTransposeMulSelf A
  let hB := sqrtConjTransposeMulSelf_isPosSemidef A

  -- B² = Aᴴ*A
  have h_sq : B ^ 2 = Aᴴ * A := sqrtConjTransposeMulSelf_sq A

  -- eigenvalues(B²) = eigenvalues(Aᴴ*A) because they're the same matrix
  have h_eig_sq : (hB.isHermitian.pow 2).eigenvalues =
                  (posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues := by
    rw [IsHermitian.eigenvalues_eq_eigenvalues_iff]
    rw [h_sq]

  -- For PSD B: eigenvalues(B²) i = (eigenvalues(B) i)²
  have h_sq_eig : (hB.isHermitian.pow 2).eigenvalues i = (hB.isHermitian.eigenvalues i) ^ 2 :=
    eigenvalues_sq hB i

  -- eigenvalues(Aᴴ*A) i = (eigenvalues(B) i)²
  have h_eq : (posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues i =
              (hB.isHermitian.eigenvalues i) ^ 2 := by
    rw [← h_eig_sq, h_sq_eig]

  -- singularValues A i = sqrt((eigenvalues(B) i)²) = eigenvalues(B) i
  -- (since B is PSD, eigenvalues are non-negative)
  unfold singularValues
  rw [h_eq]
  rw [Real.sqrt_sq]
  exact PosSemidef.eigenvalues_nonneg hB i

/-! ### Product and Sum Properties -/

/-- Product of square roots equals square root of product for nonnegative functions. -/
private lemma prod_sqrt_eq_sqrt_prod {ι : Type*} [Fintype ι] (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) :
    ∏ i, Real.sqrt (f i) = Real.sqrt (∏ i, f i) := by
  have h_prod_nonneg : 0 ≤ ∏ i, f i := Finset.prod_nonneg fun i _ => hf i
  have h_prod_sqrt_nonneg : 0 ≤ ∏ i, Real.sqrt (f i) :=
    Finset.prod_nonneg fun i _ => Real.sqrt_nonneg _
  symm
  rw [Real.sqrt_eq_iff_eq_sq h_prod_nonneg h_prod_sqrt_nonneg]
  rw [← Finset.prod_pow]
  congr 1
  ext i
  rw [Real.sq_sqrt (hf i)]

/-- The determinant of Aᴴ * A equals the squared norm of det A. -/
private lemma det_conjTranspose_mul_self (A : Matrix n n ℂ) :
    (Aᴴ * A).det = Complex.normSq A.det := by
  rw [det_mul, det_conjTranspose]
  rw [Complex.normSq_eq_conj_mul_self]
  rfl

/-- The product of singular values equals the absolute value of the determinant. -/
theorem prod_singularValues_eq_abs_det (A : Matrix n n ℂ) :
    ∏ i, singularValues A i = Real.sqrt (Complex.normSq (A.det)) := by
  unfold singularValues
  rw [prod_sqrt_eq_sqrt_prod _ (fun i =>
    PosSemidef.eigenvalues_nonneg (posSemidef_conjTranspose_mul_self A) i)]
  congr 1
  -- Goal: ∏ eigenvalues (Aᴴ*A) = Complex.normSq (det A) at ℝ level
  have h1 := (posSemidef_conjTranspose_mul_self A).isHermitian.det_eq_prod_eigenvalues
  have h2 : (Aᴴ * A).det = Complex.normSq A.det := det_conjTranspose_mul_self A
  -- h1 : det(Aᴴ*A) = ∏ i, ↑(eigenvalues i) as complex numbers
  -- h2 : det(Aᴴ*A) = normSq(det A) as complex numbers
  have h3 : ∏ i, ((posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues i : ℂ) =
            (Complex.normSq A.det : ℂ) := by
    calc ∏ i, ((posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues i : ℂ)
        = (Aᴴ * A).det := h1.symm
      _ = Complex.normSq A.det := h2
  -- Convert from complex product to real product using Complex.ofReal_prod
  have h4 : (↑(∏ i, (posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues i) : ℂ) =
            ∏ i, ((posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues i : ℂ) :=
    Complex.ofReal_prod _ _
  have h5 : (↑(∏ i, (posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues i) : ℂ) =
            (Complex.normSq A.det : ℂ) := h4.trans h3
  exact Complex.ofReal_injective h5

/-- The sum of squared singular values equals the squared Frobenius norm.
    (i.e., trace(Aᴴ * A)) -/
theorem sum_sq_singularValues_eq_trace (A : Matrix n n ℂ) :
    ∑ i, (singularValues A i) ^ 2 = Complex.re (Matrix.trace (conjTranspose A * A)) := by
  -- Singular values squared = eigenvalues of Aᴴ * A
  simp_rw [singularValues_sq]
  -- trace(Aᴴ * A) = sum of eigenvalues (spectral theorem)
  have h := (posSemidef_conjTranspose_mul_self A).isHermitian.trace_eq_sum_eigenvalues
  -- The RHS simplifies to Re(∑ (λᵢ : ℂ)) = ∑ Re(λᵢ) = ∑ λᵢ (since λᵢ are real)
  rw [h, Complex.re_sum]
  rfl

/-! ### Truncated SVD

For Eckart-Young theorem and low-rank approximation, we define the rank-k truncated SVD
which keeps only the k largest singular values. -/

section TruncatedSVD

/-- Truncated singular values: keep first k (largest) singular values, zero the rest.
    Uses the sorted `singularValues₀` indexing. -/
noncomputable def truncatedSingularValues (A : Matrix n n ℂ) (k : ℕ) : n → ℝ :=
  fun i =>
    let idx := (Fintype.equivOfCardEq (Fintype.card_fin _)).symm i
    if idx.val < k then singularValues₀ A idx else 0

/-- Truncated singular values are non-negative. -/
theorem truncatedSingularValues_nonneg (A : Matrix n n ℂ) (k : ℕ) (i : n) :
    0 ≤ truncatedSingularValues A k i := by
  unfold truncatedSingularValues
  simp only
  split_ifs with h
  · exact singularValues₀_nonneg A _
  · rfl

/-- Truncated singular values equal regular singular values for indices < k. -/
theorem truncatedSingularValues_eq_of_lt (A : Matrix n n ℂ) (k : ℕ) (i : n)
    (h : ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm i : Fin (Fintype.card n)).val < k) :
    truncatedSingularValues A k i = singularValues₀ A ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm i) := by
  unfold truncatedSingularValues
  simp only [h, ↓reduceIte]

/-- Truncated singular values are zero for indices ≥ k. -/
theorem truncatedSingularValues_eq_zero_of_ge (A : Matrix n n ℂ) (k : ℕ) (i : n)
    (h : k ≤ ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm i : Fin (Fintype.card n)).val) :
    truncatedSingularValues A k i = 0 := by
  unfold truncatedSingularValues
  simp only [not_lt.mpr h, ↓reduceIte]

/-- The number of nonzero truncated singular values is at most k.
    This uses that truncated values are nonzero only for indices < k,
    and there are at most k such indices. -/
theorem card_truncatedSingularValues_nonzero_le (A : Matrix n n ℂ) (k : ℕ) :
    Fintype.card { i : n // truncatedSingularValues A k i ≠ 0 } ≤ k := by
  -- Nonzero entries can only occur when idx.val < k
  have h_subset : ∀ i : n, truncatedSingularValues A k i ≠ 0 →
      ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm i : Fin (Fintype.card n)).val < k := by
    intro i hi
    by_contra h_not_lt
    push_neg at h_not_lt
    have := truncatedSingularValues_eq_zero_of_ge A k i h_not_lt
    exact hi this
  -- The set { i : n | truncated ≠ 0 } maps injectively into Fin k
  -- via i ↦ (equiv.symm i).val when that value < k
  let e := (Fintype.equivOfCardEq (Fintype.card_fin _) : Fin (Fintype.card n) ≃ n).symm
  have h_inj : Function.Injective (fun (x : { i : n // truncatedSingularValues A k i ≠ 0 }) =>
      (⟨(e x.val).val, h_subset x.val x.prop⟩ : Fin k)) := by
    intro ⟨x, hx⟩ ⟨y, hy⟩ h_eq
    simp only [Fin.mk.injEq] at h_eq
    have h_fin_eq : e x = e y := Fin.ext h_eq
    exact Subtype.ext (e.injective h_fin_eq)
  calc Fintype.card { i : n // truncatedSingularValues A k i ≠ 0 }
      ≤ Fintype.card (Fin k) := Fintype.card_le_of_injective _ h_inj
    _ = k := Fintype.card_fin k

/-- The truncated SVD of rank k: Aₖ = U * Σₖ * Vᴴ where Σₖ keeps only the k largest singular values.
    This is the best rank-k approximation in both Frobenius and spectral norms (Eckart-Young). -/
noncomputable def truncatedSVD (A : Matrix n n ℂ) (k : ℕ) : Matrix n n ℂ :=
  (constructedU A : Matrix n n ℂ) *
    diagonal (Complex.ofReal ∘ truncatedSingularValues A k) *
    star (rightUnitary A : Matrix n n ℂ)

/-- The truncated SVD with k = 0 is the zero matrix. -/
theorem truncatedSVD_zero (A : Matrix n n ℂ) : truncatedSVD A 0 = 0 := by
  unfold truncatedSVD truncatedSingularValues
  simp only [Nat.not_lt_zero, ↓reduceIte]
  have h_diag : diagonal (Complex.ofReal ∘ fun _ : n => (0 : ℝ)) = (0 : Matrix n n ℂ) := by
    ext i j
    simp only [diagonal_apply, Function.comp_apply, Complex.ofReal_zero]
    split_ifs <;> rfl
  rw [h_diag, mul_zero, zero_mul]

/-- The truncated SVD with k ≥ card n equals the original SVD (hence equals A). -/
theorem truncatedSVD_full (A : Matrix n n ℂ) (k : ℕ) (hk : Fintype.card n ≤ k) :
    truncatedSVD A k = A := by
  unfold truncatedSVD truncatedSingularValues
  -- All indices satisfy idx.val < k since idx.val < card n ≤ k
  have h_all : ∀ i : n, ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm i : Fin (Fintype.card n)).val < k := by
    intro i
    calc ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm i).val
        < Fintype.card n := Fin.isLt _
      _ ≤ k := hk
  -- Simplify the diagonal to use singularValues
  have h_diag_eq : diagonal (Complex.ofReal ∘ fun i =>
      if ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm i : Fin (Fintype.card n)).val < k
      then singularValues₀ A ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm i)
      else 0) =
      diagonal (Complex.ofReal ∘ singularValues A) := by
    ext i j
    simp only [diagonal_apply, Function.comp_apply]
    split_ifs with h_eq h_lt
    · -- case h_eq : i = j, h_lt : idx < k
      subst h_eq
      rw [singularValues_eq_singularValues₀]
    · -- case h_eq : i = j, h_lt : ¬(idx < k) - impossible
      subst h_eq
      exact absurd (h_all i) h_lt
    · rfl  -- case ¬(i = j) - both sides are 0
  rw [h_diag_eq]
  -- This is exactly the SVD decomposition
  have h_svd := AV_eq_constructedU_mul_sigma A
  have h_V_unitary : (rightUnitary A : Matrix n n ℂ) * star (rightUnitary A : Matrix n n ℂ) = 1 :=
    mem_unitaryGroup_iff.mp (rightUnitary A).2
  calc (constructedU A : Matrix n n ℂ) * diagonal (Complex.ofReal ∘ singularValues A) * star (rightUnitary A : Matrix n n ℂ)
      = ((constructedU A : Matrix n n ℂ) * diagonal (Complex.ofReal ∘ singularValues A)) * star (rightUnitary A : Matrix n n ℂ) := by rw [mul_assoc]
    _ = (A * (rightUnitary A : Matrix n n ℂ)) * star (rightUnitary A : Matrix n n ℂ) := by rw [← h_svd]
    _ = A * ((rightUnitary A : Matrix n n ℂ) * star (rightUnitary A : Matrix n n ℂ)) := by rw [mul_assoc]
    _ = A * 1 := by rw [h_V_unitary]
    _ = A := by rw [mul_one]

/-- The rank of the truncated SVD is at most k.
    This uses that rank(diagonal w) = #{i | w i ≠ 0} and unitary transformations preserve rank. -/
theorem truncatedSVD_rank_le (A : Matrix n n ℂ) (k : ℕ) :
    (truncatedSVD A k).rank ≤ k := by
  unfold truncatedSVD
  -- Let D = diagonal(truncatedSingularValues)
  let D := diagonal (Complex.ofReal ∘ truncatedSingularValues A k)
  let U := (constructedU A : Matrix n n ℂ)
  let V := (rightUnitary A : Matrix n n ℂ)
  -- truncatedSVD A k = U * D * Vᴴ
  -- rank(U * D * Vᴴ) = rank(D) since U, Vᴴ are unitary (invertible)
  have hU_isUnit : IsUnit U.det := UnitaryGroup.det_isUnit (constructedU A)
  have hVstar_isUnit : IsUnit (star V).det := by
    have hV_isUnit : IsUnit V.det := UnitaryGroup.det_isUnit (rightUnitary A)
    rw [star_eq_conjTranspose, det_conjTranspose]
    exact hV_isUnit.star
  -- rank(U * D * Vᴴ) = rank(D * Vᴴ) = rank(D)
  have h1 : (U * D * star V).rank = (D * star V).rank := by
    rw [mul_assoc]
    exact rank_mul_eq_right_of_isUnit_det U (D * star V) hU_isUnit
  have h2 : (D * star V).rank = D.rank := rank_mul_eq_left_of_isUnit_det (star V) D hVstar_isUnit
  -- rank(D) = #{i | D i i ≠ 0} = #{i | truncatedSingularValues A k i ≠ 0} ≤ k
  have h3 : D.rank = Fintype.card { i : n // (Complex.ofReal ∘ truncatedSingularValues A k) i ≠ 0 } := by
    exact rank_diagonal _
  have h4 : Fintype.card { i : n // (Complex.ofReal ∘ truncatedSingularValues A k) i ≠ 0 } =
            Fintype.card { i : n // truncatedSingularValues A k i ≠ 0 } := by
    have h_equiv : { i : n // (Complex.ofReal ∘ truncatedSingularValues A k) i ≠ 0 } ≃
                   { i : n // truncatedSingularValues A k i ≠ 0 } := by
      apply Equiv.subtypeEquivProp
      ext i
      simp only [Function.comp_apply, ne_eq, Complex.ofReal_eq_zero]
    exact Fintype.card_eq.mpr ⟨h_equiv⟩
  rw [h1, h2, h3, h4]
  exact card_truncatedSingularValues_nonzero_le A k

/-- The tail of the SVD: singular values beyond the k-th. -/
noncomputable def truncatedSingularValues_tail (A : Matrix n n ℂ) (k : ℕ) : n → ℝ :=
  fun i =>
    let idx := (Fintype.equivOfCardEq (Fintype.card_fin _)).symm i
    if k ≤ idx.val then singularValues₀ A idx else 0

/-- The truncated and tail singular values sum to the original. -/
theorem truncatedSingularValues_add_tail (A : Matrix n n ℂ) (k : ℕ) (i : n) :
    truncatedSingularValues A k i + truncatedSingularValues_tail A k i = singularValues A i := by
  unfold truncatedSingularValues truncatedSingularValues_tail
  simp only [singularValues_eq_singularValues₀]
  split_ifs with h1 h2
  · -- h1 : idx < k, h2 : k ≤ idx - impossible
    omega
  · -- h1 : idx < k, h2 : ¬(k ≤ idx)
    ring
  · -- h1 : ¬(idx < k), h2 : k ≤ idx
    ring
  · -- h1 : ¬(idx < k), h2 : ¬(k ≤ idx) - impossible
    omega

/-- The tail of the truncated SVD. -/
noncomputable def truncatedSVD_tail (A : Matrix n n ℂ) (k : ℕ) : Matrix n n ℂ :=
  (constructedU A : Matrix n n ℂ) *
    diagonal (Complex.ofReal ∘ truncatedSingularValues_tail A k) *
    star (rightUnitary A : Matrix n n ℂ)

/-- The original matrix equals the truncated SVD plus its tail: A = Aₖ + A_tail. -/
theorem truncatedSVD_add_tail (A : Matrix n n ℂ) (k : ℕ) :
    A = truncatedSVD A k + truncatedSVD_tail A k := by
  unfold truncatedSVD truncatedSVD_tail
  -- diag(trunc) + diag(tail) = diag(trunc + tail) = diag(singularValues)
  have h_diag : diagonal (Complex.ofReal ∘ truncatedSingularValues A k) +
                diagonal (Complex.ofReal ∘ truncatedSingularValues_tail A k) =
                diagonal (Complex.ofReal ∘ singularValues A) := by
    ext i j
    simp only [add_apply, diagonal_apply, Function.comp_apply]
    split_ifs with h
    · subst h
      rw [← Complex.ofReal_add, truncatedSingularValues_add_tail]
    · ring
  -- U * D₁ * Vᴴ + U * D₂ * Vᴴ = U * (D₁ + D₂) * Vᴴ
  have h_factor : (constructedU A : Matrix n n ℂ) * diagonal (Complex.ofReal ∘ truncatedSingularValues A k) *
                  star (rightUnitary A : Matrix n n ℂ) +
                  (constructedU A : Matrix n n ℂ) * diagonal (Complex.ofReal ∘ truncatedSingularValues_tail A k) *
                  star (rightUnitary A : Matrix n n ℂ) =
                  (constructedU A : Matrix n n ℂ) * diagonal (Complex.ofReal ∘ singularValues A) *
                  star (rightUnitary A : Matrix n n ℂ) := by
    -- Use (A * B) * C + (A * D) * C = (A * (B + D)) * C
    rw [← add_mul, ← mul_add, h_diag]
  rw [h_factor]
  -- Now we have A = U * diag(singularValues) * Vᴴ by SVD
  have h_svd := AV_eq_constructedU_mul_sigma A
  have h_V_unitary : (rightUnitary A : Matrix n n ℂ) * star (rightUnitary A : Matrix n n ℂ) = 1 :=
    mem_unitaryGroup_iff.mp (rightUnitary A).2
  symm
  calc (constructedU A : Matrix n n ℂ) * diagonal (Complex.ofReal ∘ singularValues A) * star (rightUnitary A : Matrix n n ℂ)
      = ((constructedU A : Matrix n n ℂ) * diagonal (Complex.ofReal ∘ singularValues A)) * star (rightUnitary A : Matrix n n ℂ) := by rw [mul_assoc]
    _ = (A * (rightUnitary A : Matrix n n ℂ)) * star (rightUnitary A : Matrix n n ℂ) := by rw [← h_svd]
    _ = A * ((rightUnitary A : Matrix n n ℂ) * star (rightUnitary A : Matrix n n ℂ)) := by rw [mul_assoc]
    _ = A * 1 := by rw [h_V_unitary]
    _ = A := by rw [mul_one]

end TruncatedSVD

end Matrix.SVD

/-! ## Real Matrix SVD -/

namespace Matrix.SVD.Real

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The singular values of a real matrix A are the square roots of the eigenvalues of Aᵀ * A. -/
noncomputable def singularValues (A : Matrix n n ℝ) : n → ℝ :=
  Matrix.SVD.singularValues (A.map Complex.ofReal)

omit [Fintype n] [DecidableEq n] in
/-- A real matrix mapped to ℂ has Hermitian = Symmetric (transpose equals conjTranspose). -/
lemma real_matrix_conjTranspose_eq_transpose (A : Matrix n n ℝ) :
    (A.map Complex.ofReal)ᴴ = (Aᵀ).map Complex.ofReal := by
  ext i j
  simp only [conjTranspose_apply, map_apply, transpose_apply]
  exact Complex.conj_ofReal (A j i)

omit [DecidableEq n] in
/-- For real A, Aᴴ * A = Aᵀ * A (as complex matrices). -/
lemma real_conjTranspose_mul_self (A : Matrix n n ℝ) :
    (A.map Complex.ofReal)ᴴ * (A.map Complex.ofReal) = (Aᵀ * A).map Complex.ofReal := by
  rw [real_matrix_conjTranspose_eq_transpose]
  ext i j
  simp only [mul_apply, map_apply, transpose_apply]
  conv_lhs =>
    arg 2
    ext k
    rw [← Complex.ofReal_mul]
  rw [← Complex.ofReal_sum]

omit [Fintype n] [DecidableEq n] in
/-- A real symmetric matrix is Hermitian when viewed as complex. -/
lemma real_symmetric_isHermitian {A : Matrix n n ℝ} (hA : A.IsSymm) :
    (A.map Complex.ofReal).IsHermitian := by
  ext i j
  simp only [conjTranspose_apply, map_apply]
  have h_star : star (Complex.ofReal (A j i)) = Complex.ofReal (A j i) := by
    rw [Complex.star_def]
    exact Complex.conj_ofReal (A j i)
  rw [h_star, hA.apply j i]

/-- For real symmetric matrices, eigenvalues can be computed in ℝ. -/
private lemma real_symmetric_eigenvalues_real {A : Matrix n n ℝ} (hA : A.IsSymm) :
    let hAc := real_symmetric_isHermitian hA
    ∀ i, Complex.re (Complex.ofReal (hAc.eigenvalues i)) = hAc.eigenvalues i := by
  intro hAc i
  exact Complex.ofReal_re _

omit [DecidableEq n] in
/-- Aᵀ * A is symmetric for any real matrix A. -/
lemma transpose_mul_self_isSymm (A : Matrix n n ℝ) : (Aᵀ * A).IsSymm := by
  rw [IsSymm, transpose_mul, transpose_transpose]

omit [Fintype n] [DecidableEq n] in
/-- For real matrices, transpose = conjTranspose. -/
private lemma transpose_eq_conjTranspose (A : Matrix n n ℝ) :
    A.transpose = A.conjTranspose := by
  ext i j
  simp only [conjTranspose_apply, transpose_apply]
  exact (starRingEnd_self_apply (A j i)).symm

omit [DecidableEq n] in
/-- Aᵀ * A is Hermitian for real A (since transpose = conjTranspose). -/
private lemma transpose_mul_self_isHermitian' (A : Matrix n n ℝ) :
    (A.transpose * A).IsHermitian := by
  rw [transpose_eq_conjTranspose]
  exact (posSemidef_conjTranspose_mul_self A).isHermitian

/-- Eigenvalues of Aᵀ*A are nonnegative for real A. -/
lemma eigenvalues_transpose_mul_self_nonneg (A : Matrix n n ℝ) :
    let hATA := transpose_mul_self_isHermitian' A
    ∀ i, 0 ≤ hATA.eigenvalues i := by
  intro hATA i
  have h := eigenvalues_conjTranspose_mul_self_nonneg A
  have h_charpoly : (A.transpose * A).charpoly = (A.conjTranspose * A).charpoly := by
    simp only [transpose_eq_conjTranspose]
  have h_eig_eq : hATA.eigenvalues =
      (posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues :=
    hATA.eigenvalues_eq_eigenvalues_iff _ |>.mpr h_charpoly
  rw [h_eig_eq]
  exact h i

/-- Spectral theorem for real Hermitian matrices in direct form:
    A = V * Λ * Vᵀ where V is orthogonal. -/
private lemma real_spectral_theorem (A : Matrix n n ℝ) (hA : A.IsHermitian) :
    A = (hA.eigenvectorUnitary : Matrix n n ℝ) *
        diagonal hA.eigenvalues *
        (hA.eigenvectorUnitary : Matrix n n ℝ).transpose := by
  have h := hA.spectral_theorem
  simp only [Unitary.conjStarAlgAut_apply] at h
  -- Over ℝ: RCLike.ofReal = id
  rw [show diagonal hA.eigenvalues = diagonal (RCLike.ofReal ∘ hA.eigenvalues) by
    ext i j; simp only [diagonal, Function.comp_apply, of_apply]
    split_ifs with hij <;> simp [RCLike.ofReal, hij]]
  -- Over ℝ: star = transpose
  rw [show (hA.eigenvectorUnitary : Matrix n n ℝ).transpose =
          star (hA.eigenvectorUnitary : Matrix n n ℝ) by
    ext i j; simp [transpose]]
  exact h

/-! ### Real SVD Construction

We construct the real SVD by adapting the complex construction pattern.
Key insight: Over ℝ, `unitaryGroup = orthogonalGroup` and `star = transpose`.
-/

/-- The right orthogonal matrix V for SVD, obtained from eigenvectors of Aᵀ * A. -/
noncomputable def rightOrthogonal (A : Matrix n n ℝ) : orthogonalGroup n ℝ :=
  let hHerm := transpose_mul_self_isHermitian' A
  ⟨hHerm.eigenvectorUnitary, hHerm.eigenvectorUnitary.2⟩

/-- A * V, the key intermediate matrix for SVD construction. -/
noncomputable def realAV (A : Matrix n n ℝ) : Matrix n n ℝ :=
  A * (rightOrthogonal A : Matrix n n ℝ)

/-- Real singular values: σᵢ = √(eigenvalues of Aᵀ*A). -/
noncomputable def realSingularValues (A : Matrix n n ℝ) : n → ℝ :=
  let hHerm := transpose_mul_self_isHermitian' A
  fun i => Real.sqrt (hHerm.eigenvalues i)

/-- Key property: (A*V)ᵀ * (A*V) = diagonal of eigenvalues of Aᵀ*A. -/
lemma transpose_realAV_mul_realAV (A : Matrix n n ℝ) :
    (realAV A).transpose * realAV A =
    diagonal (transpose_mul_self_isHermitian' A).eigenvalues := by
  let hHerm := transpose_mul_self_isHermitian' A
  let V : Matrix n n ℝ := hHerm.eigenvectorUnitary
  have h := hHerm.spectral_theorem
  simp only [Unitary.conjStarAlgAut_apply] at h
  -- Over ℝ: RCLike.ofReal is identity
  have h_real_diag : diagonal (RCLike.ofReal ∘ hHerm.eigenvalues) = diagonal hHerm.eigenvalues := by
    ext i j; simp only [diagonal, of_apply, Function.comp_apply]
    split_ifs <;> simp [RCLike.ofReal]
  -- Over ℝ: star = transpose
  have h_star_eq_trans : star V = V.transpose := by ext i j; simp [star]
  have h_Vstar_V : star V * V = 1 := mem_unitaryGroup_iff'.mp (hHerm.eigenvectorUnitary).2
  simp only [realAV, rightOrthogonal]
  have step1 : (A * V).transpose * (A * V) = V.transpose * (A.transpose * A) * V := by
    rw [transpose_mul]; noncomm_ring
  have step2 : V.transpose * (A.transpose * A) * V = star V * (A.transpose * A) * V := by
    rw [← h_star_eq_trans]
  have step3 : star V * (A.transpose * A) * V =
               star V * (V * diagonal (RCLike.ofReal ∘ hHerm.eigenvalues) * star V) * V := by
    conv_lhs => rw [h]
  have step4 : star V * (V * diagonal (RCLike.ofReal ∘ hHerm.eigenvalues) * star V) * V =
               (star V * V) * diagonal (RCLike.ofReal ∘ hHerm.eigenvalues) * (star V * V) := by
    noncomm_ring
  have step5 : (star V * V) * diagonal (RCLike.ofReal ∘ hHerm.eigenvalues) * (star V * V) =
               diagonal (RCLike.ofReal ∘ hHerm.eigenvalues) := by
    rw [h_Vstar_V]; simp
  rw [step1, step2, step3, step4, step5, h_real_diag]

/-- Columns of A*V are orthogonal. -/
lemma realAV_columns_orthogonal (A : Matrix n n ℝ) (i j : n) (hij : i ≠ j) :
    ∑ k, (realAV A) k i * (realAV A) k j = 0 := by
  have h := transpose_realAV_mul_realAV A
  have h_entry : ((realAV A).transpose * realAV A) i j = ∑ k, (realAV A) k i * (realAV A) k j := by
    simp only [mul_apply, transpose_apply]
  have h_diag : (diagonal (transpose_mul_self_isHermitian' A).eigenvalues) i j = 0 := by
    simp only [diagonal_apply, hij, ↓reduceIte]
  rw [← h_entry, h, h_diag]

/-- Squared norm of column i of A*V equals σᵢ². -/
lemma realAV_column_norm_sq (A : Matrix n n ℝ) (i : n) :
    ∑ k, (realAV A) k i * (realAV A) k i = (realSingularValues A i) ^ 2 := by
  have h := transpose_realAV_mul_realAV A
  have h_entry : ((realAV A).transpose * realAV A) i i = ∑ k, (realAV A) k i * (realAV A) k i := by
    simp only [mul_apply, transpose_apply]
  rw [← h_entry, h, diagonal_apply_eq]
  simp only [realSingularValues]
  rw [Real.sq_sqrt]
  exact eigenvalues_transpose_mul_self_nonneg A i

/-- Left singular vector for nonzero σᵢ: uᵢ = (1/σᵢ) * (A*V)[:,i]. -/
noncomputable def leftSingularVectorNonzero_real (A : Matrix n n ℝ) (i : n)
    (_ : realSingularValues A i ≠ 0) : n → ℝ :=
  fun k => (realSingularValues A i)⁻¹ * realAV A k i

/-- Left singular vector as EuclideanSpace element. -/
noncomputable def leftSingularVectorEuclidean_real (A : Matrix n n ℝ) (i : n)
    (hi : realSingularValues A i ≠ 0) : EuclideanSpace ℝ n :=
  (WithLp.equiv 2 (n → ℝ)).symm (leftSingularVectorNonzero_real A i hi)

/-- Extended function: left singular vector for nonzero σ, 0 for zero σ. -/
noncomputable def leftSingularVectorExtended_real (A : Matrix n n ℝ) : n → EuclideanSpace ℝ n :=
  fun i => if h : realSingularValues A i ≠ 0
           then leftSingularVectorEuclidean_real A i h
           else 0

/-- Set of indices with nonzero singular values. -/
def nonzeroSingularIndices_real (A : Matrix n n ℝ) : Set n :=
  {i | realSingularValues A i ≠ 0}

set_option linter.unusedSectionVars false in
/-- Inner product on EuclideanSpace ℝ n equals sum formula. -/
private lemma inner_euclidean_eq_sum_real (x y : EuclideanSpace ℝ n) :
    @inner ℝ (EuclideanSpace ℝ n) _ x y = ∑ i, x i * y i := by
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply, conj_trivial]
  congr 1; ext i; ring

/-- Left singular vectors (on nonzero singular value indices) are orthonormal. -/
theorem leftSingularVectorExtended_orthonormal_on_nonzero_real (A : Matrix n n ℝ) :
    Orthonormal ℝ ((nonzeroSingularIndices_real A).restrict (leftSingularVectorExtended_real A)) := by
  rw [orthonormal_iff_ite]
  intro ⟨i, hi⟩ ⟨j, hj⟩
  simp only [Set.restrict_apply, nonzeroSingularIndices_real, Set.mem_setOf_eq] at hi hj ⊢
  have hi' : (if h : realSingularValues A i ≠ 0 then leftSingularVectorEuclidean_real A i h else 0)
            = leftSingularVectorEuclidean_real A i hi := dif_pos hi
  have hj' : (if h : realSingularValues A j ≠ 0 then leftSingularVectorEuclidean_real A j h else 0)
            = leftSingularVectorEuclidean_real A j hj := dif_pos hj
  simp only [leftSingularVectorExtended_real]
  rw [hi', hj']
  rw [inner_euclidean_eq_sum_real]
  simp only [leftSingularVectorEuclidean_real, leftSingularVectorNonzero_real,
             WithLp.equiv_symm_apply]
  by_cases h : i = j
  · -- Case i = j: inner product = 1
    subst h
    simp only [ite_true]
    have h_norm := realAV_column_norm_sq A i
    have factor : ∀ k : n,
        (realSingularValues A i)⁻¹ * realAV A k i * ((realSingularValues A i)⁻¹ * realAV A k i) =
        (realSingularValues A i)⁻¹ * (realSingularValues A i)⁻¹ * (realAV A k i * realAV A k i) := by
      intro k; ring
    simp_rw [factor, ← Finset.mul_sum, h_norm]
    have h_sq : (realSingularValues A i)⁻¹ * (realSingularValues A i)⁻¹ * (realSingularValues A i) ^ 2 =
                ((realSingularValues A i)⁻¹ * (realSingularValues A i)) ^ 2 := by ring
    rw [h_sq, inv_mul_cancel₀ hi, one_pow]
  · -- Case i ≠ j: inner product = 0
    simp only [Subtype.mk.injEq, h, ite_false]
    have h_orth := realAV_columns_orthogonal A i j h
    have factor : ∀ k : n,
        (realSingularValues A i)⁻¹ * realAV A k i * ((realSingularValues A j)⁻¹ * realAV A k j) =
        (realSingularValues A i)⁻¹ * (realSingularValues A j)⁻¹ * (realAV A k i * realAV A k j) := by
      intro k; ring
    simp_rw [factor, ← Finset.mul_sum, h_orth, mul_zero]

/-- Extend orthonormal left singular vectors to a full orthonormal basis. -/
noncomputable def extendedONB_real (A : Matrix n n ℝ) :
    OrthonormalBasis n ℝ (EuclideanSpace ℝ n) :=
  ((leftSingularVectorExtended_orthonormal_on_nonzero_real A).exists_orthonormalBasis_extension_of_card_eq
    finrank_euclideanSpace).choose

/-- The extended ONB agrees with left singular vectors on nonzero singular value indices. -/
theorem extendedONB_real_spec (A : Matrix n n ℝ) :
    ∀ i, i ∈ nonzeroSingularIndices_real A → (extendedONB_real A) i = leftSingularVectorExtended_real A i :=
  ((leftSingularVectorExtended_orthonormal_on_nonzero_real A).exists_orthonormalBasis_extension_of_card_eq
    finrank_euclideanSpace).choose_spec

/-- Convert an orthonormal basis of EuclideanSpace ℝ n to a matrix (column j = basis vector j). -/
noncomputable def onbToMatrix_real (b : OrthonormalBasis n ℝ (EuclideanSpace ℝ n)) : Matrix n n ℝ :=
  fun i j => (b j) i

/-- A matrix built from an orthonormal basis is orthogonal. -/
theorem onbToMatrix_real_mem_orthogonalGroup (b : OrthonormalBasis n ℝ (EuclideanSpace ℝ n)) :
    onbToMatrix_real b ∈ orthogonalGroup n ℝ := by
  rw [mem_orthogonalGroup_iff']
  ext i j
  simp only [mul_apply, transpose_apply, one_apply, onbToMatrix_real]
  have h_inner : @inner ℝ (EuclideanSpace ℝ n) _ (b i) (b j) = if i = j then 1 else 0 := by
    have h_on := b.orthonormal
    rw [orthonormal_iff_ite] at h_on
    exact h_on i j
  rw [← h_inner, inner_euclidean_eq_sum_real]

/-- The constructed orthogonal matrix U for real SVD. -/
noncomputable def constructedU_real (A : Matrix n n ℝ) : orthogonalGroup n ℝ :=
  ⟨onbToMatrix_real (extendedONB_real A), onbToMatrix_real_mem_orthogonalGroup _⟩

/-- Column j of constructed U equals the left singular vector when σⱼ ≠ 0. -/
theorem constructedU_real_column_eq (A : Matrix n n ℝ) (j : n) (hj : realSingularValues A j ≠ 0) :
    (fun i => (constructedU_real A : Matrix n n ℝ) i j) = leftSingularVectorNonzero_real A j hj := by
  ext i
  simp only [constructedU_real, onbToMatrix_real]
  have hj_mem : j ∈ nonzeroSingularIndices_real A := hj
  have h_spec := extendedONB_real_spec A j hj_mem
  have h_expand : leftSingularVectorExtended_real A j = leftSingularVectorEuclidean_real A j hj := dif_pos hj
  rw [h_spec, h_expand]
  simp only [leftSingularVectorEuclidean_real]
  rfl

/-- When σᵢ = 0, column i of A*V is zero. -/
lemma realAV_column_zero_of_singularValue_zero (A : Matrix n n ℝ) (i : n)
    (hi : realSingularValues A i = 0) :
    ∀ k, (realAV A) k i = 0 := by
  intro k
  have h_sum := realAV_column_norm_sq A i
  rw [hi] at h_sum
  simp only [sq, mul_zero] at h_sum
  -- Sum of squares = 0 implies each term = 0
  have h_each_nonneg : ∀ m, m ∈ Finset.univ → 0 ≤ (realAV A) m i * (realAV A) m i :=
    fun m _ => mul_self_nonneg _
  have h_each_zero := (Finset.sum_eq_zero_iff_of_nonneg h_each_nonneg).mp h_sum
  have hk := h_each_zero k (Finset.mem_univ k)
  exact mul_self_eq_zero.mp hk

/-- Key relationship: A * V = U * Σ for real matrices. -/
theorem realAV_eq_constructedU_real_mul_sigma (A : Matrix n n ℝ) :
    realAV A = (constructedU_real A : Matrix n n ℝ) * diagonal (realSingularValues A) := by
  ext i j
  simp only [mul_apply, diagonal_apply]
  -- RHS: ∑ x, U i x * (if x = j then σ x else 0) = U i j * σ j
  have h_rhs : ∑ x, (constructedU_real A : Matrix n n ℝ) i x *
               (if x = j then realSingularValues A x else 0) =
               (constructedU_real A : Matrix n n ℝ) i j * realSingularValues A j := by
    rw [Finset.sum_eq_single j]
    · simp only [↓reduceIte]
    · intro b _ hbj; simp only [hbj, ↓reduceIte, mul_zero]
    · intro hj_not_mem; exact absurd (Finset.mem_univ j) hj_not_mem
  rw [h_rhs]
  by_cases hj : realSingularValues A j ≠ 0
  · -- Case σⱼ ≠ 0: (A*V)ᵢⱼ = σⱼ * Uᵢⱼ
    have h_col := constructedU_real_column_eq A j hj
    have h_U_eq : (constructedU_real A : Matrix n n ℝ) i j = leftSingularVectorNonzero_real A j hj i := by
      exact congrFun h_col i
    rw [h_U_eq]
    simp only [leftSingularVectorNonzero_real, realAV]
    -- Uᵢⱼ = (1/σⱼ) * (A*V)ᵢⱼ, so σⱼ * Uᵢⱼ = (A*V)ᵢⱼ
    field_simp
  · -- Case σⱼ = 0: both sides are 0
    push_neg at hj
    have h_AV_zero := realAV_column_zero_of_singularValue_zero A j hj
    simp only [hj, mul_zero, h_AV_zero i]

/-- **Real SVD Theorem**: Any square real matrix A can be decomposed as A = U * Σ * Vᵀ
    where U and V are orthogonal matrices and Σ is diagonal with non-negative entries.

    **Proof:**
    1. V = eigenvectors of Aᵀ * A (from spectral theorem, automatically orthogonal)
    2. σᵢ = √(eigenvalues of Aᵀ * A) (nonnegative since Aᵀ * A is positive semidefinite)
    3. U is constructed by:
       - For σᵢ ≠ 0: column i = (1/σᵢ) * A * vᵢ (normalized left singular vector)
       - For σᵢ = 0: extend orthonormally to complete the basis
    4. The equation A = U * Σ * Vᵀ follows from A * V = U * Σ and V * Vᵀ = I -/
theorem svd_decomposition (A : Matrix n n ℝ) :
    ∃ (U V : Matrix.orthogonalGroup n ℝ) (σ : n → ℝ),
      (∀ i, 0 ≤ σ i) ∧
      A = (U : Matrix n n ℝ) * diagonal σ * (V : Matrix n n ℝ)ᵀ := by
  -- Use constructed U and V
  use constructedU_real A, rightOrthogonal A, realSingularValues A
  constructor
  · -- Singular values are nonnegative
    intro i
    exact Real.sqrt_nonneg _
  · -- Main equation: A = U * Σ * Vᵀ
    -- From realAV_eq_constructedU_real_mul_sigma: A * V = U * Σ
    -- Multiply both sides by Vᵀ: A * V * Vᵀ = U * Σ * Vᵀ
    -- Since V is orthogonal: V * Vᵀ = I, so A = U * Σ * Vᵀ
    have h_AV := realAV_eq_constructedU_real_mul_sigma A
    have hV := (rightOrthogonal A).2
    have h_V_VT : (rightOrthogonal A : Matrix n n ℝ) * (rightOrthogonal A : Matrix n n ℝ)ᵀ = 1 := by
      rw [mem_orthogonalGroup_iff] at hV
      exact hV
    calc A = A * 1 := by rw [mul_one]
      _ = A * ((rightOrthogonal A : Matrix n n ℝ) * (rightOrthogonal A : Matrix n n ℝ)ᵀ) := by rw [h_V_VT]
      _ = (A * (rightOrthogonal A : Matrix n n ℝ)) * (rightOrthogonal A : Matrix n n ℝ)ᵀ := by rw [mul_assoc]
      _ = realAV A * (rightOrthogonal A : Matrix n n ℝ)ᵀ := rfl
      _ = ((constructedU_real A : Matrix n n ℝ) * diagonal (realSingularValues A)) *
          (rightOrthogonal A : Matrix n n ℝ)ᵀ := by rw [h_AV]
      _ = (constructedU_real A : Matrix n n ℝ) * diagonal (realSingularValues A) *
          (rightOrthogonal A : Matrix n n ℝ)ᵀ := by rw [mul_assoc]

end Matrix.SVD.Real

/-! ### Helper lemmas for eigenvalues₀ -/

/-- eigenvalues₀ are nonneg for PosSemidef matrices.
    Transfer from `PosSemidef.eigenvalues_nonneg` via the bijection
    `eigenvalues j = eigenvalues₀ (equivOfCardEq.symm j)`. -/
lemma PosSemidef_eigenvalues₀_nonneg {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.PosSemidef) (i : Fin (Fintype.card n)) :
    0 ≤ hA.isHermitian.eigenvalues₀ i := by
  have h := hA.eigenvalues_nonneg ((Fintype.equivOfCardEq (Fintype.card_fin _)) i)
  unfold IsHermitian.eigenvalues at h
  simp only [Equiv.symm_apply_apply] at h
  exact h

/-- For an antitone nonneg function on Fin n, if only the first k values can be nonzero,
    then values at indices ≥ k are 0.
    Used to prove `eigenvalues₀_zero_beyond_rank`. -/
lemma antitone_nonneg_zeros_after_rank {n k : ℕ} (f : Fin n → ℝ)
    (h_anti : Antitone f) (h_nonneg : ∀ i, 0 ≤ f i)
    (h_card : Fintype.card {i : Fin n // f i ≠ 0} ≤ k)
    (i : Fin n) (hi : k ≤ i.val) : f i = 0 := by
  by_contra h_ne
  -- If f i ≠ 0, then all f j for j ≤ i are also ≠ 0 (by antitone + nonneg)
  have h_all_nonzero : ∀ j : Fin n, j ≤ i → f j ≠ 0 := by
    intro j hji h_fj_zero
    have h_fi_pos : 0 < f i := (h_nonneg i).lt_of_ne' h_ne
    have h_fj_ge : f j ≥ f i := h_anti hji
    linarith [h_fj_zero.symm ▸ h_fj_ge]
  -- So {j | f j ≠ 0} ⊇ {j | j ≤ i}, which has at least i.val + 1 elements
  have h_count : i.val + 1 ≤ Fintype.card {j : Fin n // f j ≠ 0} := by
    have h_iic : (Finset.Iic i).card = i.val + 1 := by simp [Fin.card_Iic]
    calc i.val + 1 = (Finset.Iic i).card := h_iic.symm
      _ ≤ (Finset.univ.filter (fun j : Fin n => f j ≠ 0)).card := by
          apply Finset.card_le_card
          intro j hj
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact h_all_nonzero j (Finset.mem_Iic.mp hj)
      _ = Fintype.card {j : Fin n // f j ≠ 0} := by rw [Fintype.card_subtype]
  -- But i.val + 1 > k ≥ card {j | f j ≠ 0}, contradiction
  omega

/-! ## Rectangular SVD

Extension of SVD to m × n matrices (not necessarily square).

### Mathematical Background

For an m × n matrix A:
- **Aᴴ*A** is an n × n positive semidefinite matrix
- **A*Aᴴ** is an m × m positive semidefinite matrix
- The nonzero eigenvalues of Aᴴ*A and A*Aᴴ are identical (by `Matrix.charpoly_mul_comm'`)
- Singular values σᵢ = √λᵢ where λᵢ are eigenvalues of the smaller Gram matrix

### Goal Statement

For any m × n complex matrix A, there exist:
- U ∈ unitaryGroup m ℂ (m × m unitary)
- V ∈ unitaryGroup n ℂ (n × n unitary)
- S : Matrix m n ℂ (rectangular "diagonal" with singular values)

Such that: **A = U * S * Vᴴ**

### References
- Horn & Johnson, *Matrix Analysis*, Chapter 7
- RectangularSVD-TODO.md for implementation plan
-/

namespace Matrix.SVD.Rectangular

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-! ### Eigenvalue Index Relationship -/

/-- Card of nonzero eigenvalues equals card of nonzero eigenvalues₀ via bijection. -/
lemma card_nonzero_eigenvalues₀_eq_card_nonzero_eigenvalues
    {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    Fintype.card {i : Fin (Fintype.card n) // hA.eigenvalues₀ i ≠ 0} =
    Fintype.card {j : n // hA.eigenvalues j ≠ 0} := by
  -- eigenvalues j = eigenvalues₀ (equiv.symm j), so use equiv for subtype
  let e := (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n))).symm
  have h_eq : ∀ j : n, hA.eigenvalues j = hA.eigenvalues₀ (e j) := fun j => rfl
  -- Build equivalence between the subtypes
  let f : {i : Fin (Fintype.card n) // hA.eigenvalues₀ i ≠ 0} →
          {j : n // hA.eigenvalues j ≠ 0} :=
    fun ⟨i, hi⟩ => ⟨e.symm i, by
      simp only [ne_eq, h_eq, e, Equiv.symm_symm, Equiv.symm_apply_apply]
      exact hi⟩
  let g : {j : n // hA.eigenvalues j ≠ 0} →
          {i : Fin (Fintype.card n) // hA.eigenvalues₀ i ≠ 0} :=
    fun ⟨j, hj⟩ => ⟨e j, by rwa [h_eq] at hj⟩
  have hfg : ∀ x, f (g x) = x := fun ⟨j, _⟩ => by simp [f, g]
  have hgf : ∀ x, g (f x) = x := fun ⟨i, _⟩ => by simp [f, g]
  -- Use the equivalence to show equal cardinality
  exact Fintype.card_eq.mpr ⟨{
    toFun := f
    invFun := g
    left_inv := hgf
    right_inv := hfg
  }⟩

set_option linter.unusedSectionVars false in
/-- Eigenvalues₀ of Aᴴ*A at indices beyond rank(A) are zero.

For a matrix A : m × n, rank(Aᴴ*A) = rank(A) ≤ min(m,n).
Since eigenvalues₀ is antitone (sorted decreasing), eigenvalues at index ≥ rank are 0.
When i.val ≥ card m and card m < card n, eigenvalues₀ i = 0. -/
lemma eigenvalues₀_zero_beyond_rank (A : Matrix m n ℂ) (i : Fin (Fintype.card n))
    (h_idx : i.val ≥ Fintype.card m)
    (_h_card : Fintype.card m < Fintype.card n) :
    (posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues₀ i = 0 := by
  let hAHA := posSemidef_conjTranspose_mul_self A
  let hermAHA := hAHA.isHermitian

  -- Step 1: eigenvalues₀ is nonneg
  have h_nonneg : ∀ j, 0 ≤ hermAHA.eigenvalues₀ j := PosSemidef_eigenvalues₀_nonneg hAHA

  -- Step 2: eigenvalues₀ is antitone
  have h_anti : Antitone hermAHA.eigenvalues₀ := hermAHA.eigenvalues₀_antitone

  -- Step 3: Rank bound: rank(Aᴴ*A) = rank(A) ≤ card m
  have h_rank_eq : (Aᴴ * A).rank = A.rank := rank_conjTranspose_mul_self A
  have h_rank_le : A.rank ≤ Fintype.card m := rank_le_card_height A

  -- Step 4: Transfer rank to card of nonzero eigenvalues₀
  have h_rank_eigs : Fintype.card {j : n // hermAHA.eigenvalues j ≠ 0} = (Aᴴ * A).rank :=
    (hermAHA.rank_eq_card_non_zero_eigs).symm

  have h_card_eigs₀ : Fintype.card {j : Fin (Fintype.card n) // hermAHA.eigenvalues₀ j ≠ 0} ≤ Fintype.card m := by
    calc Fintype.card {j : Fin (Fintype.card n) // hermAHA.eigenvalues₀ j ≠ 0}
      = Fintype.card {j : n // hermAHA.eigenvalues j ≠ 0} :=
          card_nonzero_eigenvalues₀_eq_card_nonzero_eigenvalues hermAHA
      _ = (Aᴴ * A).rank := h_rank_eigs
      _ = A.rank := h_rank_eq
      _ ≤ Fintype.card m := h_rank_le

  -- Step 5: Apply antitone_nonneg_zeros_after_rank
  exact antitone_nonneg_zeros_after_rank hermAHA.eigenvalues₀ h_anti h_nonneg h_card_eigs₀ i h_idx

/-! ### Singular Values for Rectangular Matrices -/

/-- Singular values for rectangular m × n matrices, indexed by `Fin (min (#m) (#n))`.

These are the square roots of eigenvalues of Aᴴ*A (the n×n Gram matrix), taking
the first `min(m,n)` eigenvalues (sorted in decreasing order by `eigenvalues₀`).

**Design choice**: We always use Aᴴ*A rather than switching between Aᴴ*A and A*Aᴴ.
This ensures consistency with `rightUnitary` (which uses eigenvectors of Aᴴ*A) and
avoids bijection mismatch issues between `equivFin` and `equivOfCardEq` when proving
the SVD equation A*V = U*S.

Mathematical justification: For A ∈ ℂ^{m×n}:
- Aᴴ*A has n eigenvalues, of which at most r = rank(A) ≤ min(m,n) are nonzero
- A*Aᴴ has the same nonzero eigenvalues (by spectrum.nonzero_mul_comm)
- Taking the first min(m,n) eigenvalues from either matrix gives the same values -/
noncomputable def singularValues (A : Matrix m n ℂ) :
    Fin (min (Fintype.card m) (Fintype.card n)) → ℝ := fun k =>
  -- Always use Aᴴ*A (n×n), consistent with rightUnitary
  let hermAHA := (posSemidef_conjTranspose_mul_self A).isHermitian
  let j : Fin (Fintype.card n) := Fin.castLE (Nat.min_le_right _ _) k
  Real.sqrt (hermAHA.eigenvalues₀ j)

set_option linter.unusedSectionVars false in
/-- Singular values are non-negative. -/
theorem singularValues_nonneg (A : Matrix m n ℂ) (k : Fin (min (Fintype.card m) (Fintype.card n))) :
    0 ≤ singularValues A k := by
  unfold singularValues
  exact Real.sqrt_nonneg _

/-! ### Right and Left Singular Vector Matrices -/


/-- Right singular vectors V: the eigenvector unitary of Aᴴ*A (n×n matrix).

The columns of V form an orthonormal basis of eigenvectors of Aᴴ*A,
ordered by decreasing eigenvalue (and thus decreasing singular value).
This is an n×n unitary matrix. -/
noncomputable def rightUnitary (A : Matrix m n ℂ) : unitaryGroup n ℂ :=
  (posSemidef_conjTranspose_mul_self A).isHermitian.eigenvectorUnitary

/-- Left singular vectors U: the eigenvector unitary of A*Aᴴ (m×m matrix).

The columns of U form an orthonormal basis of eigenvectors of A*Aᴴ,
ordered by decreasing eigenvalue (and thus decreasing singular value).
This is an m×m unitary matrix. -/
noncomputable def leftUnitary (A : Matrix m n ℂ) : unitaryGroup m ℂ :=
  (posSemidef_self_mul_conjTranspose A).isHermitian.eigenvectorUnitary

/-- The bijection used by eigenvalues to map a Fintype to `Fin (card α)`.
    This is equivalent to `Fintype.equivFin` and matches how Mathlib's
    `eigenvalues` is defined in terms of `eigenvalues₀`.
    We define this directly as `equivFin` for better proof interaction. -/
noncomputable def eigenvaluesBijection (α : Type*) [Fintype α] : α ≃ Fin (Fintype.card α) :=
  Fintype.equivFin α

/-! ### Rectangular "Diagonal" Matrix -/

/-- The rectangular "diagonal" matrix S : Matrix m n ℂ containing singular values.

For a rectangular m×n matrix, S has the structure:
- `S(i, j) = σₖ` if both i and j correspond to the same diagonal index k < min(m,n)
- `S(i, j) = 0` otherwise

This uses `eigenvaluesBijection` to establish canonical orderings of the abstract
index types m and n, consistent with how Mathlib's eigenvalues are indexed.
This ensures that the singular value at diagonal position (i, j) corresponds
to the correct eigenvector column in the unitary matrices. -/
noncomputable def singularDiagonal (A : Matrix m n ℂ) : Matrix m n ℂ := fun i j =>
  let fi : Fin (Fintype.card m) := eigenvaluesBijection m i
  let fj : Fin (Fintype.card n) := eigenvaluesBijection n j
  if h : fi.val = fj.val ∧ fi.val < min (Fintype.card m) (Fintype.card n) then
    Complex.ofReal (singularValues A ⟨fi.val, h.2⟩)
  else
    0

/-! ### Key Lemmas for Rectangular SVD

These lemmas bridge the definitions to the main SVD construction.
The core challenge is relating eigenvalues of AᴴA (n×n) and AAᴴ (m×m) when m ≠ n,
plus adapting square-case column norm proofs to rectangular index types.
-/

/-! #### Index Embedding Helpers

These functions cleanly map indices from `Fin (min #m #n)` to the abstract types m and n.
They compose `Fin.castLE` with `Fintype.equivFin` for canonical bijections. -/

/-- Embed an index from `Fin (min #m #n)` into the type `m`.
    This uses the canonical bijection `Fintype.equivFin m` and `Fin.castLE`. -/
noncomputable def embedMinToM (k : Fin (min (Fintype.card m) (Fintype.card n))) : m :=
  (Fintype.equivFin m).symm (Fin.castLE (Nat.min_le_left _ _) k)

/-- Embed an index from `Fin (min #m #n)` into the type `n`.
    This uses the canonical bijection `Fintype.equivFin n` and `Fin.castLE`. -/
noncomputable def embedMinToN (k : Fin (min (Fintype.card m) (Fintype.card n))) : n :=
  (Fintype.equivFin n).symm (Fin.castLE (Nat.min_le_right _ _) k)

set_option linter.unusedSectionVars false in
/-- The embedding `embedMinToM` is injective. -/
theorem embedMinToM_injective : Function.Injective (embedMinToM (m := m) (n := n)) := by
  intro k₁ k₂ h
  simp only [embedMinToM] at h
  have h1 : (Fintype.equivFin m).symm (Fin.castLE (Nat.min_le_left _ _) k₁) =
            (Fintype.equivFin m).symm (Fin.castLE (Nat.min_le_left _ _) k₂) := h
  have h2 := (Fintype.equivFin m).symm.injective h1
  exact Fin.castLE_injective _ h2

set_option linter.unusedSectionVars false in
/-- The embedding `embedMinToN` is injective. -/
theorem embedMinToN_injective : Function.Injective (embedMinToN (m := m) (n := n)) := by
  intro k₁ k₂ h
  simp only [embedMinToN] at h
  have h1 : (Fintype.equivFin n).symm (Fin.castLE (Nat.min_le_right _ _) k₁) =
            (Fintype.equivFin n).symm (Fin.castLE (Nat.min_le_right _ _) k₂) := h
  have h2 := (Fintype.equivFin n).symm.injective h1
  exact Fin.castLE_injective _ h2

/-! #### Type Coercion Bridge Lemmas -/

/-- Fintype.equivFin α equals (equivOfCardEq (card_fin _)).symm.

    Both are noncomputable bijections `α ≃ Fin (card α)` obtained via `Trunc.out`.
    This is a technical lemma needed to bridge between different ways Mathlib
    constructs equivalences to Fin types.

    NOTE: This relies on the internal implementation details of how Mathlib
    constructs these equivalences. Both ultimately use the same enumeration
    from `Fintype.elems`, so they should agree. -/
lemma equivFin_eq_equivOfCardEq_symm (α : Type*) [Fintype α] :
    Fintype.equivFin α = (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card α))).symm := by
  -- This is a definitional equality at the Trunc level - both are built from
  -- truncEquivFin which uses the same underlying enumeration.
  -- However, the composed Trunc operations make this non-trivially definitional.
  --
  -- Technical note: Both equivFin and equivOfCardEq.symm produce α ≃ Fin (card α)
  -- by extracting from Trunc values. The key insight is that:
  -- 1. truncEquivFin α produces Trunc (α ≃ Fin (card α)) from univ enumeration
  -- 2. truncEquivOfCardEq composes truncEquivFin with itself (for Fin types)
  -- 3. When β = Fin (card α), the composition simplifies to identity on Fin
  --
  -- The proof requires showing that truncEquivFin.out composed with its own
  -- inverse (via equivOfCardEq) gives the identity, which holds by construction.
  sorry

omit [DecidableEq m] [DecidableEq n] in
/-- The eigenvalues bijection composed with embedMinToN recovers castLE.
    This is the fundamental bridge: `eigenvaluesBijection n' (embedMinToN k) = castLE k`.

    Mathematical insight: Both `eigenvaluesBijection` (via equivOfCardEq.symm) and
    `embedMinToN` (via equivFin.symm) are noncomputable bijections chosen via Trunc.out.
    This lemma states they compose to give the expected castLE result. -/
theorem eigenvaluesBijection_embedMinToN (k : Fin (min (Fintype.card m) (Fintype.card n))) :
    eigenvaluesBijection n (embedMinToN k) = Fin.castLE (Nat.min_le_right _ _) k := by
  unfold embedMinToN eigenvaluesBijection
  -- eigenvaluesBijection = equivFin, embedMinToN uses equivFin.symm
  -- So: equivFin ((equivFin).symm (castLE k)) = castLE k by apply/symm cancel
  simp only [Equiv.apply_symm_apply]

omit [DecidableEq m] [DecidableEq n] in
/-- Inverse direction: from a Fin index in range, we can find the corresponding
    element of n' that maps back to it. -/
theorem embedMinToN_eigenvaluesBijection_inverse
    (i : Fin (Fintype.card n)) (hi : i.val < min (Fintype.card m) (Fintype.card n)) :
    embedMinToN (m := m) ⟨i.val, hi⟩ = (eigenvaluesBijection n).symm i := by
  unfold embedMinToN eigenvaluesBijection
  -- Goal: (equivFin n).symm (castLE ⟨i.val, hi⟩) = (equivFin n).symm i
  -- castLE ⟨i.val, hi⟩ = i (both have the same val), so congr closes it
  congr 1

omit [DecidableEq m] in
/-- The eigenvalue at embedMinToN(k) equals the eigenvalue at castLE(k).
    This is the key lemma for bridging singular value proofs to eigenvalue proofs. -/
theorem eigenvalues_at_embedMinToN_eq_eigenvalues₀_castLE
    (A : Matrix m n ℂ) (k : Fin (min (Fintype.card m) (Fintype.card n))) :
    let hermAHA := (posSemidef_conjTranspose_mul_self A).isHermitian
    hermAHA.eigenvalues (embedMinToN k) = hermAHA.eigenvalues₀ (Fin.castLE (Nat.min_le_right _ _) k) := by
  intro hermAHA
  -- eigenvalues j = eigenvalues₀ ((equivOfCardEq ...).symm j) by Mathlib definition
  -- So we need: (equivOfCardEq ...).symm (embedMinToN k) = castLE k
  simp only [Matrix.IsHermitian.eigenvalues]
  congr 1
  -- eigenvaluesBijection = equivFin = (equivOfCardEq ...).symm by equivFin_eq_equivOfCardEq_symm
  have h := eigenvaluesBijection_embedMinToN (m := m) k
  unfold eigenvaluesBijection at h
  -- h : equivFin n (embedMinToN k) = castLE k
  -- Need: (equivOfCardEq ...).symm (embedMinToN k) = castLE k
  rw [equivFin_eq_equivOfCardEq_symm] at h
  exact h

/-- For j : n' with eigenvaluesBijection(j).val < min, we can convert j to a Fin min index. -/
noncomputable def finMinOfAbstract (j : n)
    (hj : (eigenvaluesBijection n j).val < min (Fintype.card m) (Fintype.card n)) :
    Fin (min (Fintype.card m) (Fintype.card n)) :=
  ⟨(eigenvaluesBijection n j).val, hj⟩

omit [DecidableEq m] [DecidableEq n] in
/-- The conversion finMinOfAbstract is inverse to embedMinToN when applied appropriately. -/
theorem embedMinToN_finMinOfAbstract (j : n)
    (hj : (eigenvaluesBijection n j).val < min (Fintype.card m) (Fintype.card n)) :
    embedMinToN (m := m) (finMinOfAbstract j hj) = j := by
  unfold finMinOfAbstract embedMinToN eigenvaluesBijection
  simp_rw [equivFin_eq_equivOfCardEq_symm]
  -- Goal: (equivOfCardEq ..) (castLE ⟨(equivOfCardEq ..).symm j, hj⟩) = j
  -- Key: castLE preserves value, and equivOfCardEq (equivOfCardEq.symm j) = j
  conv_lhs => rw [show Fin.castLE _ ⟨((Fintype.equivOfCardEq (Fintype.card_fin _)).symm j).val, _⟩ =
    (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n))).symm j from Fin.ext (by rfl)]
  simp only [Equiv.symm_symm, Equiv.apply_symm_apply]

set_option linter.unusedSectionVars false in
/-- eigenvaluesBijection_val_eq_finMinOfAbstract -/
theorem eigenvaluesBijection_finMinOfAbstract (j : n)
    (hj : (eigenvaluesBijection n j).val < min (Fintype.card m) (Fintype.card n)) :
    (eigenvaluesBijection n j).val = (finMinOfAbstract (m := m) j hj).val := rfl

omit [DecidableEq m] in
/-- Key bridge for proofs: singularValues at k equals sqrt of eigenvalue at embedMinToN k. -/
theorem singularValues_eq_sqrt_eigenvalues_at_embedMinToN
    (A : Matrix m n ℂ) (k : Fin (min (Fintype.card m) (Fintype.card n))) :
    singularValues A k =
    Real.sqrt ((posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues (embedMinToN k)) := by
  simp only [singularValues]
  -- Goal: sqrt(hermAHA.eigenvalues₀ (castLE k)) = sqrt(hermAHA.eigenvalues (embedMinToN k))
  -- We need to show the arguments to sqrt are equal
  rw [eigenvalues_at_embedMinToN_eq_eigenvalues₀_castLE]

/-! #### Shared Nonzero Eigenvalues -/

/-- The characteristic polynomials of AᴴA and AAᴴ are related by powers of X.
    X^n · charpoly(A * B) = X^m · charpoly(B * A)
    i.e., X^n · charpoly(A * Aᴴ) = X^m · charpoly(Aᴴ * A)
    Rearranging: X^m · charpoly(AᴴA) = X^n · charpoly(AAᴴ) -/
theorem charpoly_conjTranspose_mul_self_mul_comm (A : Matrix m n ℂ) :
    Polynomial.X ^ Fintype.card m * (Aᴴ * A).charpoly =
    Polynomial.X ^ Fintype.card n * (A * Aᴴ).charpoly := by
  -- Apply charpoly_mul_comm' with first matrix = A, second = Aᴴ
  have h := Matrix.charpoly_mul_comm' A Aᴴ
  -- h : X^n * (A * Aᴴ).charpoly = X^m * (Aᴴ * A).charpoly
  exact h.symm

/-- Helper: X^k * p ≠ 0 when p ≠ 0 over ℂ[X]. -/
private lemma X_pow_mul_ne_zero {k : ℕ} {p : ℂ[X]} (hp : p ≠ 0) : Polynomial.X ^ k * p ≠ 0 :=
  mul_ne_zero (pow_ne_zero k Polynomial.X_ne_zero) hp

/-- Helper: For μ ≠ 0, μ ∈ roots(X^k * p) ↔ μ ∈ roots(p).
    The X^k factor only adds zeros as roots. -/
private lemma mem_roots_X_pow_mul_iff_of_ne_zero {k : ℕ} {p : ℂ[X]} {μ : ℂ}
    (hp : p ≠ 0) (hμ : μ ≠ 0) : μ ∈ (Polynomial.X ^ k * p).roots ↔ μ ∈ p.roots := by
  have hne : Polynomial.X ^ k * p ≠ 0 := X_pow_mul_ne_zero hp
  rw [Polynomial.roots_mul hne, Multiset.mem_add, Polynomial.roots_X_pow]
  constructor
  · intro h
    rcases h with h_left | h_right
    · rw [Multiset.mem_nsmul] at h_left
      simp only [Multiset.mem_singleton] at h_left
      exact absurd h_left.2 hμ
    · exact h_right
  · intro h
    right
    exact h

/-- The nonzero eigenvalues of AᴴA and AAᴴ match.

    This is a consequence of the characteristic polynomial relation:
    X^m · charpoly(AᴴA) = X^n · charpoly(AAᴴ)

    For any nonzero μ, being an eigenvalue means being a root of the charpoly.
    Since X^k only adds zeros as roots, the nonzero roots of both sides match. -/
theorem eigenvalues_shared_rectangular_aux (A : Matrix m n ℂ) (μ : ℝ) (hμ : μ ≠ 0) :
    (∃ i : n, (posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues i = μ) ↔
    (∃ j : m, (posSemidef_self_mul_conjTranspose A).isHermitian.eigenvalues j = μ) := by
  let hAHA := (posSemidef_conjTranspose_mul_self A).isHermitian
  let hAAH := (posSemidef_self_mul_conjTranspose A).isHermitian
  -- The characteristic polynomial equality: X^n * (AAᴴ).charpoly = X^m * (AᴴA).charpoly
  have h_charpoly := charpoly_mul_comm' A Aᴴ
  -- Roots of charpoly = eigenvalues mapped to ℂ
  have h_roots_AHA := hAHA.roots_charpoly_eq_eigenvalues
  have h_roots_AAH := hAAH.roots_charpoly_eq_eigenvalues
  -- Convert eigenvalue existence to root membership in charpoly
  have h_mem_iff_AHA : (∃ i : n, hAHA.eigenvalues i = μ) ↔ (↑μ : ℂ) ∈ (Aᴴ * A).charpoly.roots := by
    rw [h_roots_AHA, Multiset.mem_map]
    constructor
    · intro ⟨i, hi⟩
      refine ⟨i, Finset.mem_univ i, ?_⟩
      simp only [Function.comp_apply]
      exact congrArg _ hi
    · intro ⟨i, _, hi⟩
      exact ⟨i, Complex.ofReal_injective hi⟩
  have h_mem_iff_AAH : (∃ j : m, hAAH.eigenvalues j = μ) ↔ (↑μ : ℂ) ∈ (A * Aᴴ).charpoly.roots := by
    rw [h_roots_AAH, Multiset.mem_map]
    constructor
    · intro ⟨j, hj⟩
      refine ⟨j, Finset.mem_univ j, ?_⟩
      simp only [Function.comp_apply]
      exact congrArg _ hj
    · intro ⟨j, _, hj⟩
      exact ⟨j, Complex.ofReal_injective hj⟩
  rw [h_mem_iff_AHA, h_mem_iff_AAH]
  -- Now use the polynomial equality to show nonzero root membership is equivalent
  have hp_AHA : (Aᴴ * A).charpoly ≠ 0 := Matrix.charpoly_monic _ |>.ne_zero
  have hp_AAH : (A * Aᴴ).charpoly ≠ 0 := Matrix.charpoly_monic _ |>.ne_zero
  have hμ' : (↑μ : ℂ) ≠ 0 := by simp [hμ]
  -- μ ∈ (AᴴA).charpoly.roots ↔ μ ∈ (X^m * AᴴA.charpoly).roots  (since μ ≠ 0)
  --                          ↔ μ ∈ (X^n * AAᴴ.charpoly).roots  (by h_charpoly)
  --                          ↔ μ ∈ (AAᴴ).charpoly.roots        (since μ ≠ 0)
  rw [← mem_roots_X_pow_mul_iff_of_ne_zero hp_AHA hμ',
      ← mem_roots_X_pow_mul_iff_of_ne_zero hp_AAH hμ',
      h_charpoly.symm]


/-! #### Column Norms for Rectangular A*V

For a rectangular m×n matrix A with V = rightUnitary A (n×n), the product A*V is m×n.
The key lemma: the squared norm of column j of A*V equals the j-th eigenvalue of AᴴA,
which equals (singularValues A k)² when j corresponds to index k.
-/

set_option linter.unusedSectionVars false in
/-- Key computational lemma: (A*V)ᴴ * (A*V) = diag(eigenvalues of AᴴA)
    where V is the eigenvector matrix of AᴴA.

    This is the rectangular analogue of `conjTranspose_AV_mul_AV` from the square case.
    Note: A*V is m×n, so (A*V)ᴴ*(A*V) is n×n. -/
theorem conjTranspose_AV_mul_AV_rectangular (A : Matrix m n ℂ) :
    let V : Matrix n n ℂ := rightUnitary A
    let eig := (posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues
    (A * V)ᴴ * (A * V) = diagonal (Complex.ofReal ∘ eig) := by
  intro V eig
  -- The proof follows the same structure as the square case
  rw [conjTranspose_mul]
  -- Vᴴ * Aᴴ * (A * V) = Vᴴ * (Aᴴ * A) * V
  have h_assoc : Vᴴ * Aᴴ * (A * V) = Vᴴ * (Aᴴ * A) * V := by
    simp only [Matrix.mul_assoc]
  rw [h_assoc]
  -- Apply spectral theorem: Aᴴ * A = V * diag(eig) * Vᴴ
  have h_spectral : Aᴴ * A = V * diagonal (Complex.ofReal ∘ eig) * Vᴴ :=
    (posSemidef_conjTranspose_mul_self A).isHermitian.spectral_theorem
  have hVV : Vᴴ * V = 1 := mem_unitaryGroup_iff'.mp (rightUnitary A).2
  calc Vᴴ * (Aᴴ * A) * V
      = Vᴴ * (V * diagonal (Complex.ofReal ∘ eig) * Vᴴ) * V := by simp only [h_spectral]
    _ = Vᴴ * V * diagonal (Complex.ofReal ∘ eig) * Vᴴ * V := by simp only [Matrix.mul_assoc]
    _ = 1 * diagonal (Complex.ofReal ∘ eig) * Vᴴ * V := by rw [hVV]
    _ = diagonal (Complex.ofReal ∘ eig) * Vᴴ * V := by rw [one_mul]
    _ = diagonal (Complex.ofReal ∘ eig) * (Vᴴ * V) := by simp only [Matrix.mul_assoc]
    _ = diagonal (Complex.ofReal ∘ eig) * 1 := by rw [hVV]
    _ = diagonal (Complex.ofReal ∘ eig) := by rw [mul_one]

/-- Squared norm of column j of A*V equals σⱼ² (eigenvalue of AᴴA).

    This is the rectangular analogue of `AV_column_norm_sq` from the square case. -/
lemma AV_column_norm_sq_rectangular (A : Matrix m n ℂ) (j : n) :
    let V : Matrix n n ℂ := rightUnitary A
    let AV := A * V
    ∑ i, star (AV i j) * AV i j =
      Complex.ofReal ((posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues j) := by
  intro V AV
  have h_diag := conjTranspose_AV_mul_AV_rectangular A
  simp only at h_diag
  -- (AVᴴ * AV)ⱼⱼ = ∑ᵢ star(AV i j) * (AV i j)
  have h_entry : (AVᴴ * AV) j j = ∑ i, star (AV i j) * AV i j := by
    simp only [conjTranspose_apply, mul_apply]
  rw [← h_entry, h_diag, diagonal_apply_eq, Function.comp_apply]

/-- Columns of A*V are orthogonal (rectangular case).
    For j ≠ j', the inner product of columns j and j' is 0. -/
lemma AV_columns_orthogonal_rectangular (A : Matrix m n ℂ) (j j' : n) (hjj' : j ≠ j') :
    let V : Matrix n n ℂ := rightUnitary A
    let AV := A * V
    ∑ i, star (AV i j) * AV i j' = 0 := by
  intro V AV
  have h_diag := conjTranspose_AV_mul_AV_rectangular A
  simp only at h_diag
  have h_entry : (AVᴴ * AV) j j' = ∑ i, star (AV i j) * AV i j' := by
    simp only [conjTranspose_apply, mul_apply]
  rw [← h_entry, h_diag, diagonal_apply, if_neg hjj']

/-! #### Left Singular Vectors for Rectangular Matrices

For rectangular m×n matrix A with singular value σⱼ ≠ 0, the j-th left singular vector is:
  uⱼ = (1/σⱼ) · (column j of A*V)

This is an m-dimensional vector (unlike the square case which gives n-dimensional).
The vectors are orthonormal: ⟨uᵢ, uⱼ⟩ = δᵢⱼ for all i, j with σᵢ, σⱼ ≠ 0.
-/

/-- Helper: convert eigenvalue of AᴴA to singular value.
    For rectangular matrices, we use `eigenvalues j` directly (indexed by the matrix column type n)
    rather than `eigenvalues₀` to avoid bijection mismatch issues between `equivFin` and
    `equivOfCardEq`. The `eigenvalues_nonneg` lemma applies directly to this definition. -/
noncomputable def singularValueFromEigenvalue (A : Matrix m n ℂ) (j : n) : ℝ :=
  Real.sqrt ((posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues j)

set_option linter.unusedSectionVars false in
/-- Relates the Fin-indexed `singularValues` to the n-indexed `singularValueFromEigenvalue`.

Since both `singularValues` and `singularValueFromEigenvalue` use eigenvalues of Aᴴ*A,
and we use `eigenvaluesBijection` (same as `equivOfCardEq.symm`) for indexing,
the equality follows from the definition of `eigenvalues` in Mathlib. -/
lemma singularValues_eq_singularValueFromEigenvalue (A : Matrix m n ℂ) (j : n)
    (h_in_min : (eigenvaluesBijection n j).val < min (Fintype.card m) (Fintype.card n)) :
    singularValues A ⟨(eigenvaluesBijection n j).val, h_in_min⟩ = singularValueFromEigenvalue A j := by
  -- After architectural change: both singularValues and singularValueFromEigenvalue use Aᴴ*A
  -- Since eigenvaluesBijection = equivFin and eigenvalues uses equivOfCardEq.symm bijection,
  -- we need to bridge via our equivFin_eq_equivOfCardEq_symm lemma
  simp only [singularValues, singularValueFromEigenvalue]
  congr 1
  -- Goal: eigenvalues₀ (Fin.castLE .. ⟨(eigenvaluesBijection n j).val, h_in_min⟩) = eigenvalues j
  -- Use eigenvalues_at_embedMinToN_eq_eigenvalues₀_castLE with k = ⟨(eigenvaluesBijection n j).val, h_in_min⟩
  have h_bridge := eigenvalues_at_embedMinToN_eq_eigenvalues₀_castLE
    A ⟨(eigenvaluesBijection n j).val, h_in_min⟩
  -- h_bridge: eigenvalues (embedMinToN k) = eigenvalues₀ (castLE k)
  -- We need the reverse: eigenvalues₀ (castLE k) = eigenvalues j
  rw [← h_bridge]
  congr 1
  -- Goal: embedMinToN ⟨↑((eigenvaluesBijection n) j), h_in_min⟩ = j
  -- Use embedMinToN_eigenvaluesBijection_inverse and then Equiv.symm_apply_apply
  rw [embedMinToN_eigenvaluesBijection_inverse (eigenvaluesBijection n j) h_in_min]
  exact Equiv.symm_apply_apply (eigenvaluesBijection n) j

/-- The j-th left singular vector for rectangular A (when σⱼ ≠ 0).
    Output type is m → ℂ (m-dimensional vector).

    Definition: uⱼ = (1/σⱼ) · (column j of A*V) -/
noncomputable def leftSingularVectorNonzero_rectangular (A : Matrix m n ℂ) (j : n)
    (_ : singularValueFromEigenvalue A j ≠ 0) : m → ℂ :=
  let AV := A * (rightUnitary A : Matrix n n ℂ)
  fun i => (Complex.ofReal (singularValueFromEigenvalue A j))⁻¹ * AV i j

/-- The squared norm of a left singular vector is 1 (rectangular case).
    Uses: ‖uⱼ‖² = (1/σⱼ)² · ‖(A*V)[:,j]‖² = (1/σⱼ)² · σⱼ² = 1 -/
theorem leftSingularVectorNonzero_rectangular_inner_self (A : Matrix m n ℂ) (j : n)
    (hj : singularValueFromEigenvalue A j ≠ 0) :
    ∑ i, star (leftSingularVectorNonzero_rectangular A j hj i) *
             (leftSingularVectorNonzero_rectangular A j hj i) = 1 := by
  unfold leftSingularVectorNonzero_rectangular
  have h_norm := AV_column_norm_sq_rectangular A j
  simp only [star_mul', RCLike.star_def, map_inv₀, Complex.conj_ofReal]
  -- Factor out (σ⁻¹)² from the sum
  have factor : ∀ i : m,
      ((Complex.ofReal (singularValueFromEigenvalue A j) : ℂ))⁻¹ *
        (starRingEnd ℂ) ((A * (rightUnitary A : Matrix n n ℂ)) i j) *
        (((Complex.ofReal (singularValueFromEigenvalue A j) : ℂ))⁻¹ *
         (A * (rightUnitary A : Matrix n n ℂ)) i j) =
      ((Complex.ofReal (singularValueFromEigenvalue A j) : ℂ))⁻¹ *
       ((Complex.ofReal (singularValueFromEigenvalue A j) : ℂ))⁻¹ *
        ((starRingEnd ℂ) ((A * (rightUnitary A : Matrix n n ℂ)) i j) *
         (A * (rightUnitary A : Matrix n n ℂ)) i j) := by
    intro i; ring
  conv_lhs => arg 2; ext i; rw [factor i]
  rw [← Finset.mul_sum]
  have h_star_eq : ∀ i : m, (starRingEnd ℂ) ((A * (rightUnitary A : Matrix n n ℂ)) i j) =
      star ((A * (rightUnitary A : Matrix n n ℂ)) i j) := fun _ => rfl
  simp_rw [h_star_eq]
  -- The sum is now ∑ᵢ star(AV i j) * (AV i j), which equals the eigenvalue
  simp only at h_norm
  -- Need to show the eigenvalue equals σ²
  have h_eig_eq_sq : Complex.ofReal ((posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues j) =
      Complex.ofReal ((singularValueFromEigenvalue A j) ^ 2) := by
    unfold singularValueFromEigenvalue
    congr 1
    rw [Real.sq_sqrt]
    exact (posSemidef_conjTranspose_mul_self A).eigenvalues_nonneg j
  rw [h_norm, h_eig_eq_sq]
  -- Now: (σ⁻¹)² · σ² = 1
  have hj' : (Complex.ofReal (singularValueFromEigenvalue A j) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact hj
  have h_sq_eq : (Complex.ofReal ((singularValueFromEigenvalue A j) ^ 2) : ℂ) =
      ((Complex.ofReal (singularValueFromEigenvalue A j) : ℂ)) *
       ((Complex.ofReal (singularValueFromEigenvalue A j) : ℂ)) := by
    rw [sq, Complex.ofReal_mul]
  rw [h_sq_eq]
  field_simp

/-- Left singular vectors for different indices are orthogonal (rectangular case).
    For j ≠ j' with both σⱼ, σⱼ' ≠ 0, we have ⟨uⱼ, uⱼ'⟩ = 0. -/
theorem leftSingularVectorNonzero_rectangular_orthogonal (A : Matrix m n ℂ) (j j' : n)
    (hj : singularValueFromEigenvalue A j ≠ 0) (hj' : singularValueFromEigenvalue A j' ≠ 0)
    (hjj' : j ≠ j') :
    ∑ i, star (leftSingularVectorNonzero_rectangular A j hj i) *
             (leftSingularVectorNonzero_rectangular A j' hj' i) = 0 := by
  unfold leftSingularVectorNonzero_rectangular
  have h_orth := AV_columns_orthogonal_rectangular A j j' hjj'
  simp only [star_mul', RCLike.star_def, map_inv₀, Complex.conj_ofReal]
  have factor : ∀ i : m,
      ((Complex.ofReal (singularValueFromEigenvalue A j) : ℂ))⁻¹ *
        (starRingEnd ℂ) ((A * (rightUnitary A : Matrix n n ℂ)) i j) *
        (((Complex.ofReal (singularValueFromEigenvalue A j') : ℂ))⁻¹ *
         (A * (rightUnitary A : Matrix n n ℂ)) i j') =
      ((Complex.ofReal (singularValueFromEigenvalue A j) : ℂ))⁻¹ *
       ((Complex.ofReal (singularValueFromEigenvalue A j') : ℂ))⁻¹ *
        ((starRingEnd ℂ) ((A * (rightUnitary A : Matrix n n ℂ)) i j) *
         (A * (rightUnitary A : Matrix n n ℂ)) i j') := by
    intro i; ring
  conv_lhs => arg 2; ext i; rw [factor i]
  rw [← Finset.mul_sum]
  have h_star_eq : ∀ i : m, (starRingEnd ℂ) ((A * (rightUnitary A : Matrix n n ℂ)) i j) =
      star ((A * (rightUnitary A : Matrix n n ℂ)) i j) := fun _ => rfl
  simp_rw [h_star_eq, h_orth, mul_zero]

/-! #### Singular Values Ordering

The singular values inherit the decreasing order from `IsHermitian.eigenvalues`.
This is important for truncated SVD and Eckart-Young theorem.

Note: `Matrix.IsHermitian.eigenvalues` are sorted in decreasing order by construction
(via `LinearMap.IsSymmetric.eigenvalues` which uses a sorted list).
The antitone property follows from this ordering.
-/

set_option linter.unusedSectionVars false in
/-- Singular values are non-increasing (antitone).
    This follows from the eigenvalue ordering of Hermitian matrices.

    The eigenvalues of a Hermitian matrix are sorted in decreasing order by construction
    (via `eigenvalues₀_antitone`), so larger indices give smaller eigenvalues.
    Since singular values are square roots of eigenvalues (which are nonneg), the ordering
    is preserved by `Real.sqrt_le_sqrt`. -/
theorem singularValues_antitone (A : Matrix m n ℂ) :
    Antitone (singularValues A) := by
  intro k₁ k₂ hk
  unfold singularValues
  -- Always use AᴴA eigenvalues₀ (after architectural change)
  apply Real.sqrt_le_sqrt
  -- eigenvalues₀_antitone: k₁ ≤ k₂ → eigenvalues₀ k₂ ≤ eigenvalues₀ k₁
  -- castLE preserves ≤: k₁ ≤ k₂ → castLE k₁ ≤ castLE k₂
  have h_cast : Fin.castLE (Nat.min_le_right (Fintype.card m) (Fintype.card n)) k₁ ≤
                Fin.castLE (Nat.min_le_right (Fintype.card m) (Fintype.card n)) k₂ := by
    simp only [Fin.le_def, Fin.coe_castLE]
    exact hk
  exact (posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues₀_antitone h_cast

/-! ### Rectangular Coherence Infrastructure

These lemmas connect rank to singular values for rectangular matrices,
enabling the coherence factor extension in CoherenceCharacterization.lean.

For A : Matrix m n ℂ:
- rank(A) ≤ min(#m, #n)
- rank(A) = |{k : σₖ ≠ 0}| where σₖ are singular values
-/

set_option linter.unusedSectionVars false in
/-- The rank of a rectangular matrix is at most the minimum of its dimensions.
    This follows from Mathlib's `rank_le_card_height` and `rank_le_card_width`. -/
theorem rank_le_min_card (A : Matrix m n ℂ) :
    A.rank ≤ min (Fintype.card m) (Fintype.card n) := by
  apply Nat.le_min.mpr
  constructor
  · exact rank_le_card_height A
  · exact rank_le_card_width A

set_option linter.unusedSectionVars false in
/-- Nonzero singular values (for rectangular matrices) correspond to nonzero eigenvalues of Aᴴ*A.
    Since σₖ = √(λₖ) where λₖ ≥ 0, we have σₖ ≠ 0 ↔ λₖ ≠ 0.

    This is the rectangular analogue of `singularValues_ne_zero_iff_eigenvalues_ne_zero`
    from the square case in CoherenceCharacterization.lean. -/
theorem singularValues_ne_zero_iff_eigenvalues₀_ne_zero (A : Matrix m n ℂ)
    (k : Fin (min (Fintype.card m) (Fintype.card n))) :
    singularValues A k ≠ 0 ↔
    (posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues₀
      (Fin.castLE (Nat.min_le_right _ _) k) ≠ 0 := by
  let hermAHA := (posSemidef_conjTranspose_mul_self A).isHermitian
  let j := Fin.castLE (Nat.min_le_right (Fintype.card m) (Fintype.card n)) k
  have h_eig_nonneg : 0 ≤ hermAHA.eigenvalues₀ j := by
    have h_psd := posSemidef_conjTranspose_mul_self A
    exact PosSemidef_eigenvalues₀_nonneg h_psd j
  constructor
  · intro h_sv_ne h_eig_eq
    -- If σₖ ≠ 0, then √(λₖ) ≠ 0, so λₖ ≠ 0
    unfold singularValues at h_sv_ne
    simp only [h_eig_eq, Real.sqrt_zero, ne_eq, not_true] at h_sv_ne
  · intro h_eig_ne
    -- If λₖ ≠ 0 and λₖ ≥ 0, then λₖ > 0, so √λₖ > 0 ≠ 0
    unfold singularValues
    have h_pos : 0 < hermAHA.eigenvalues₀ j := lt_of_le_of_ne h_eig_nonneg (ne_comm.mpr h_eig_ne)
    exact ne_of_gt (Real.sqrt_pos.mpr h_pos)

/-- The rank of a rectangular matrix equals the number of nonzero singular values.

    For A : Matrix m n ℂ, we have:
      rank(A) = rank(Aᴴ*A) = |{k : eigenvalues₀ k ≠ 0}| = |{k : singularValues A k ≠ 0}|

    Key insight: The singular values are indexed by Fin (min #m #n), and
    rank(A) ≤ min(#m, #n), so all nonzero singular values fit within this index range. -/
theorem rank_eq_card_nonzero_singularValues_rect (A : Matrix m n ℂ) :
    A.rank = Fintype.card {k : Fin (min (Fintype.card m) (Fintype.card n)) // singularValues A k ≠ 0} := by
  let hermAHA := (posSemidef_conjTranspose_mul_self A).isHermitian
  let h_psd := posSemidef_conjTranspose_mul_self A

  -- Step 1: rank(A) = rank(Aᴴ*A)
  have h_rank_eq : A.rank = (Aᴴ * A).rank := (rank_conjTranspose_mul_self A).symm

  -- Step 2: rank(Aᴴ*A) = |{j : n // eigenvalues j ≠ 0}| by Hermitian characterization
  have h_herm_rank : (Aᴴ * A).rank = Fintype.card {j : n // hermAHA.eigenvalues j ≠ 0} :=
    hermAHA.rank_eq_card_non_zero_eigs

  -- Step 3: Convert to eigenvalues₀ (indexed by Fin (card n))
  have h_card_eig₀_eq_eig : Fintype.card {i : Fin (Fintype.card n) // hermAHA.eigenvalues₀ i ≠ 0} =
                            Fintype.card {j : n // hermAHA.eigenvalues j ≠ 0} :=
    card_nonzero_eigenvalues₀_eq_card_nonzero_eigenvalues hermAHA

  -- Step 4: Show nonzero eigenvalues₀ only occur for indices < min(#m, #n)
  -- Since rank(A) ≤ min(#m, #n) and eigenvalues₀ is antitone with nonneg values,
  -- indices ≥ min(#m, #n) have eigenvalue 0

  -- Build bijection between {k : Fin (min ..) | σₖ ≠ 0} and {i : Fin (card n) | λᵢ ≠ 0}
  -- The key is that for i with i.val ≥ min(#m, #n), we have λᵢ = 0

  -- Helper: eigenvalues₀ at index ≥ rank are 0
  have h_rank_le : A.rank ≤ min (Fintype.card m) (Fintype.card n) := rank_le_min_card A

  -- The nonzero eigenvalues₀ are exactly those at indices < rank(A) ≤ min(#m, #n)
  -- Due to antitone property and rank = card of nonzero eigenvalues

  -- Build the bijection via restriction
  have h_card_eq : Fintype.card {k : Fin (min (Fintype.card m) (Fintype.card n)) // singularValues A k ≠ 0} =
                   Fintype.card {i : Fin (Fintype.card n) // hermAHA.eigenvalues₀ i ≠ 0} := by
    -- Forward: k ↦ castLE k (since singularValues uses eigenvalues₀ ∘ castLE)
    -- Backward: i ↦ ⟨i.val, ...⟩ when i.val < min ...
    apply Fintype.card_eq.mpr
    let cast_to_n := fun (k : Fin (min (Fintype.card m) (Fintype.card n))) =>
                       Fin.castLE (Nat.min_le_right _ _) k
    refine ⟨{
      toFun := fun ⟨k, hk⟩ => ⟨cast_to_n k, (singularValues_ne_zero_iff_eigenvalues₀_ne_zero A k).mp hk⟩
      invFun := fun ⟨i, hi⟩ => by
        -- Need to show i.val < min(#m, #n) when eigenvalues₀ i ≠ 0
        -- This follows from: at indices ≥ rank(A), eigenvalues₀ = 0 (by antitonicity)
        -- and rank(A) ≤ min(#m, #n)
        by_cases h_lt : i.val < min (Fintype.card m) (Fintype.card n)
        · refine ⟨⟨i.val, h_lt⟩, ?_⟩
          have h_eq : Fin.castLE (Nat.min_le_right _ _) (⟨i.val, h_lt⟩ :
              Fin (min (Fintype.card m) (Fintype.card n))) = i := by ext; simp
          rw [singularValues_ne_zero_iff_eigenvalues₀_ne_zero]
          simp only [h_eq]
          exact hi
        · -- Contradiction: if i.val ≥ min(#m, #n), then eigenvalues₀ i = 0
          exfalso
          push_neg at h_lt
          -- Since card_nonzero_eigenvalues₀ ≤ rank(A) ≤ min(#m, #n) ≤ i.val,
          -- and eigenvalues₀ is antitone with nonzero entries only for indices < card_nonzero,
          -- we must have eigenvalues₀ i = 0
          -- Use antitone_nonneg_zeros_after_rank
          have h_card_le : Fintype.card {j : Fin (Fintype.card n) // hermAHA.eigenvalues₀ j ≠ 0} ≤
                           min (Fintype.card m) (Fintype.card n) := by
            calc Fintype.card {j : Fin (Fintype.card n) // hermAHA.eigenvalues₀ j ≠ 0}
              = Fintype.card {j : n // hermAHA.eigenvalues j ≠ 0} := h_card_eig₀_eq_eig
              _ = (Aᴴ * A).rank := h_herm_rank.symm
              _ = A.rank := h_rank_eq.symm
              _ ≤ min (Fintype.card m) (Fintype.card n) := h_rank_le
          have h_zero := antitone_nonneg_zeros_after_rank hermAHA.eigenvalues₀
            hermAHA.eigenvalues₀_antitone
            (fun j => PosSemidef_eigenvalues₀_nonneg h_psd j)
            h_card_le i h_lt
          exact hi h_zero
      left_inv := fun ⟨k, hk⟩ => by
        simp only [cast_to_n]
        -- The invFun at cast_to_n k = ⟨k.val, ...⟩ should give back k
        -- Since k : Fin (min #m #n), we have k.val < min(#m, #n)
        have h_k_lt : k.val < min (Fintype.card m) (Fintype.card n) := k.isLt
        simp only [Fin.coe_castLE, h_k_lt, ↓reduceDIte]
      right_inv := fun ⟨i, hi⟩ => by
        simp only [cast_to_n]
        -- Need: the inverse gives back i
        -- The inverse picks ⟨i.val, h_lt⟩ and castLE gives back i
        -- This requires showing i.val < min(#m, #n)
        have h_lt : i.val < min (Fintype.card m) (Fintype.card n) := by
          by_contra h_not_lt
          push_neg at h_not_lt
          have h_card_le : Fintype.card {j : Fin (Fintype.card n) // hermAHA.eigenvalues₀ j ≠ 0} ≤
                           min (Fintype.card m) (Fintype.card n) := by
            calc Fintype.card {j : Fin (Fintype.card n) // hermAHA.eigenvalues₀ j ≠ 0}
              = Fintype.card {j : n // hermAHA.eigenvalues j ≠ 0} := h_card_eig₀_eq_eig
              _ = (Aᴴ * A).rank := h_herm_rank.symm
              _ = A.rank := h_rank_eq.symm
              _ ≤ min (Fintype.card m) (Fintype.card n) := h_rank_le
          have h_zero := antitone_nonneg_zeros_after_rank hermAHA.eigenvalues₀
            hermAHA.eigenvalues₀_antitone
            (fun j => PosSemidef_eigenvalues₀_nonneg h_psd j)
            h_card_le i h_not_lt
          exact hi h_zero
        simp only [h_lt, ↓reduceDIte, Subtype.mk.injEq, Fin.ext_iff, Fin.coe_castLE]
    }⟩

  rw [h_rank_eq, h_herm_rank, ← h_card_eig₀_eq_eig, h_card_eq]

/-! ### Frobenius-Singular Value Connection for Rectangular Matrices

This section establishes that for rectangular matrices A : Matrix m n ℂ,
the Frobenius norm squared equals the sum of squared singular values:
  ‖A‖_F² = ∑ k, (singularValues A k)²

**Key insight:**
- trace(Aᴴ*A) = ∑ j:n, eigenvalues j (for the n×n Hermitian matrix Aᴴ*A)
- singularValues A k = √(eigenvalues₀ (Fin.castLE k)) for k < min(#m, #n)
- Eigenvalues for indices ≥ min(#m, #n) are zero (by rank constraint)

Therefore the sum over singular values (indexed by Fin (min #m #n)) captures
all nonzero eigenvalues, and equals the trace.
-/

omit [DecidableEq m] in
/-- Singular values squared equal the corresponding eigenvalues₀ for rectangular matrices.
    This is the rectangular analogue of `singularValues_sq`. -/
theorem singularValues_sq_rect (A : Matrix m n ℂ) (k : Fin (min (Fintype.card m) (Fintype.card n))) :
    (singularValues A k) ^ 2 =
    (posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues₀
      (Fin.castLE (Nat.min_le_right _ _) k) := by
  unfold singularValues
  have h_nonneg := PosSemidef_eigenvalues₀_nonneg (posSemidef_conjTranspose_mul_self A)
    (Fin.castLE (Nat.min_le_right (Fintype.card m) (Fintype.card n)) k)
  rw [Real.sq_sqrt h_nonneg]

set_option linter.unusedSectionVars false in
/-- Eigenvalues beyond index min(#m, #n) are zero.
    This follows from rank(A) ≤ min(#m, #n) and the eigenvalue structure. -/
theorem eigenvalues₀_zero_beyond_min (A : Matrix m n ℂ) (j : Fin (Fintype.card n))
    (hj : j.val ≥ min (Fintype.card m) (Fintype.card n)) :
    (posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues₀ j = 0 := by
  let hermAHA := (posSemidef_conjTranspose_mul_self A).isHermitian
  let h_psd := posSemidef_conjTranspose_mul_self A
  -- rank(A) ≤ min(#m, #n) ≤ j.val
  have h_rank_le : A.rank ≤ min (Fintype.card m) (Fintype.card n) := rank_le_min_card A
  have h_card_nonzero : Fintype.card {i : Fin (Fintype.card n) // hermAHA.eigenvalues₀ i ≠ 0} ≤
                        min (Fintype.card m) (Fintype.card n) := by
    have h_eq := card_nonzero_eigenvalues₀_eq_card_nonzero_eigenvalues hermAHA
    have h_herm_rank := hermAHA.rank_eq_card_non_zero_eigs
    have h_rank_eq : A.rank = (Aᴴ * A).rank := (rank_conjTranspose_mul_self A).symm
    calc Fintype.card {i : Fin (Fintype.card n) // hermAHA.eigenvalues₀ i ≠ 0}
        = Fintype.card {i : n // hermAHA.eigenvalues i ≠ 0} := h_eq
      _ = (Aᴴ * A).rank := h_herm_rank.symm
      _ = A.rank := h_rank_eq.symm
      _ ≤ min (Fintype.card m) (Fintype.card n) := h_rank_le
  exact antitone_nonneg_zeros_after_rank hermAHA.eigenvalues₀
    hermAHA.eigenvalues₀_antitone
    (fun i => PosSemidef_eigenvalues₀_nonneg h_psd i)
    h_card_nonzero j hj

/-- **Sum of squared singular values equals trace** for rectangular matrices.
    For A : Matrix m n ℂ, ∑ k, (singularValues A k)² = Re(trace(Aᴴ * A)).

    This is the rectangular analogue of `sum_sq_singularValues_eq_trace`. -/
theorem sum_sq_singularValues_rect_eq_trace (A : Matrix m n ℂ) :
    ∑ k, (singularValues A k) ^ 2 = Complex.re (Matrix.trace (Aᴴ * A)) := by
  let hermAHA := (posSemidef_conjTranspose_mul_self A).isHermitian
  -- trace(Aᴴ*A) = ∑ j:n, eigenvalues j (as complex numbers)
  have h_trace := hermAHA.trace_eq_sum_eigenvalues
  rw [h_trace, Complex.re_sum]
  -- eigenvalues j = eigenvalues₀ (bijection j)
  -- Note: eigenvalues are ℝ, cast to ℂ, then we take .re which recovers the original ℝ value
  have h_eig_eq : ∀ j : n, hermAHA.eigenvalues j =
      hermAHA.eigenvalues₀ ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm j) := fun _ => rfl
  -- Convert RHS: .re of (ℝ : ℂ) back to ℝ, then eigenvalues to eigenvalues₀
  trans (∑ i : n, hermAHA.eigenvalues i)
  swap
  · apply Finset.sum_congr rfl
    intro j _
    exact (Complex.ofReal_re _).symm
  -- Sum equivalence via bijection n ≃ Fin (card n)
  let e := (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n))).symm
  have h_sum_bij : ∑ j : n, hermAHA.eigenvalues j = ∑ i : Fin (Fintype.card n), hermAHA.eigenvalues₀ i := by
    simp_rw [h_eig_eq]
    exact Finset.sum_equiv e (fun _ => by simp [Finset.mem_univ]) (fun _ _ => rfl)
  rw [h_sum_bij]
  -- Now sum over Fin (card n), but only indices < min(#m, #n) contribute (rest are 0)
  -- Use singular values squared = eigenvalues₀ ∘ castLE
  conv_lhs =>
    arg 2; ext k
    rw [singularValues_sq_rect]
  -- Partition Fin (card n) into {i | i.val < min} and {i | i.val ≥ min}
  have h_sum_split : ∑ i : Fin (Fintype.card n), hermAHA.eigenvalues₀ i =
      ∑ i ∈ Finset.univ.filter (fun i : Fin (Fintype.card n) => i.val < min (Fintype.card m) (Fintype.card n)),
        hermAHA.eigenvalues₀ i +
      ∑ i ∈ Finset.univ.filter (fun i : Fin (Fintype.card n) => i.val ≥ min (Fintype.card m) (Fintype.card n)),
        hermAHA.eigenvalues₀ i := by
    rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
          (p := fun i => i.val < min (Fintype.card m) (Fintype.card n))]
    congr 1
    -- Show filter (not (< min)) = filter (≥ min)
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt, ge_iff_le, le_iff_lt_or_eq]
  rw [h_sum_split]
  -- The second sum is 0 (eigenvalues beyond min are 0)
  have h_tail_zero : ∑ i ∈ Finset.univ.filter
      (fun i : Fin (Fintype.card n) => i.val ≥ min (Fintype.card m) (Fintype.card n)),
        hermAHA.eigenvalues₀ i = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact eigenvalues₀_zero_beyond_min A i hi
  rw [h_tail_zero, add_zero]
  -- Now show: ∑ k : Fin (min ..), eigenvalues₀ (castLE k) =
  --           ∑ i ∈ filter (< min), eigenvalues₀ i
  symm
  -- The LHS sums over i : Fin (card n) with i.val < min, the RHS sums over k : Fin (min ...)
  -- We establish a bijection: i ↦ ⟨i.val, hi⟩ and k ↦ ⟨k.val, k.isLt_min_right⟩
  refine Finset.sum_bij'
    (fun i hi => ⟨i.val, by simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi; exact hi⟩)
    (fun k _ => ⟨k.val, Nat.lt_of_lt_of_le k.isLt (Nat.min_le_right _ _)⟩) ?_ ?_ ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_univ]
  · intro k _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact k.isLt
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    ext; rfl
  · intro k _
    ext; rfl
  · intro i _
    congr 1

end Matrix.SVD.Rectangular

/-! ## Frobenius Norm - Singular Values Connection for Rectangular Matrices -/

section FrobeniusNormRectangular

open Matrix.SVD.Rectangular

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

attribute [local instance] Matrix.frobeniusSeminormedAddCommGroup

/-- **Frobenius norm squared equals sum of squared singular values** for rectangular matrices.
    This connects to the trace identity via trace(Aᴴ*A) = ‖A‖_F². -/
theorem Matrix.SVD.Rectangular.frobeniusNorm_sq_eq_sum_singularValues_sq_rect (A : Matrix m n ℂ) :
    ‖A‖ ^ 2 = ∑ k, (singularValues A k) ^ 2 := by
  rw [sum_sq_singularValues_rect_eq_trace]
  -- ‖A‖_F² = trace(Aᴴ*A).re
  rw [frobenius_norm_def]
  have h_nonneg : 0 ≤ ∑ i, ∑ j, ‖A i j‖ ^ (2 : ℝ) :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => Real.rpow_nonneg (norm_nonneg _) _))
  -- (x^(1/2))^2 = x for x ≥ 0
  have h_sq_sqrt : ((∑ i, ∑ j, ‖A i j‖ ^ (2 : ℝ)) ^ (1/2 : ℝ)) ^ 2 = ∑ i, ∑ j, ‖A i j‖ ^ (2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul h_nonneg]
    norm_num
  rw [h_sq_sqrt]
  -- Goal: ∑ i, ∑ j, ‖A i j‖ ^ 2 = trace(Aᴴ*A).re
  simp only [trace, diag_apply, mul_apply, conjTranspose_apply]
  rw [Finset.sum_comm]
  -- RHS is (∑ x, ∑ x_1, star (A x_1 x) * A x_1 x).re
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  -- Goal: ‖A i j‖ ^ 2 = (star (A i j) * A i j).re
  rw [Complex.star_def]
  -- Goal: ‖A i j‖ ^ 2 = (conj (A i j) * A i j).re
  rw [Complex.conj_mul']
  -- Goal: ‖A i j‖ ^ 2 = (↑‖A i j‖ ^ 2).re
  simp only [← Complex.ofReal_pow, Complex.ofReal_re]
  -- Need to convert ℝ power to ℕ power: x ^ (2:ℝ) = x ^ (2:ℕ)
  norm_cast

/-- **Frobenius norm equals square root of sum of squared singular values** for rectangular matrices. -/
theorem Matrix.SVD.Rectangular.frobeniusNorm_eq_sqrt_sum_singularValues_sq_rect (A : Matrix m n ℂ) :
    ‖A‖ = Real.sqrt (∑ k, (singularValues A k) ^ 2) := by
  have h_sq := frobeniusNorm_sq_eq_sum_singularValues_sq_rect A
  have h_nonneg : 0 ≤ ‖A‖ := norm_nonneg _
  rw [← h_sq, Real.sqrt_sq h_nonneg]

end FrobeniusNormRectangular

/-! ## Spectral Norm for Rectangular Matrices

This section establishes that for rectangular matrices `A : Matrix m n ℂ`:
- `‖A‖² = ‖Aᴴ*A‖ = λ_max(Aᴴ*A)` (spectral norm squared equals max eigenvalue of Gram matrix)
- `‖A‖ = max{σₖ}` where σₖ are the singular values

These connect the L2 operator norm to singular values, generalizing the square case
in `MatrixNormRelations.lean` to rectangular matrices.

**Key insight:** The fundamental identity `‖A‖² = ‖Aᴴ*A‖` holds for all rectangular A
(from `Matrix.l2_opNorm_conjTranspose_mul_self` in Mathlib). Since Aᴴ*A is a square
Hermitian positive semidefinite n×n matrix, its spectral norm equals its max eigenvalue,
which equals the max squared singular value of A.
-/

section SpectralNormRectangular

open Matrix.SVD.Rectangular

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

-- Enable L2 operator norm instances locally for this section (needed for CStarAlgebra)
attribute [local instance] Matrix.instL2OpNormedAddCommGroup
attribute [local instance] Matrix.instL2OpNormedSpace
attribute [local instance] Matrix.instL2OpNormedRing
attribute [local instance] Matrix.instL2OpNormedAlgebra
attribute [local instance] Matrix.instL2OpMetricSpace
attribute [local instance] Matrix.instCStarRing

/-- The CStarAlgebra instance for complex matrices with L2 operator norm. -/
private noncomputable def instCStarAlgebraMatrixLocal : CStarAlgebra (Matrix n n ℂ) :=
  CStarAlgebra.mk

/-- Notation for L2 operator norm of rectangular matrices. -/
local notation "‖" A "‖₂" => @Norm.norm _ Matrix.instL2OpNormedAddCommGroup.toNorm A

/-! ### Helper Lemmas for Spectral Norm -/

/-- For a Hermitian matrix H, the L2 operator norm equals the spectral radius. -/
private theorem l2_opNorm_hermitian_eq_spectralRadius
    (H : Matrix n n ℂ) (hH : Matrix.IsHermitian H) :
    @Norm.norm _ Matrix.instL2OpNormedAddCommGroup.toNorm H = (spectralRadius ℝ H).toReal := by
  -- Use the CStarAlgebra instance for matrices with L2 norm
  have h_sa : IsSelfAdjoint H := hH.isSelfAdjoint
  -- The L2 norm of matrices forms a C*-algebra, so we can use the spectral radius formula
  have := @IsSelfAdjoint.toReal_spectralRadius_eq_norm (Matrix n n ℂ)
    instCStarAlgebraMatrixLocal H h_sa
  exact this.symm

/-- The spectral radius of a Hermitian matrix equals the supremum of absolute eigenvalues. -/
private theorem hermitian_spectralRadius_eq_sup_abs_eigenvalues [Nonempty n]
    (H : Matrix n n ℂ) (hH : Matrix.IsHermitian H) :
    (spectralRadius ℝ H).toReal = Finset.sup' Finset.univ Finset.univ_nonempty (|hH.eigenvalues ·|) := by
  have h_spec := hH.spectrum_real_eq_range_eigenvalues
  simp only [spectralRadius, h_spec]
  rw [iSup_range]
  have h_ne_top : ∀ i, ((‖hH.eigenvalues i‖₊ : NNReal) : ENNReal) ≠ ⊤ := fun i => ENNReal.coe_ne_top
  rw [ENNReal.toReal_iSup h_ne_top]
  have h_eq : ∀ i, (↑(‖hH.eigenvalues i‖₊) : ENNReal).toReal = |hH.eigenvalues i| := fun i => by
    simp only [ENNReal.toReal, ENNReal.toNNReal_coe]
    simp only [nnnorm, Real.norm_eq_abs]
    rfl
  simp_rw [h_eq]
  symm
  rw [Finset.sup'_eq_csSup_image]
  simp only [Finset.coe_univ, Set.image_univ, sSup_range]

/-- For a Hermitian matrix, ‖H‖ = max |λᵢ| where λᵢ are eigenvalues. -/
private theorem l2_opNorm_hermitian_eq_sup_abs_eigenvalues [Nonempty n]
    (H : Matrix n n ℂ) (hH : Matrix.IsHermitian H) :
    @Norm.norm _ Matrix.instL2OpNormedAddCommGroup.toNorm H =
      Finset.sup' Finset.univ Finset.univ_nonempty (|hH.eigenvalues ·|) := by
  rw [l2_opNorm_hermitian_eq_spectralRadius H hH]
  exact hermitian_spectralRadius_eq_sup_abs_eigenvalues H hH

/-- For nonneg values, sup(f²) = (sup f)². Helper lemma for spectral norm theorem. -/
private lemma sup'_sq_eq_sq_sup' {α : Type*} {s : Finset α} (hs : s.Nonempty) (f : α → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) :
    s.sup' hs (fun i => (f i) ^ 2) = (s.sup' hs f) ^ 2 := by
  obtain ⟨j, hjs, hj⟩ := s.exists_mem_eq_sup' hs f
  rw [hj]
  apply le_antisymm
  · apply Finset.sup'_le
    intro i hi
    have : f i ≤ f j := by
      calc f i ≤ s.sup' hs f := Finset.le_sup' f hi
        _ = f j := hj
    exact sq_le_sq' (by linarith [hf i hi]) this
  · exact Finset.le_sup' (fun i => (f i) ^ 2) hjs

/-! ### Main Theorems -/

/-- The largest singular value of a rectangular matrix. -/
noncomputable def Matrix.SVD.Rectangular.maxSingularValue
    (h : 0 < min (Fintype.card m) (Fintype.card n)) (A : Matrix m n ℂ) : ℝ :=
  Finset.sup' Finset.univ (Finset.univ_nonempty_iff.mpr ⟨⟨0, h⟩⟩) (singularValues A)

/-- **Spectral norm squared equals max eigenvalue of Aᴴ*A** for rectangular matrices.

This is the key intermediate result connecting operator norm to eigenvalues. -/
theorem Matrix.SVD.Rectangular.spectral_norm_sq_eq_max_eigenvalue_rect
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (h : 0 < min (Fintype.card m) (Fintype.card n)) (A : Matrix m n ℂ) :
    @Norm.norm _ Matrix.instL2OpNormedAddCommGroup.toNorm A ^ 2 = Finset.sup' Finset.univ
      (Finset.univ_nonempty_iff.mpr (⟨⟨0, Nat.lt_of_lt_of_le h (Nat.min_le_right _ _)⟩⟩ : Nonempty (Fin (Fintype.card n))))
      (posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues₀ := by
  -- Step 1: ‖A‖² = ‖Aᴴ*A‖ (fundamental C*-algebra identity)
  have h1 : @Norm.norm _ Matrix.instL2OpNormedAddCommGroup.toNorm A ^ 2 =
      @Norm.norm _ Matrix.instL2OpNormedAddCommGroup.toNorm (Aᴴ * A) := by
    have := Matrix.l2_opNorm_conjTranspose_mul_self A
    linarith [sq_nonneg ‖A‖₂]
  rw [h1]
  -- Step 2: Aᴴ*A is Hermitian positive semidefinite
  let h_psd := posSemidef_conjTranspose_mul_self A
  let h_herm := h_psd.isHermitian
  -- Step 3: For Hermitian PSD matrices, ‖H‖ = max eigenvalue = max |eigenvalue| = max eigenvalue (since ≥ 0)
  have h_nonempty_n : Nonempty n := by
    have : 0 < Fintype.card n := Nat.lt_of_lt_of_le h (Nat.min_le_right _ _)
    exact Fintype.card_pos_iff.mp this
  -- ‖Aᴴ*A‖ = sup |eigenvalues|
  have h2 : @Norm.norm _ Matrix.instL2OpNormedAddCommGroup.toNorm (Aᴴ * A) =
      Finset.sup' Finset.univ Finset.univ_nonempty (|h_herm.eigenvalues ·|) :=
    l2_opNorm_hermitian_eq_sup_abs_eigenvalues (Aᴴ * A) h_herm
  -- For PSD, eigenvalues ≥ 0 so |λ| = λ
  have h3 : ∀ i, |h_herm.eigenvalues i| = h_herm.eigenvalues i := fun i =>
    abs_of_nonneg (h_psd.eigenvalues_nonneg i)
  rw [h2]
  -- Convert: sup over unsorted eigenvalues = sup over sorted eigenvalues₀
  -- For PSD, |λ| = λ
  conv_lhs => rw [show (fun x => |h_herm.eigenvalues x|) = (fun x => h_herm.eigenvalues x) from
    funext h3]
  -- eigenvalues and eigenvalues₀ have the same image (one is a sorted reindexing of the other)
  -- eigenvalues₀ k = eigenvalues ((Fintype.equivOfCardEq _) k) by Mathlib's definition
  -- So their sups are equal. We prove this by showing each is ≤ the other.
  let equiv := (Fintype.equivOfCardEq (Fintype.card_fin _) : Fin (Fintype.card n) ≃ n)
  apply le_antisymm
  · -- sup eigenvalues ≤ sup eigenvalues₀
    apply Finset.sup'_le
    intro i _
    -- eigenvalues i = eigenvalues₀ (equiv.symm i)
    have h_eq : h_herm.eigenvalues i = h_herm.eigenvalues₀ (equiv.symm i) := by
      simp only [Matrix.IsHermitian.eigenvalues, equiv]
    rw [h_eq]
    exact Finset.le_sup' h_herm.eigenvalues₀ (Finset.mem_univ _)
  · -- sup eigenvalues₀ ≤ sup eigenvalues
    apply Finset.sup'_le
    intro j _
    -- eigenvalues₀ j = eigenvalues (equiv j)
    have h_eq : h_herm.eigenvalues₀ j = h_herm.eigenvalues (equiv j) := by
      simp only [Matrix.IsHermitian.eigenvalues, equiv, Equiv.symm_apply_apply]
    rw [h_eq]
    exact Finset.le_sup' h_herm.eigenvalues (Finset.mem_univ _)

/-- **Spectral norm squared equals max squared singular value** for rectangular matrices.

This converts from eigenvalues to singular values using σₖ² = λₖ. -/
theorem Matrix.SVD.Rectangular.spectral_norm_sq_eq_max_singularValue_sq_rect
    (h : 0 < min (Fintype.card m) (Fintype.card n)) (A : Matrix m n ℂ) :
    ‖A‖₂ ^ 2 = Finset.sup' Finset.univ
      (Finset.univ_nonempty_iff.mpr ⟨⟨0, h⟩⟩)
      (fun k => (singularValues A k) ^ 2) := by
  -- First establish the eigenvalue version
  have h_eig := spectral_norm_sq_eq_max_eigenvalue_rect h A
  rw [h_eig]
  -- Now we need: sup_{j : Fin #n} eigenvalues₀ j = sup_{k : Fin min} (singularValues A k)²
  let h_psd := posSemidef_conjTranspose_mul_self A
  let h_herm := h_psd.isHermitian
  -- Key: eigenvalues beyond min are 0, and singularValues k² = eigenvalues₀ (castLE k)
  -- So the sup over all eigenvalues₀ equals the sup over singular values²
  apply le_antisymm
  · -- sup eigenvalues₀ ≤ sup singularValues²
    apply Finset.sup'_le
    intro j _
    by_cases hj : j.val < min (Fintype.card m) (Fintype.card n)
    · -- j < min: eigenvalues₀ j = singularValues ⟨j.val, hj⟩²
      have h_eq : h_herm.eigenvalues₀ j = (singularValues A ⟨j.val, hj⟩) ^ 2 := by
        rw [singularValues_sq_rect]
        congr 1
      rw [h_eq]
      exact Finset.le_sup' (fun k => (singularValues A k) ^ 2) (Finset.mem_univ _)
    · -- j ≥ min: eigenvalues₀ j = 0
      have hj' : j.val ≥ min (Fintype.card m) (Fintype.card n) := Nat.not_lt.mp hj
      have h_zero := eigenvalues₀_zero_beyond_min A j hj'
      rw [h_zero]
      apply Finset.le_sup'_of_le (fun k => (singularValues A k) ^ 2) (Finset.mem_univ ⟨0, h⟩)
      exact sq_nonneg _
  · -- sup singularValues² ≤ sup eigenvalues₀
    apply Finset.sup'_le
    intro k _
    have h_eq : (singularValues A k) ^ 2 = h_herm.eigenvalues₀ (Fin.castLE (Nat.min_le_right _ _) k) := by
      rw [singularValues_sq_rect]
    rw [h_eq]
    apply Finset.le_sup'
    exact Finset.mem_univ _

/-- **The spectral norm of a rectangular matrix equals its largest singular value.**

For any matrix A, ‖A‖₂ = σ₁(A) = √(λ_max(Aᴴ A)).

This is the main result of this section, generalizing `spectral_norm_eq_max_singularValue`
from square matrices to rectangular matrices. -/
theorem Matrix.SVD.Rectangular.spectral_norm_eq_max_singularValue_rect
    (h : 0 < min (Fintype.card m) (Fintype.card n)) (A : Matrix m n ℂ) :
    ‖A‖₂ = maxSingularValue h A := by
  unfold maxSingularValue
  -- Nonemptiness proof for Finset.sup'
  have h_ne : (Finset.univ : Finset (Fin (min (Fintype.card m) (Fintype.card n)))).Nonempty :=
    Finset.univ_nonempty_iff.mpr ⟨⟨0, h⟩⟩
  have h_norm_nonneg : 0 ≤ ‖A‖₂ := @norm_nonneg (Matrix m n ℂ) _ A
  have h_maxSV_nonneg : 0 ≤ Finset.sup' Finset.univ h_ne (singularValues A) := by
    apply Finset.le_sup'_of_le (singularValues A) (Finset.mem_univ ⟨0, h⟩)
    exact singularValues_nonneg A ⟨0, h⟩
  -- We have ‖A‖² = (max σₖ)² from spectral_norm_sq_eq_max_singularValue_sq_rect
  have h_sq_eq : ‖A‖₂ ^ 2 = (Finset.sup' Finset.univ h_ne (singularValues A)) ^ 2 := by
    rw [spectral_norm_sq_eq_max_singularValue_sq_rect h A]
    -- Goal: sup' (fun k => (σₖ)²) = (sup' σₖ)²
    -- Apply sup'_sq_eq_sq_sup' which gives: sup' (fun i => (f i)²) = (sup' f)²
    rw [sup'_sq_eq_sq_sup' h_ne (singularValues A) (fun i _ => singularValues_nonneg A i)]
  -- From x² = y² and x,y ≥ 0, conclude x = y
  have h_abs_eq : |‖A‖₂| = |Finset.sup' Finset.univ h_ne (singularValues A)| :=
    (sq_eq_sq_iff_abs_eq_abs ‖A‖₂ _).mp h_sq_eq
  rwa [abs_of_nonneg h_norm_nonneg, abs_of_nonneg h_maxSV_nonneg] at h_abs_eq

/-- Spectral norm squared is bounded by sum of squared singular values (rectangular). -/
theorem Matrix.SVD.Rectangular.spectral_norm_sq_le_sum_singularValues_sq_rect
    (h : 0 < min (Fintype.card m) (Fintype.card n)) (A : Matrix m n ℂ) :
    ‖A‖₂ ^ 2 ≤ ∑ k, (singularValues A k) ^ 2 := by
  rw [spectral_norm_sq_eq_max_singularValue_sq_rect h A]
  apply Finset.sup'_le
  intro k _
  exact Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ k)

/-- **Spectral norm is bounded by Frobenius norm** for rectangular matrices: ‖A‖₂ ≤ ‖A‖_F.

This generalizes `spectral_norm_le_frobenius_norm` to rectangular matrices. -/
theorem Matrix.SVD.Rectangular.spectral_norm_le_frobenius_norm_rect
    (h : 0 < min (Fintype.card m) (Fintype.card n)) (A : Matrix m n ℂ) :
    ‖A‖₂ ≤ Real.sqrt (∑ k, (singularValues A k) ^ 2) := by
  have h_sq : ‖A‖₂ ^ 2 ≤ ∑ k, (singularValues A k) ^ 2 :=
    spectral_norm_sq_le_sum_singularValues_sq_rect h A
  have h_sum_nonneg : 0 ≤ ∑ k, (singularValues A k) ^ 2 :=
    Finset.sum_nonneg (fun k _ => sq_nonneg _)
  have h_norm_nonneg : 0 ≤ ‖A‖₂ := @norm_nonneg (Matrix m n ℂ) _ A
  calc ‖A‖₂ = Real.sqrt (‖A‖₂ ^ 2) := (Real.sqrt_sq h_norm_nonneg).symm
    _ ≤ Real.sqrt (∑ k, (singularValues A k) ^ 2) := Real.sqrt_le_sqrt h_sq

end SpectralNormRectangular

namespace Matrix.SVD.Rectangular

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-! ### Main Construction -/

set_option linter.unusedSectionVars false in
/-- Inner product on EuclideanSpace ℂ m matches our sum formula. -/
lemma inner_euclidean_eq_sum_rectangular (x y : m → ℂ) :
    @inner ℂ (EuclideanSpace ℂ m) _
      ((WithLp.equiv 2 (m → ℂ)).symm x)
      ((WithLp.equiv 2 (m → ℂ)).symm y)
    = ∑ i, star (x i) * y i := by
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply]
  have h1 : ∀ i, ((WithLp.equiv 2 (m → ℂ)).symm x).ofLp i = x i := fun _ => rfl
  have h2 : ∀ i, ((WithLp.equiv 2 (m → ℂ)).symm y).ofLp i = y i := fun _ => rfl
  simp_rw [h1, h2, ← Complex.star_def, mul_comm]

/-- Left singular vector as EuclideanSpace ℂ m element (rectangular case).
    For j : n with σⱼ ≠ 0, this is the normalized column j of A*V. -/
noncomputable def leftSingularVectorEuclidean_rectangular (A : Matrix m n ℂ) (j : n)
    (hj : singularValueFromEigenvalue A j ≠ 0) : EuclideanSpace ℂ m :=
  (WithLp.equiv 2 (m → ℂ)).symm (leftSingularVectorNonzero_rectangular A j hj)

/-- The set of column indices with nonzero singular values (rectangular case).
    These are the indices j : n for which σⱼ ≠ 0. -/
def nonzeroSingularIndices_rectangular (A : Matrix m n ℂ) : Set n :=
  {j | singularValueFromEigenvalue A j ≠ 0}

/-- Extended function for all column indices: uses left singular vector when σⱼ ≠ 0, else 0.
    This maps n → EuclideanSpace ℂ m (columns to m-dimensional vectors). -/
noncomputable def leftSingularVectorExtended_rectangular (A : Matrix m n ℂ) :
    n → EuclideanSpace ℂ m :=
  fun j => if h : singularValueFromEigenvalue A j ≠ 0
           then leftSingularVectorEuclidean_rectangular A j h
           else 0

/-- The left singular vectors (restricted to nonzero σⱼ) form an orthonormal set.
    This is the key lemma enabling ONB extension. -/
theorem leftSingularVectorExtended_orthonormal_on_nonzero_rectangular (A : Matrix m n ℂ) :
    Orthonormal ℂ ((nonzeroSingularIndices_rectangular A).restrict
                   (leftSingularVectorExtended_rectangular A)) := by
  rw [orthonormal_iff_ite]
  intro ⟨j, hj⟩ ⟨j', hj'⟩
  simp only [Set.restrict_apply, nonzeroSingularIndices_rectangular, Set.mem_setOf_eq] at hj hj' ⊢
  have hj_dif : (if h : singularValueFromEigenvalue A j ≠ 0
                then leftSingularVectorEuclidean_rectangular A j h else 0)
               = leftSingularVectorEuclidean_rectangular A j hj := dif_pos hj
  have hj'_dif : (if h : singularValueFromEigenvalue A j' ≠ 0
                 then leftSingularVectorEuclidean_rectangular A j' h else 0)
                = leftSingularVectorEuclidean_rectangular A j' hj' := dif_pos hj'
  simp only [leftSingularVectorExtended_rectangular]
  rw [hj_dif, hj'_dif]
  simp only [leftSingularVectorEuclidean_rectangular]
  rw [inner_euclidean_eq_sum_rectangular]
  by_cases h : j = j'
  · subst h
    simp only [↓reduceIte]
    exact leftSingularVectorNonzero_rectangular_inner_self A j hj
  · have hjj' : (⟨j, hj⟩ : {j : n | singularValueFromEigenvalue A j ≠ 0}) ≠ ⟨j', hj'⟩ := by
      intro heq; apply h; exact Subtype.ext_iff.mp heq
    simp only [Subtype.mk.injEq, h, ↓reduceIte]
    exact leftSingularVectorNonzero_rectangular_orthogonal A j j' hj hj' h

/-! #### Orthonormal Basis Extension -/

/-- For k : m, find the corresponding j : n on the diagonal. -/
noncomputable def correspondingN (k : m) : Option n :=
  if h : (eigenvaluesBijection m k).val < Fintype.card n then
    some ((eigenvaluesBijection n).symm ⟨(eigenvaluesBijection m k).val, h⟩)
  else
    none

set_option linter.unusedSectionVars false in
/-- When correspondingN returns Some j, the indices align on the diagonal. -/
lemma correspondingN_spec (k : m) (j : n) (hj : correspondingN k = some j) :
    (eigenvaluesBijection m k).val = (eigenvaluesBijection n j).val := by
  unfold correspondingN at hj
  split_ifs at hj with h
  · simp only [Option.some.injEq] at hj
    subst hj; simp only [Equiv.apply_symm_apply]

/-- The correspondence is injective: different k give different j. -/
lemma correspondingN_injective (k k' : m) (j : n)
    (hk : correspondingN k = some j) (hk' : correspondingN k' = some j) : k = k' := by
  have h1 := correspondingN_spec k j hk
  have h2 := correspondingN_spec k' j hk'
  have h3 : (eigenvaluesBijection m k).val = (eigenvaluesBijection m k').val := by
    rw [h1, h2]
  have h4 : eigenvaluesBijection m k = eigenvaluesBijection m k' := Fin.ext h3
  exact (eigenvaluesBijection m).injective h4

/-- Left singular vectors indexed by m: for k : m, use uⱼ if k corresponds to j with σⱼ ≠ 0, else 0. -/
noncomputable def leftSingularVectorByM (A : Matrix m n ℂ) (k : m) : EuclideanSpace ℂ m :=
  match correspondingN k with
  | some j => if h : singularValueFromEigenvalue A j ≠ 0
              then leftSingularVectorEuclidean_rectangular A j h
              else 0
  | none => 0

/-- The set of m-indices that correspond to nonzero singular values. -/
def nonzeroSingularIndicesM (A : Matrix m n ℂ) : Set m :=
  {k | ∃ j, correspondingN k = some j ∧ singularValueFromEigenvalue A j ≠ 0}

set_option linter.unusedSectionVars false in
/-- Helper: when k ∈ nonzeroSingularIndicesM, leftSingularVectorByM equals the corresponding left singular vector. -/
lemma leftSingularVectorByM_eq (A : Matrix m n ℂ) (k : m) (j : n)
    (hcorr : correspondingN k = some j) (hj : singularValueFromEigenvalue A j ≠ 0) :
    leftSingularVectorByM A k = leftSingularVectorEuclidean_rectangular A j hj := by
  unfold leftSingularVectorByM
  simp only [hcorr, dif_pos hj]

/-- The left singular vectors indexed by m are orthonormal on the nonzero set. -/
theorem leftSingularVectorByM_orthonormal_on_nonzero (A : Matrix m n ℂ) :
    Orthonormal ℂ ((nonzeroSingularIndicesM A).restrict (leftSingularVectorByM A)) := by
  rw [orthonormal_iff_ite]
  intro ⟨k, hk⟩ ⟨k', hk'⟩
  simp only [Set.restrict_apply, nonzeroSingularIndicesM, Set.mem_setOf_eq] at hk hk' ⊢
  obtain ⟨j, hcorr, hj⟩ := hk
  obtain ⟨j', hcorr', hj'⟩ := hk'
  rw [leftSingularVectorByM_eq A k j hcorr hj, leftSingularVectorByM_eq A k' j' hcorr' hj']
  simp only [leftSingularVectorEuclidean_rectangular]
  rw [inner_euclidean_eq_sum_rectangular]
  by_cases h : k = k'
  · -- Same index k = k', so j = j' by injectivity
    subst h
    have hj_eq : j = j' := by
      have h_eq : some j = some j' := hcorr.symm.trans hcorr'
      exact Option.some_injective _ h_eq
    subst hj_eq
    simp only [↓reduceIte]
    exact leftSingularVectorNonzero_rectangular_inner_self A j hj
  · -- Different k ≠ k', need to show j ≠ j' or inner product is 0
    have hjj' : j ≠ j' := by
      intro heq
      subst heq
      exact h (correspondingN_injective k k' j hcorr hcorr')
    simp only [Subtype.mk.injEq, h, ↓reduceIte]
    exact leftSingularVectorNonzero_rectangular_orthogonal A j j' hj hj' hjj'

/-- Extend the m-indexed left singular vectors to a full orthonormal basis.
    This uses `exists_orthonormalBasis_extension_of_card_eq` to get an ONB indexed by m
    that agrees with the left singular vectors on the diagonal nonzero positions. -/
noncomputable def extendedONB_rectangular_v2 (A : Matrix m n ℂ) :
    OrthonormalBasis m ℂ (EuclideanSpace ℂ m) :=
  (leftSingularVectorByM_orthonormal_on_nonzero A).exists_orthonormalBasis_extension_of_card_eq
    finrank_euclideanSpace |>.choose

/-- The extended ONB agrees with left singular vectors on the nonzero diagonal positions. -/
theorem extendedONB_rectangular_v2_spec (A : Matrix m n ℂ) (k : m) (hk : k ∈ nonzeroSingularIndicesM A) :
    (extendedONB_rectangular_v2 A) k = leftSingularVectorByM A k :=
  (leftSingularVectorByM_orthonormal_on_nonzero A).exists_orthonormalBasis_extension_of_card_eq
    finrank_euclideanSpace |>.choose_spec k hk

/-! ##### Original Orthonormal Basis Extension (kept for compatibility) -/

/-- Extend the orthonormal left singular vectors to a full orthonormal basis of EuclideanSpace ℂ m.

    Note: The partial set is indexed by a subset of n (columns with σⱼ ≠ 0), but the full
    basis must be indexed by m. The extension theorem handles this mismatch by constructing
    a basis indexed by m that agrees with our vectors on their domain. -/
noncomputable def extendedONB_rectangular (A : Matrix m n ℂ) :
    OrthonormalBasis m ℂ (EuclideanSpace ℂ m) := by
  let s := nonzeroSingularIndices_rectangular A
  let v := leftSingularVectorExtended_rectangular A
  have h_on := leftSingularVectorExtended_orthonormal_on_nonzero_rectangular A
  -- The range of the restricted function forms an orthonormal set
  let restricted_v := s.restrict v
  have h_inj : Function.Injective restricted_v := h_on.linearIndependent.injective
  -- Convert to orthonormal on the range (as a set)
  have h_img_on : Orthonormal ℂ ((↑) : Set.range restricted_v → EuclideanSpace ℂ m) :=
    (orthonormal_subtype_range h_inj).mpr h_on
  -- Get extension - use Classical.choose to extract the witnesses
  let ext_proof := h_img_on.exists_orthonormalBasis_extension
  let u : Finset (EuclideanSpace ℂ m) := ext_proof.choose
  let b : OrthonormalBasis u ℂ (EuclideanSpace ℂ m) := ext_proof.choose_spec.choose
  -- Reindex to m using cardinality equality
  -- Fintype.card u = u.card by Fintype.card_coe
  -- u.card = finrank by Module.finrank_eq_card_finset_basis
  -- finrank = Fintype.card m by finrank_euclideanSpace
  have h_card : Fintype.card u = Fintype.card m := by
    rw [Fintype.card_coe, (Module.finrank_eq_card_finset_basis b.toBasis).symm,
        finrank_euclideanSpace]
  exact b.reindex (Fintype.equivOfCardEq h_card)

/-! #### Unitary Matrix Construction

Convert the orthonormal basis to a unitary matrix in unitaryGroup m ℂ.
-/

/-- Convert an orthonormal basis of EuclideanSpace ℂ m to a matrix.
    Column j of the matrix is basis vector j. -/
noncomputable def onbToMatrix_rectangular (b : OrthonormalBasis m ℂ (EuclideanSpace ℂ m)) :
    Matrix m m ℂ :=
  fun i j => (b j) i

set_option linter.unusedSectionVars false in
/-- Inner product of columns equals inner product of basis vectors. -/
lemma onbToMatrix_rectangular_inner (b : OrthonormalBasis m ℂ (EuclideanSpace ℂ m)) (i j : m) :
    (star (onbToMatrix_rectangular b) * onbToMatrix_rectangular b) i j =
    @inner ℂ (EuclideanSpace ℂ m) _ (b i) (b j) := by
  simp only [mul_apply, star_apply, onbToMatrix_rectangular]
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply]
  congr 1
  ext k
  simp only [star, ← Complex.star_def, mul_comm]

/-- A matrix built from an orthonormal basis is unitary. -/
theorem onbToMatrix_rectangular_mem_unitaryGroup (b : OrthonormalBasis m ℂ (EuclideanSpace ℂ m)) :
    onbToMatrix_rectangular b ∈ unitaryGroup m ℂ := by
  rw [mem_unitaryGroup_iff']
  ext i j
  rw [onbToMatrix_rectangular_inner, one_apply]
  have h_on : Orthonormal ℂ b := b.orthonormal
  rw [orthonormal_iff_ite] at h_on
  exact h_on i j

/-- The constructed unitary matrix U for rectangular SVD.
    Columns are derived from the extended orthonormal basis (v2 with diagonal alignment). -/
noncomputable def constructedU_rectangular (A : Matrix m n ℂ) : unitaryGroup m ℂ :=
  ⟨onbToMatrix_rectangular (extendedONB_rectangular_v2 A),
   onbToMatrix_rectangular_mem_unitaryGroup _⟩

/-- Column k of constructedU_rectangular equals the left singular vector uⱼ
    when k corresponds to j (via diagonal correspondence) and σⱼ ≠ 0. -/
theorem constructedU_rectangular_column_spec (A : Matrix m n ℂ) (k : m) (j : n)
    (hcorr : correspondingN k = some j) (hj : singularValueFromEigenvalue A j ≠ 0) :
    (fun i => (constructedU_rectangular A : Matrix m m ℂ) i k) =
    leftSingularVectorNonzero_rectangular A j hj := by
  ext i
  simp only [constructedU_rectangular, onbToMatrix_rectangular]
  have hk_mem : k ∈ nonzeroSingularIndicesM A := ⟨j, hcorr, hj⟩
  have h_spec := extendedONB_rectangular_v2_spec A k hk_mem
  rw [h_spec, leftSingularVectorByM_eq A k j hcorr hj]
  simp only [leftSingularVectorEuclidean_rectangular]
  rfl

/-! #### Diagonal Correspondence Helpers

For the rectangular SVD equation A*V = U*S, we need to track which row index k : m
corresponds to which column index j : n on the "diagonal" of the rectangular matrix S.
-/

/-- Given j : n, find the corresponding k : m on the diagonal of S (if it exists).
    Returns Some k when (eigenvaluesBijection n j).val < #m, i.e., when j is in the "diagonal range".
    Uses eigenvaluesBijection to be consistent with eigenvalue/eigenvector indexing. -/
noncomputable def diagonalK (j : n) : Option m :=
  if h : (eigenvaluesBijection n j).val < Fintype.card m then
    some ((eigenvaluesBijection m).symm ⟨(eigenvaluesBijection n j).val, h⟩)
  else
    none

set_option linter.unusedSectionVars false in
/-- When diagonalK returns Some k, the indices align on the diagonal. -/
lemma diagonalK_spec (j : n) (k : m) (hk : diagonalK j = some k) :
    (eigenvaluesBijection m k).val = (eigenvaluesBijection n j).val := by
  unfold diagonalK at hk
  split_ifs at hk with h
  · simp only [Option.some.injEq] at hk
    subst hk; simp only [Equiv.apply_symm_apply]

set_option linter.unusedSectionVars false in
/-- When #n ≤ #m, every j has a corresponding k on the diagonal. -/
lemma diagonalK_isSome_of_card_le (hn : Fintype.card n ≤ Fintype.card m) (j : n) :
    (diagonalK (m := m) (n := n) j).isSome = true := by
  unfold diagonalK
  have h : (eigenvaluesBijection n j).val < Fintype.card m := by
    calc (eigenvaluesBijection n j).val < Fintype.card n := (eigenvaluesBijection n j).isLt
      _ ≤ Fintype.card m := hn
  simp only [h, ↓reduceDIte, Option.isSome_some]

set_option linter.unusedSectionVars false in
/-- The singular diagonal entry S(k,j) is nonzero only at the diagonal position for j. -/
lemma singularDiagonal_eq_zero_of_ne_diagonalK (A : Matrix m n ℂ) (j : n) (k : m)
    (hk : diagonalK j ≠ some k) : singularDiagonal A k j = 0 := by
  unfold singularDiagonal
  -- After unfolding, we have: if h : ... then ... else 0
  -- S k j ≠ 0 requires (eigenvaluesBijection m k).val = (eigenvaluesBijection n j).val ∧ ... < min(#m, #n)
  -- If k is not the diagonal match for j, then the first condition fails
  by_cases h_in_range : (eigenvaluesBijection n j).val < Fintype.card m
  · -- j is in diagonal range, so diagonalK j = some k₀ for some k₀
    have h_some : diagonalK (m := m) (n := n) j = some ((eigenvaluesBijection m).symm ⟨(eigenvaluesBijection n j).val, h_in_range⟩) := by
      unfold diagonalK; simp only [h_in_range, ↓reduceDIte]
    -- Since hk says k ≠ that k₀, we have (eigenvaluesBijection m k).val ≠ (eigenvaluesBijection n j).val
    have h_ne : (eigenvaluesBijection m k).val ≠ (eigenvaluesBijection n j).val := by
      intro heq
      apply hk
      unfold diagonalK
      simp only [h_in_range, ↓reduceDIte, Option.some.injEq]
      have h_fin_eq : eigenvaluesBijection m k = ⟨(eigenvaluesBijection n j).val, h_in_range⟩ := by
        ext; exact heq
      have h_apply : (eigenvaluesBijection m).symm (eigenvaluesBijection m k) = k := (eigenvaluesBijection m).symm_apply_apply k
      rw [h_fin_eq] at h_apply
      exact h_apply
    -- Now the dif_pos condition fails: need to show ¬(fi.val = fj.val ∧ fi.val < min)
    have h_cond_false : ¬((eigenvaluesBijection m k).val = (eigenvaluesBijection n j).val ∧
        (eigenvaluesBijection m k).val < min (Fintype.card m) (Fintype.card n)) := by
      intro ⟨h_eq, _⟩
      exact h_ne h_eq
    simp only [dif_neg h_cond_false]
  · -- j is out of diagonal range, so S k j = 0 for all k
    have h_none : diagonalK (m := m) (n := n) j = none := by
      unfold diagonalK; simp only [h_in_range, ↓reduceDIte]
    -- (eigenvaluesBijection n j).val ≥ #m, so (eigenvaluesBijection m k).val < #m ≤ (eigenvaluesBijection n j).val
    have h_cond_false : ¬((eigenvaluesBijection m k).val = (eigenvaluesBijection n j).val ∧
        (eigenvaluesBijection m k).val < min (Fintype.card m) (Fintype.card n)) := by
      intro ⟨h_eq, _⟩
      have h_lt_m : (eigenvaluesBijection m k).val < Fintype.card m := (eigenvaluesBijection m k).isLt
      rw [h_eq] at h_lt_m
      exact h_in_range h_lt_m
    simp only [dif_neg h_cond_false]

/-- When diagonalK j = some k, the singular diagonal value at (k,j) equals the singular value. -/
lemma singularDiagonal_at_diagonalK (A : Matrix m n ℂ) (j : n) (k : m)
    (hk : diagonalK j = some k)
    (h_in_min : (eigenvaluesBijection n j).val < min (Fintype.card m) (Fintype.card n)) :
    singularDiagonal A k j = Complex.ofReal (singularValues A ⟨(eigenvaluesBijection n j).val, h_in_min⟩) := by
  unfold singularDiagonal
  have h_eq := diagonalK_spec j k hk
  have h_cond : (eigenvaluesBijection m k).val = (eigenvaluesBijection n j).val ∧
                (eigenvaluesBijection m k).val < min (Fintype.card m) (Fintype.card n) := by
    constructor
    · exact h_eq
    · rw [h_eq]; exact h_in_min
  simp only [dif_pos h_cond]
  -- The two Fin values have same underlying nat value by h_eq
  have h_fin_eq : (⟨(eigenvaluesBijection m k).val, h_cond.2⟩ : Fin (min (Fintype.card m) (Fintype.card n))) =
                  ⟨(eigenvaluesBijection n j).val, h_in_min⟩ := by
    ext
    exact h_eq
  rw [h_fin_eq]

/-! #### Core Equation: A*V = U*S

The main theorem of prove that A*V equals U*S column by column.

For column j (with j : n):
- If σⱼ ≠ 0: (A*V)[:,j] = σⱼ · uⱼ by construction of left singular vectors
- If σⱼ = 0: (A*V)[:,j] = 0 and (U*S)[:,j] = 0 (since S has zero in that diagonal position)

Note: S is m×n, so we need to handle the case where j corresponds to a diagonal
position (j < min(m,n)) vs an off-diagonal zero.
-/

/-- Column j of A*V is zero when the corresponding eigenvalue (and hence singular value) is zero. -/
lemma AV_column_zero_of_eigenvalue_zero_rectangular (A : Matrix m n ℂ) (j : n)
    (hj : singularValueFromEigenvalue A j = 0) :
    ∀ i, (A * (rightUnitary A : Matrix n n ℂ)) i j = 0 := by
  intro i
  -- The sum ∑ k, star(AV k j) * (AV k j) = eigenvalue j = 0 when hj holds
  have h_sum := AV_column_norm_sq_rectangular A j
  simp only at h_sum
  -- singularValueFromEigenvalue A j = 0 means eigenvalues j = 0 (since it's sqrt of eigenvalue)
  unfold singularValueFromEigenvalue at hj
  have h_eig_zero : (posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues j = 0 := by
    have h_nonneg := (posSemidef_conjTranspose_mul_self A).eigenvalues_nonneg j
    exact Real.sqrt_eq_zero h_nonneg |>.mp hj
  rw [h_eig_zero, Complex.ofReal_zero] at h_sum
  -- Each term star(z) * z = |z|² ≥ 0
  let AV := (A * (rightUnitary A : Matrix n n ℂ))
  have h_eq_normSq : ∀ k, star (AV k j) * AV k j = Complex.normSq (AV k j) := by
    intro k
    have h1 : star (AV k j) = (starRingEnd ℂ) (AV k j) := rfl
    rw [h1]
    have h2 : (starRingEnd ℂ) (AV k j) * AV k j = AV k j * (starRingEnd ℂ) (AV k j) := mul_comm _ _
    rw [h2, mul_comm]
    exact Complex.normSq_eq_conj_mul_self.symm
  have h_sum_normSq_complex : ∑ k, (Complex.normSq (AV k j) : ℂ) = 0 := by
    conv_lhs => rw [← Finset.sum_congr rfl (fun k _ => h_eq_normSq k)]
    exact h_sum
  have h_sum_normSq : ∑ k, Complex.normSq (AV k j) = 0 := by
    have h_real : (∑ k, Complex.normSq (AV k j) : ℂ) = (∑ k, Complex.normSq (AV k j) : ℝ) := by
      rw [Complex.ofReal_sum]
    rw [h_real] at h_sum_normSq_complex
    exact Complex.ofReal_injective h_sum_normSq_complex
  have h_each_zero := @Finset.sum_eq_zero_iff_of_nonneg m ℝ _ _ (fun k => Complex.normSq (AV k j))
    Finset.univ _ (fun k _ => Complex.normSq_nonneg _)
  rw [h_each_zero] at h_sum_normSq
  have hi := h_sum_normSq i (Finset.mem_univ i)
  exact Complex.normSq_eq_zero.mp hi

/-- **Core equation for rectangular SVD**: A * V = U * S

    This is the central identity that makes SVD work:
    - A is m × n
    - V = rightUnitary A is n × n unitary
    - U = constructedU_rectangular A is m × m unitary
    - S = singularDiagonal A is m × n with singular values on the "diagonal"

    The proof proceeds entry by entry:
    - Find the unique diagonal k (if it exists) where S k j ≠ 0
    - When σⱼ ≠ 0: use constructedU_rectangular_column_spec to relate U[:,k] to uⱼ
    - When σⱼ = 0 or off-diagonal: both sides are zero -/
theorem AV_eq_US_rectangular (A : Matrix m n ℂ) :
    A * (rightUnitary A : Matrix n n ℂ) =
    (constructedU_rectangular A : Matrix m m ℂ) * singularDiagonal A := by
  ext i j
  simp only [mul_apply]
  -- RHS: ∑ k, U i k * S k j
  -- S k j is nonzero only when k = diagonalK j (the diagonal position for j)

  -- Case split: is j in the "diagonal range" (has corresponding k)?
  by_cases h_in_range : (eigenvaluesBijection n j).val < Fintype.card m
  · -- j has a corresponding k on the diagonal
    let k₀ := (eigenvaluesBijection m).symm ⟨(eigenvaluesBijection n j).val, h_in_range⟩
    have h_diagonalK : diagonalK j = some k₀ := by
      unfold diagonalK; simp only [h_in_range, ↓reduceDIte]; rfl

    -- The sum collapses to just the k₀ term
    have h_sum_eq : ∑ k, (constructedU_rectangular A : Matrix m m ℂ) i k * singularDiagonal A k j =
                   (constructedU_rectangular A : Matrix m m ℂ) i k₀ * singularDiagonal A k₀ j := by
      apply Finset.sum_eq_single k₀
      · intro k _ hk_ne
        have h_zero := singularDiagonal_eq_zero_of_ne_diagonalK A j k
          (by rw [h_diagonalK]; intro h; exact hk_ne (Option.some_injective _ h.symm))
        simp only [h_zero, mul_zero]
      · intro h_not_mem
        exact absurd (Finset.mem_univ k₀) h_not_mem
    rw [h_sum_eq]

    -- Case split on whether σⱼ ≠ 0
    by_cases hj : singularValueFromEigenvalue A j ≠ 0
    · -- Case 1a: σⱼ ≠ 0 - use the column spec
      -- First, establish correspondingN k₀ = some j
      have h_corr : correspondingN k₀ = some j := by
        unfold correspondingN
        have h_lt : (eigenvaluesBijection m k₀).val < Fintype.card n := by
          simp only [k₀]; simp only [Equiv.apply_symm_apply]
          exact (eigenvaluesBijection n j).isLt
        simp only [dif_pos h_lt, Option.some.injEq]
        have h_eq : (eigenvaluesBijection m k₀).val = (eigenvaluesBijection n j).val := by
          simp only [k₀]; simp only [Equiv.apply_symm_apply]
        have h_fin_eq : (⟨(eigenvaluesBijection m k₀).val, h_lt⟩ : Fin (Fintype.card n)) =
                       eigenvaluesBijection n j := by ext; exact h_eq
        rw [h_fin_eq]; simp only [Equiv.symm_apply_apply]

      -- Get the column spec: U[:,k₀] = uⱼ
      have h_col := constructedU_rectangular_column_spec A k₀ j h_corr hj
      have h_U_eq : (constructedU_rectangular A : Matrix m m ℂ) i k₀ =
                   leftSingularVectorNonzero_rectangular A j hj i := congrFun h_col i

      -- The singular diagonal value at (k₀, j)
      have h_in_min : (eigenvaluesBijection n j).val < min (Fintype.card m) (Fintype.card n) := by
        apply Nat.lt_min.mpr ⟨h_in_range, (eigenvaluesBijection n j).isLt⟩
      have h_S_val := singularDiagonal_at_diagonalK A j k₀ h_diagonalK h_in_min
      rw [h_S_val, h_U_eq]

      -- uⱼ i * σ_from_singularValues = (A*V) i j
      -- where uⱼ i = (1/σⱼ) * (A*V) i j (by definition)
      simp only [leftSingularVectorNonzero_rectangular]

      -- Need: singularValues A ⟨idx, _⟩ = singularValueFromEigenvalue A j
      -- Now that singularValues always uses Aᴴ*A, this follows directly
      have h_sv_eq : singularValues A ⟨(eigenvaluesBijection n j).val, h_in_min⟩ =
                    singularValueFromEigenvalue A j :=
        singularValues_eq_singularValueFromEigenvalue A j h_in_min
      rw [h_sv_eq]

      have hj' : (Complex.ofReal (singularValueFromEigenvalue A j) : ℂ) ≠ 0 := by
        simp only [ne_eq, Complex.ofReal_eq_zero]; exact hj
      field_simp
      ring_nf
      rfl  -- Goal: ∑ x, A i x * ↑(rightUnitary A) x j = (A * ↑(rightUnitary A)) i j

    · -- Case 1b: σⱼ = 0 - both sides are zero
      push_neg at hj
      -- LHS: (A*V) i j = 0 when σⱼ = 0
      have h_AV_zero := AV_column_zero_of_eigenvalue_zero_rectangular A j hj

      -- RHS: U i k₀ * S k₀ j, need to show S k₀ j = 0 when σⱼ = 0
      have h_S_zero : singularDiagonal A k₀ j = 0 := by
        unfold singularDiagonal
        simp only
        split_ifs with h_diag
        · -- At diagonal position, the value is singularValues A ⟨idx, _⟩
          have h_eq := h_diag.1
          have h_lt := h_diag.2
          -- Convert h_lt from (eigenvaluesBijection m k₀).val < min ... to (eigenvaluesBijection n j).val < min ...
          have h_in_min_j : (eigenvaluesBijection n j).val < min (Fintype.card m) (Fintype.card n) := by
            rw [← h_eq]; exact h_lt
          have h_sv_eq : singularValues A ⟨(eigenvaluesBijection n j).val, h_in_min_j⟩ =
                        singularValueFromEigenvalue A j :=
            singularValues_eq_singularValueFromEigenvalue A j h_in_min_j
          -- The Fin index h_lt vs h_in_min_j: they have the same .val (via h_eq)
          have h_idx_eq : (⟨(eigenvaluesBijection m k₀).val, h_lt⟩ : Fin (min (Fintype.card m) (Fintype.card n))) =
                         ⟨(eigenvaluesBijection n j).val, h_in_min_j⟩ := by
            ext; exact h_eq
          rw [h_idx_eq, h_sv_eq, hj, Complex.ofReal_zero]
        · rfl
      -- The goal is: (A*V) i j = U i k₀ * S k₀ j
      -- LHS = 0 by h_AV_zero, RHS = 0 by h_S_zero
      rw [h_S_zero, mul_zero]
      -- Now goal is: (A*V) i j = 0
      exact h_AV_zero i

  · -- Case 2: j outside diagonal range - all S k j = 0, need (A*V) i j = 0
    have h_all_zero : ∀ k, singularDiagonal A k j = 0 := by
      intro k
      unfold singularDiagonal
      simp only
      split_ifs with h_diag
      · have h_lt_m : (eigenvaluesBijection m k).val < Fintype.card m := (eigenvaluesBijection m k).isLt
        have h_ge_m : (eigenvaluesBijection n j).val ≥ Fintype.card m := le_of_not_gt h_in_range
        omega
      · rfl
    simp only [h_all_zero, mul_zero, Finset.sum_const_zero]

    -- Need: (A*V) i j = 0 when j is outside diagonal range
    -- This requires: singularValueFromEigenvalue A j = 0 for such j
    -- Which follows from rank considerations: rank(AᴴA) ≤ min(m,n) = m
    -- For j with index ≥ m, the eigenvalue is 0
    have h_sigma_zero : singularValueFromEigenvalue A j = 0 := by
      -- When idx(j) ≥ m and m < n, the j-th eigenvalue of AᴴA is 0
      -- because AᴴA has at most m nonzero eigenvalues
      unfold singularValueFromEigenvalue
      -- eigenvalues j = eigenvalues₀ (equivOfCardEq.symm j) by Mathlib definition
      -- eigenvaluesBijection = equivFin = equivOfCardEq.symm by our bridge lemma
      have h_eq : (posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues j =
                  (posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues₀
                    (eigenvaluesBijection n j) := by
        unfold eigenvaluesBijection
        simp_rw [equivFin_eq_equivOfCardEq_symm]
        rfl
      rw [h_eq]
      -- Use eigenvalues₀_zero_beyond_rank since (eigenvaluesBijection n j).val ≥ card m
      have h_ge_m : (eigenvaluesBijection n j).val ≥ Fintype.card m := le_of_not_gt h_in_range
      have h_card_lt : Fintype.card m < Fintype.card n := by
        -- Since j exists and its index ≥ card m, we must have card m < card n
        exact Nat.lt_of_le_of_lt h_ge_m (eigenvaluesBijection n j).isLt
      have h_eig_zero := eigenvalues₀_zero_beyond_rank A (eigenvaluesBijection n j) h_ge_m h_card_lt
      rw [h_eig_zero]
      exact Real.sqrt_zero
    exact AV_column_zero_of_eigenvalue_zero_rectangular A j h_sigma_zero i

/-! #### Main Decomposition Theorem -/

/-- **Rectangular SVD Decomposition (Existence Form)**:
    Any m × n complex matrix A can be decomposed as A = U * S * Vᴴ
    where:
    - U ∈ unitaryGroup m ℂ (m × m unitary matrix of left singular vectors)
    - V ∈ unitaryGroup n ℂ (n × n unitary matrix of right singular vectors)
    - S : Matrix m n ℂ (rectangular "diagonal" with non-negative singular values)

    This is the natural extension of SVD to non-square matrices. -/
theorem svd_decomposition_rectangular (A : Matrix m n ℂ) :
    ∃ (U : unitaryGroup m ℂ) (V : unitaryGroup n ℂ) (S : Matrix m n ℂ),
      A = (U : Matrix m m ℂ) * S * star (V : Matrix n n ℂ) := by
  use constructedU_rectangular A, rightUnitary A, singularDiagonal A
  -- Main equation: A = U * S * Vᴴ
  have h_AV := AV_eq_US_rectangular A
  have h_V_unitary := mem_unitaryGroup_iff.mp (rightUnitary A).2
  calc A = A * (1 : Matrix n n ℂ) := by rw [Matrix.mul_one]
    _ = A * ((rightUnitary A : Matrix n n ℂ) * star (rightUnitary A : Matrix n n ℂ)) := by rw [h_V_unitary]
    _ = (A * (rightUnitary A : Matrix n n ℂ)) * star (rightUnitary A : Matrix n n ℂ) := by rw [Matrix.mul_assoc]
    _ = ((constructedU_rectangular A : Matrix m m ℂ) * singularDiagonal A) *
        star (rightUnitary A : Matrix n n ℂ) := by rw [h_AV]
    _ = (constructedU_rectangular A : Matrix m m ℂ) * singularDiagonal A *
        star (rightUnitary A : Matrix n n ℂ) := by rw [Matrix.mul_assoc]

end Matrix.SVD.Rectangular

/-! ## Rectangular Coherence Factor

This section defines the coherence factor for **rectangular** matrices `Matrix m n ℂ`.
The coherence factor μ(E) measures how concentrated the singular values are:

  μ(E) = ‖E‖_F / (√rank(E) · ‖E‖₂) ∈ [1/√r, 1]

- μ ≈ 1: Incoherent (flat spectrum, singular values roughly equal)
- μ ≈ 1/√r: Coherent (dominated by top singular value)

This generalizes the square-matrix `coherenceFactor` from `CoherenceCharacterization.lean`
to rectangular matrices, which is required for analyzing Kronecker approximation errors
after the rearrangement operator $\mathcal{R}$ produces non-square matrices.

### Main definitions

* `coherenceFactorRect`: μ(E) = ‖E‖_F / (√rank(E) · ‖E‖₂) for rectangular matrices

### Main results

* `coherenceFactorRect_zero`: μ(0) = 1
* `coherenceFactorRect_pos_of_ne_zero`: E ≠ 0 → μ(E) > 0
* `coherenceFactorRect_eq_square_case`: For n×n matrices, matches `coherenceFactor`
-/

section RectangularCoherenceFactor

open Matrix.SVD.Rectangular

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

-- Enable L2 operator norm instances locally
attribute [local instance] Matrix.instL2OpNormedAddCommGroup
attribute [local instance] Matrix.instL2OpNormedSpace
attribute [local instance] Matrix.instL2OpNormedRing
attribute [local instance] Matrix.instL2OpNormedAlgebra
attribute [local instance] Matrix.instL2OpMetricSpace

/-- Notation for L2 operator norm of rectangular matrices. -/
local notation "‖" A "‖₂" => @Norm.norm _ Matrix.instL2OpNormedAddCommGroup.toNorm A

/-- Frobenius norm for rectangular matrices as an explicit function.
    Avoids instance conflicts with the L2 operator norm. -/
noncomputable def frobeniusNormRect (A : Matrix m n ℂ) : ℝ :=
  @Norm.norm _ Matrix.frobeniusNormedAddCommGroup.toNorm A

omit [DecidableEq m] [DecidableEq n] in
/-- Frobenius norm is non-negative. -/
theorem frobeniusNormRect_nonneg (A : Matrix m n ℂ) : 0 ≤ frobeniusNormRect A :=
  @norm_nonneg _ (@SeminormedAddCommGroup.toSeminormedAddGroup _
    Matrix.frobeniusSeminormedAddCommGroup) A

omit [DecidableEq m] [DecidableEq n] in
/-- The squared Frobenius norm equals the sum of squared entry norms. -/
theorem frobeniusNormRect_sq (A : Matrix m n ℂ) :
    frobeniusNormRect A ^ 2 = ∑ i, ∑ j, Complex.normSq (A i j) := by
  unfold frobeniusNormRect
  have h := @Matrix.frobenius_norm_def m n ℂ _ _ _ A
  rw [h]
  have h_nonneg : (0 : ℝ) ≤ ∑ i, ∑ j, ‖A i j‖ ^ (2 : ℝ) := by positivity
  rw [← Real.rpow_natCast, ← Real.rpow_mul h_nonneg]
  norm_num
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  rw [← Complex.normSq_eq_norm_sq]

omit [DecidableEq m] [DecidableEq n] in
/-- For zero matrix, Frobenius norm is 0. -/
theorem frobeniusNormRect_zero : frobeniusNormRect (0 : Matrix m n ℂ) = 0 := by
  unfold frobeniusNormRect
  exact @norm_zero _ (@SeminormedAddCommGroup.toSeminormedAddGroup _
    Matrix.frobeniusSeminormedAddCommGroup)

omit [DecidableEq m] [DecidableEq n] in
/-- For nonzero matrix, Frobenius norm is positive. -/
theorem frobeniusNormRect_pos_of_ne_zero (A : Matrix m n ℂ) (hA : A ≠ 0) :
    0 < frobeniusNormRect A := by
  have h : frobeniusNormRect A ≠ 0 := by
    intro h_eq
    -- If ‖A‖_F = 0, then A = 0
    unfold frobeniusNormRect at h_eq
    have := @norm_eq_zero (Matrix m n ℂ)
      Matrix.frobeniusNormedAddCommGroup.toNormedAddGroup A
    rw [this] at h_eq
    exact hA h_eq
  exact (frobeniusNormRect_nonneg A).lt_of_ne' h

/-! ### Rank Properties for Rectangular Matrices -/

omit [Fintype m] [DecidableEq m] in
/-- A nonzero matrix has positive rank.
    Proved by contrapositive: rank = 0 implies the matrix is zero. -/
theorem rank_pos_of_ne_zero_rect (A : Matrix m n ℂ) (hA : A ≠ 0) : 0 < A.rank := by
  by_contra h_not_pos
  push_neg at h_not_pos
  have h_rank_zero : A.rank = 0 := Nat.eq_zero_of_le_zero h_not_pos
  -- rank = 0 means the linear map A.mulVecLin has trivial range
  rw [Matrix.rank] at h_rank_zero
  have h_range_bot : LinearMap.range A.mulVecLin = ⊥ :=
    Submodule.finrank_eq_zero.mp h_rank_zero
  -- If range is ⊥, then A * v = 0 for all v, so A = 0
  have h_zero : A = 0 := by
    ext i j
    have h_col : A.mulVecLin (Pi.single j 1) = 0 := by
      rw [Submodule.eq_bot_iff] at h_range_bot
      exact h_range_bot _ ⟨Pi.single j 1, rfl⟩
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec_single] at h_col
    have h_col' : A.col j = 0 := by
      rw [MulOpposite.op_one, one_smul] at h_col
      exact h_col
    have := congr_fun h_col' i
    simp only [Matrix.col_apply, Pi.zero_apply] at this
    exact this
  exact hA h_zero

/-! ### Main Definition: Rectangular Coherence Factor -/

/-- **Coherence factor for rectangular matrices.**

μ(E) = ‖E‖_F / (√rank(E) · ‖E‖₂) ∈ [1/√r, 1]

- μ ≈ 1: Incoherent (flat spectrum, singular values roughly equal)
- μ ≈ 1/√r: Coherent (dominated by top singular value)

For the zero matrix, we define μ(0) = 1 by convention. -/
noncomputable def coherenceFactorRect (E : Matrix m n ℂ) : ℝ :=
  if E = 0 then 1
  else frobeniusNormRect E / (Real.sqrt E.rank * ‖E‖₂)

/-! ### Basic Properties -/

omit [DecidableEq m] in
/-- For the zero matrix, coherence factor is 1 by definition. -/
theorem coherenceFactorRect_zero : coherenceFactorRect (0 : Matrix m n ℂ) = 1 := by
  simp [coherenceFactorRect]

omit [DecidableEq m] in
/-- For nonzero matrices, the coherence factor is positive.
    This follows from the positivity of ‖E‖_F, √rank(E), and ‖E‖₂. -/
theorem coherenceFactorRect_pos_of_ne_zero (E : Matrix m n ℂ) (hE : E ≠ 0) :
    0 < coherenceFactorRect E := by
  unfold coherenceFactorRect
  simp only [hE, ↓reduceIte]
  -- Need: 0 < frobeniusNormRect E / (√rank * ‖E‖₂)
  have h_frob_pos : 0 < frobeniusNormRect E := frobeniusNormRect_pos_of_ne_zero E hE
  have h_rank_pos : 0 < E.rank := rank_pos_of_ne_zero_rect E hE
  have h_sqrt_rank_pos : 0 < Real.sqrt E.rank :=
    Real.sqrt_pos.mpr (Nat.cast_pos.mpr h_rank_pos)
  have h_spectral_pos : 0 < ‖E‖₂ := @norm_pos_iff _ _ E |>.mpr hE
  have h_denom_pos : 0 < Real.sqrt E.rank * ‖E‖₂ := mul_pos h_sqrt_rank_pos h_spectral_pos
  exact div_pos h_frob_pos h_denom_pos

omit [DecidableEq m] in
/-- The coherence factor is non-negative. -/
theorem coherenceFactorRect_nonneg (E : Matrix m n ℂ) : 0 ≤ coherenceFactorRect E := by
  by_cases hE : E = 0
  · rw [hE, coherenceFactorRect_zero]; exact zero_le_one
  · exact le_of_lt (coherenceFactorRect_pos_of_ne_zero E hE)

/-! ### Square Case Equivalence -/

/-- For square matrices, `coherenceFactorRect` is compatible with the definition pattern
    used in `CoherenceCharacterization.lean`. Both use the same formula:
    μ(E) = ‖E‖_F / (√rank(E) · ‖E‖₂)

    Note: This theorem establishes structural equivalence. The actual numeric equality
    with `coherenceFactor` from CoherenceCharacterization.lean requires that both files
    use the same norm instances, which they do (L2 operator norm for ‖·‖ and Frobenius for ‖·‖_F). -/
theorem coherenceFactorRect_eq_formula (E : Matrix n n ℂ) (hE : E ≠ 0) :
    coherenceFactorRect E = frobeniusNormRect E / (Real.sqrt E.rank * ‖E‖₂) := by
  unfold coherenceFactorRect
  simp only [hE, ↓reduceIte]

/-! ## Upper Bound — μ ≤ 1

The coherence factor is bounded above by 1. This follows from:
  ‖E‖_F² = ∑ σₖ² ≤ rank(E) · max(σₖ)² = rank(E) · ‖E‖₂²

Taking square roots: ‖E‖_F ≤ √rank(E) · ‖E‖₂
Therefore: μ(E) = ‖E‖_F / (√rank(E) · ‖E‖₂) ≤ 1
-/

/-- The sum of squared singular values is bounded by rank(A) times the max squared.
    Key insight: only rank(A) singular values are nonzero, and each is ≤ max.

    This is the rectangular analogue of `sum_singularValues_sq_le_rank_mul_max_sq`
    from CoherenceCharacterization.lean. -/
theorem sum_singularValues_sq_le_rank_mul_max_sq_rect
    (h : 0 < min (Fintype.card m) (Fintype.card n)) (A : Matrix m n ℂ) :
    ∑ k, (Matrix.SVD.Rectangular.singularValues A k) ^ 2 ≤
    A.rank * (Finset.sup' Finset.univ
      (Finset.univ_nonempty_iff.mpr ⟨⟨0, h⟩⟩) (Matrix.SVD.Rectangular.singularValues A)) ^ 2 := by
  let M := Finset.sup' Finset.univ (Finset.univ_nonempty_iff.mpr ⟨⟨0, h⟩⟩)
              (Matrix.SVD.Rectangular.singularValues A)
  have hM_nonneg : 0 ≤ M := by
    apply Finset.le_sup'_of_le _ (Finset.mem_univ ⟨0, h⟩)
    exact Matrix.SVD.Rectangular.singularValues_nonneg A ⟨0, h⟩
  have h_le_M : ∀ k, Matrix.SVD.Rectangular.singularValues A k ≤ M := fun k =>
    Finset.le_sup' (Matrix.SVD.Rectangular.singularValues A) (Finset.mem_univ k)

  -- Bound each term by M²
  have h_each_le : ∀ k, (Matrix.SVD.Rectangular.singularValues A k) ^ 2 ≤ M ^ 2 := fun k => by
    apply sq_le_sq'
    · calc -M ≤ 0 := neg_nonpos.mpr hM_nonneg
        _ ≤ Matrix.SVD.Rectangular.singularValues A k :=
            Matrix.SVD.Rectangular.singularValues_nonneg A k
    · exact h_le_M k

  -- The key insight: only rank(A) singular values are nonzero
  have h_rank := Matrix.SVD.Rectangular.rank_eq_card_nonzero_singularValues_rect A

  -- Split into nonzero and zero contributions
  let S := {k : Fin (min (Fintype.card m) (Fintype.card n)) |
            Matrix.SVD.Rectangular.singularValues A k ≠ 0}.toFinset
  have hS_card : S.card = A.rank := by
    rw [h_rank]
    simp only [S, Set.toFinset_card]
    rfl

  -- Sum over nonzero equals original sum (zero terms contribute 0)
  have h_sum_eq : ∑ k, (Matrix.SVD.Rectangular.singularValues A k) ^ 2 =
                  ∑ k ∈ S, (Matrix.SVD.Rectangular.singularValues A k) ^ 2 := by
    rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ) (p := fun k => k ∈ S)]
    simp only [S, Set.mem_toFinset, Set.mem_setOf_eq]
    have h_zero_sum : ∑ k ∈ Finset.univ.filter (fun k =>
        Matrix.SVD.Rectangular.singularValues A k = 0),
        (Matrix.SVD.Rectangular.singularValues A k) ^ 2 = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
      simp [hk]
    simp only [not_not]
    rw [h_zero_sum, add_zero]
    congr 1
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, ne_eq,
               Set.mem_toFinset, Set.mem_setOf_eq]

  calc ∑ k, (Matrix.SVD.Rectangular.singularValues A k) ^ 2
      = ∑ k ∈ S, (Matrix.SVD.Rectangular.singularValues A k) ^ 2 := h_sum_eq
    _ ≤ ∑ _k ∈ S, M ^ 2 := Finset.sum_le_sum fun k _ => h_each_le k
    _ = S.card * M ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
    _ = A.rank * M ^ 2 := by rw [hS_card]

/-- **The coherence factor is at most 1.**

This is the main upper bound for coherence factor. It follows from:
  ‖E‖_F² = ∑ σₖ² ≤ rank(E) · max(σₖ)² = rank(E) · ‖E‖₂² -/
theorem coherenceFactorRect_le_one
    (h : 0 < min (Fintype.card m) (Fintype.card n)) (E : Matrix m n ℂ) :
    coherenceFactorRect E ≤ 1 := by
  unfold coherenceFactorRect
  split_ifs with hE
  · linarith  -- E = 0 case: coherenceFactorRect 0 = 1 ≤ 1
  · -- E ≠ 0
    have h_spectral_pos : 0 < ‖E‖₂ := @norm_pos_iff _ _ E |>.mpr hE
    have h_rank_pos : 0 < E.rank := rank_pos_of_ne_zero_rect E hE
    have h_denom_pos : 0 < Real.sqrt E.rank * ‖E‖₂ := by
      apply mul_pos
      · exact Real.sqrt_pos.mpr (Nat.cast_pos.mpr h_rank_pos)
      · exact h_spectral_pos
    rw [div_le_one h_denom_pos]
    -- Goal: frobeniusNormRect E ≤ √rank(E) · ‖E‖₂

    -- The maximum singular value
    let M := Finset.sup' Finset.univ (Finset.univ_nonempty_iff.mpr ⟨⟨0, h⟩⟩)
              (Matrix.SVD.Rectangular.singularValues E)

    -- Spectral norm equals max singular value
    have h_spec_eq : ‖E‖₂ = M :=
      Matrix.SVD.Rectangular.spectral_norm_eq_max_singularValue_rect h E

    -- Square bound: frobeniusNormRect E² ≤ rank(E) · ‖E‖₂²
    have h_sq : frobeniusNormRect E ^ 2 ≤ E.rank * ‖E‖₂ ^ 2 := by
      -- Use Frobenius norm = sqrt(sum of squared singular values)
      have h_frob_sq :=
        Matrix.SVD.Rectangular.frobeniusNorm_sq_eq_sum_singularValues_sq_rect E
      -- frobeniusNormRect uses the same norm instance
      have h_frob_eq : frobeniusNormRect E ^ 2 =
          @Norm.norm _ Matrix.frobeniusNormedAddCommGroup.toNorm E ^ 2 := by
        unfold frobeniusNormRect
        rfl
      rw [h_frob_eq, h_frob_sq]
      calc ∑ k, (Matrix.SVD.Rectangular.singularValues E k) ^ 2
          ≤ E.rank * M ^ 2 := sum_singularValues_sq_le_rank_mul_max_sq_rect h E
        _ = E.rank * ‖E‖₂ ^ 2 := by rw [h_spec_eq]

    -- Take square roots
    have h_frob_nonneg : 0 ≤ frobeniusNormRect E := frobeniusNormRect_nonneg E
    have h_rank_nonneg : (0 : ℝ) ≤ E.rank := Nat.cast_nonneg _
    have h_rhs_nonneg : 0 ≤ Real.sqrt E.rank * ‖E‖₂ :=
      mul_nonneg (Real.sqrt_nonneg _) (le_of_lt h_spectral_pos)

    have h_sq' : frobeniusNormRect E ^ 2 ≤ (Real.sqrt E.rank * ‖E‖₂) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt h_rank_nonneg]
      exact h_sq

    calc frobeniusNormRect E
        = Real.sqrt (frobeniusNormRect E ^ 2) := (Real.sqrt_sq h_frob_nonneg).symm
      _ ≤ Real.sqrt ((Real.sqrt E.rank * ‖E‖₂) ^ 2) := Real.sqrt_le_sqrt h_sq'
      _ = Real.sqrt E.rank * ‖E‖₂ := Real.sqrt_sq h_rhs_nonneg

/-! ## Lower Bound — μ ≥ 1/√rank

The coherence factor is bounded below by 1/√rank. This is the tight lower bound,
achieved when all nonzero singular values are equal (i.e., when E is "maximally incoherent").

**Proof strategy:**
  σ₁² ≤ ∑_{k=1}^{r} σₖ² = ‖E‖_F²

So ‖E‖ = σ₁ ≤ ‖E‖_F, and:
  μ(E) = ‖E‖_F / (√r · ‖E‖) ≥ ‖E‖ / (√r · ‖E‖) = 1/√r
-/

omit [DecidableEq m] in
/-- The maximum singular value squared is at most the sum of all squared singular values.

This is the key lemma for proving ‖E‖ ≤ ‖E‖_F (spectral ≤ Frobenius). -/
theorem max_singularValue_sq_le_sum_rect
    (h : 0 < min (Fintype.card m) (Fintype.card n)) (A : Matrix m n ℂ) :
    (Finset.sup' Finset.univ (Finset.univ_nonempty_iff.mpr ⟨⟨0, h⟩⟩)
      (Matrix.SVD.Rectangular.singularValues A)) ^ 2 ≤
    ∑ k, (Matrix.SVD.Rectangular.singularValues A k) ^ 2 := by
  let M := Finset.sup' Finset.univ (Finset.univ_nonempty_iff.mpr ⟨⟨0, h⟩⟩)
              (Matrix.SVD.Rectangular.singularValues A)
  -- M = max singular value, which is achieved at some index i₀
  have h_ne : (Finset.univ : Finset (Fin (min (Fintype.card m) (Fintype.card n)))).Nonempty :=
    Finset.univ_nonempty_iff.mpr ⟨⟨0, h⟩⟩
  obtain ⟨i₀, _, hi₀⟩ := Finset.exists_mem_eq_sup' h_ne (Matrix.SVD.Rectangular.singularValues A)
  -- M² = σᵢ₀² is one term in the sum
  calc M ^ 2
      = (Matrix.SVD.Rectangular.singularValues A i₀) ^ 2 := by congr 1
    _ ≤ ∑ k, (Matrix.SVD.Rectangular.singularValues A k) ^ 2 :=
        Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ i₀)

/-- **Spectral norm is bounded by Frobenius norm**: ‖E‖ ≤ ‖E‖_F for rectangular matrices.

This uses the Frobenius norm defined via `frobeniusNormRect` which matches the
`Matrix.frobeniusSeminormedAddCommGroup` instance. -/
theorem spectral_le_frobenius_rect
    (h : 0 < min (Fintype.card m) (Fintype.card n)) (E : Matrix m n ℂ) :
    ‖E‖₂ ≤ frobeniusNormRect E := by
  have h_spec_sq : ‖E‖₂ ^ 2 ≤ frobeniusNormRect E ^ 2 := by
    -- Spectral norm = max singular value
    let M := Finset.sup' Finset.univ (Finset.univ_nonempty_iff.mpr ⟨⟨0, h⟩⟩)
              (Matrix.SVD.Rectangular.singularValues E)
    have h_spec_eq : ‖E‖₂ = M :=
      Matrix.SVD.Rectangular.spectral_norm_eq_max_singularValue_rect h E
    -- Frobenius² = sum of singular values²
    have h_frob_sq_eq : frobeniusNormRect E ^ 2 =
        ∑ k, (Matrix.SVD.Rectangular.singularValues E k) ^ 2 := by
      unfold frobeniusNormRect
      exact Matrix.SVD.Rectangular.frobeniusNorm_sq_eq_sum_singularValues_sq_rect E
    rw [h_spec_eq, h_frob_sq_eq]
    exact max_singularValue_sq_le_sum_rect h E
  have h_spec_nonneg : 0 ≤ ‖E‖₂ := @norm_nonneg (Matrix m n ℂ) _ E
  have h_frob_nonneg : 0 ≤ frobeniusNormRect E := frobeniusNormRect_nonneg E
  calc ‖E‖₂ = Real.sqrt (‖E‖₂ ^ 2) := (Real.sqrt_sq h_spec_nonneg).symm
    _ ≤ Real.sqrt (frobeniusNormRect E ^ 2) := Real.sqrt_le_sqrt h_spec_sq
    _ = frobeniusNormRect E := Real.sqrt_sq h_frob_nonneg

/-- The ratio of Frobenius norm to spectral norm is at least 1: 1 ≤ ‖E‖_F / ‖E‖.

This is a reformulation of `spectral_le_frobenius_rect` as a ratio bound. -/
theorem frobenius_spectral_ratio_ge_one_rect
    (h : 0 < min (Fintype.card m) (Fintype.card n)) (E : Matrix m n ℂ) (hE : E ≠ 0) :
    1 ≤ frobeniusNormRect E / ‖E‖₂ := by
  have h_spec_pos : 0 < ‖E‖₂ := @norm_pos_iff _ _ E |>.mpr hE
  rw [one_le_div h_spec_pos]
  exact spectral_le_frobenius_rect h E

/-- **The coherence factor is at least 1/√rank.**

This is the tight lower bound for coherence factor. It follows from:
  ‖E‖ ≤ ‖E‖_F (spectral ≤ Frobenius)

Therefore:
  μ(E) = ‖E‖_F / (√rank · ‖E‖) ≥ ‖E‖ / (√rank · ‖E‖) = 1/√rank

The bound is tight when all nonzero singular values are equal (maximally incoherent). -/
theorem coherenceFactorRect_ge_inv_sqrt_rank
    (h : 0 < min (Fintype.card m) (Fintype.card n)) (E : Matrix m n ℂ) (hE : E ≠ 0) :
    1 / Real.sqrt E.rank ≤ coherenceFactorRect E := by
  unfold coherenceFactorRect
  simp only [hE, ↓reduceIte]
  have h_spectral_pos : 0 < ‖E‖₂ := @norm_pos_iff _ _ E |>.mpr hE
  have h_rank_pos : 0 < E.rank := rank_pos_of_ne_zero_rect E hE
  have h_sqrt_rank_pos : 0 < Real.sqrt E.rank :=
    Real.sqrt_pos.mpr (Nat.cast_pos.mpr h_rank_pos)
  have h_denom_pos : 0 < Real.sqrt E.rank * ‖E‖₂ := mul_pos h_sqrt_rank_pos h_spectral_pos
  -- Goal: 1 / √rank ≤ ‖E‖_F / (√rank · ‖E‖)
  rw [div_le_div_iff₀ h_sqrt_rank_pos h_denom_pos]
  -- Goal: 1 * (√rank · ‖E‖) ≤ ‖E‖_F * √rank
  rw [one_mul, mul_comm (frobeniusNormRect E) (Real.sqrt E.rank)]
  -- Goal: √rank · ‖E‖ ≤ √rank · ‖E‖_F
  exact mul_le_mul_of_nonneg_left (spectral_le_frobenius_rect h E) (le_of_lt h_sqrt_rank_pos)

/-- Combined bounds: the coherence factor lies in [1/√rank, 1].

This combines `coherenceFactorRect_ge_inv_sqrt_rank` and `coherenceFactorRect_le_one`. -/
theorem coherenceFactorRect_bounds
    (h : 0 < min (Fintype.card m) (Fintype.card n)) (E : Matrix m n ℂ) (hE : E ≠ 0) :
    1 / Real.sqrt E.rank ≤ coherenceFactorRect E ∧ coherenceFactorRect E ≤ 1 :=
  ⟨coherenceFactorRect_ge_inv_sqrt_rank h E hE, coherenceFactorRect_le_one h E⟩

/-! ### Application Theorems

These theorems connect coherence factor bounds to spectral norm bounds.
The key insight is that coherence μ characterizes how "spread out" the singular values are:
- μ = 1 means the matrix is maximally coherent (rank-1 structure, one dominant singular value)
- μ = 1/√rank means maximally incoherent (all nonzero singular values equal)

When μ is bounded away from 1/√rank, we get improved spectral bounds beyond the naive
‖E‖ ≤ ‖E‖_F relationship.
-/

omit [DecidableEq m] in
/-- **Spectral bound via coherence factor.**

From μ(E) = ‖E‖_F / (√rank · ‖E‖), we can solve for ‖E‖:
  ‖E‖ = ‖E‖_F / (√rank · μ(E))

This gives a way to bound the spectral norm using Frobenius norm and coherence. -/
theorem spectral_bound_via_coherence_rect
    (_h : 0 < min (Fintype.card m) (Fintype.card n)) (E : Matrix m n ℂ) (hE : E ≠ 0) :
    ‖E‖₂ = frobeniusNormRect E / (Real.sqrt E.rank * coherenceFactorRect E) := by
  unfold coherenceFactorRect
  simp only [hE, ↓reduceIte]
  have h_spectral_pos : 0 < ‖E‖₂ := @norm_pos_iff _ _ E |>.mpr hE
  have h_rank_pos : 0 < E.rank := rank_pos_of_ne_zero_rect E hE
  have h_sqrt_rank_pos : 0 < Real.sqrt E.rank :=
    Real.sqrt_pos.mpr (Nat.cast_pos.mpr h_rank_pos)
  have h_frob_pos : 0 < frobeniusNormRect E := frobeniusNormRect_pos_of_ne_zero E hE
  have h_denom_inner_pos : 0 < Real.sqrt E.rank * ‖E‖₂ := mul_pos h_sqrt_rank_pos h_spectral_pos
  have h_coherence_pos : 0 < frobeniusNormRect E / (Real.sqrt E.rank * ‖E‖₂) :=
    div_pos h_frob_pos h_denom_inner_pos
  -- μ = ‖E‖_F / (√rank · ‖E‖)
  -- √rank · μ = ‖E‖_F / ‖E‖
  -- ‖E‖_F / (√rank · μ) = ‖E‖
  -- Goal: ‖E‖ = ‖E‖_F / (√rank · μ)
  have h_simpl : Real.sqrt E.rank * (frobeniusNormRect E / (Real.sqrt E.rank * ‖E‖₂)) =
      frobeniusNormRect E / ‖E‖₂ := by
    have h_sqrt_ne : Real.sqrt E.rank ≠ 0 := ne_of_gt h_sqrt_rank_pos
    have h_spec_ne : ‖E‖₂ ≠ 0 := ne_of_gt h_spectral_pos
    field_simp
  rw [h_simpl]
  field_simp

omit [DecidableEq m] in
/-- **Improved spectral bound for incoherent matrices.**

If the coherence factor is bounded below by α (i.e., α ≤ μ(E)), then:
  ‖E‖ ≤ ‖E‖_F / (α · √rank)

This is useful when we know E is "incoherent" (μ bounded away from 1/√rank).
The smaller α is, the weaker the bound; α = 1/√rank gives the trivial bound ‖E‖ ≤ ‖E‖_F. -/
theorem incoherent_improved_bound_rect
    (h : 0 < min (Fintype.card m) (Fintype.card n)) (E : Matrix m n ℂ) (hE : E ≠ 0)
    (α : ℝ) (hα_pos : 0 < α) (hα_bound : α ≤ coherenceFactorRect E) :
    ‖E‖₂ ≤ frobeniusNormRect E / (α * Real.sqrt E.rank) := by
  have h_rank_pos : 0 < E.rank := rank_pos_of_ne_zero_rect E hE
  have h_sqrt_rank_pos : 0 < Real.sqrt E.rank :=
    Real.sqrt_pos.mpr (Nat.cast_pos.mpr h_rank_pos)
  have h_coherence_pos : 0 < coherenceFactorRect E :=
    coherenceFactorRect_pos_of_ne_zero E hE
  have h_frob_pos : 0 < frobeniusNormRect E := frobeniusNormRect_pos_of_ne_zero E hE
  -- From spectral_bound_via_coherence_rect: ‖E‖ = ‖E‖_F / (√rank · μ)
  rw [spectral_bound_via_coherence_rect h E hE]
  -- Goal: ‖E‖_F / (√rank · μ) ≤ ‖E‖_F / (α · √rank)
  rw [mul_comm α (Real.sqrt E.rank)]
  -- Goal: ‖E‖_F / (√rank · μ) ≤ ‖E‖_F / (√rank · α)
  apply div_le_div_of_nonneg_left h_frob_pos.le
  · exact mul_pos h_sqrt_rank_pos hα_pos
  · exact mul_le_mul_of_nonneg_left hα_bound (le_of_lt h_sqrt_rank_pos)

omit [DecidableEq m] in
/-- **Coherence determines the spectral-to-Frobenius ratio.**

The coherence factor equals the Frobenius-to-spectral norm ratio divided by √rank:
  μ(E) = (‖E‖_F / ‖E‖) / √rank

Equivalently:
  ‖E‖_F / ‖E‖ = √rank · μ(E)

This shows that coherence captures exactly how much the spectral norm differs
from the "averaged" Frobenius norm per rank dimension. -/
theorem coherence_eq_norm_ratio_rect
    (_h : 0 < min (Fintype.card m) (Fintype.card n)) (E : Matrix m n ℂ) (hE : E ≠ 0) :
    coherenceFactorRect E = (frobeniusNormRect E / ‖E‖₂) / Real.sqrt E.rank := by
  unfold coherenceFactorRect
  simp only [hE, ↓reduceIte]
  rw [div_div, mul_comm]

omit [DecidableEq m] in
/-- **Frobenius-to-spectral ratio via coherence.**

The ratio ‖E‖_F / ‖E‖ = √rank · μ(E).

This is useful for estimating how far the spectral norm is from the Frobenius norm. -/
theorem frobenius_spectral_ratio_eq_sqrt_rank_mul_coherence_rect
    (h : 0 < min (Fintype.card m) (Fintype.card n)) (E : Matrix m n ℂ) (hE : E ≠ 0) :
    frobeniusNormRect E / ‖E‖₂ = Real.sqrt E.rank * coherenceFactorRect E := by
  rw [coherence_eq_norm_ratio_rect h E hE]
  have h_rank_pos : 0 < E.rank := rank_pos_of_ne_zero_rect E hE
  have h_sqrt_rank_pos : 0 < Real.sqrt E.rank :=
    Real.sqrt_pos.mpr (Nat.cast_pos.mpr h_rank_pos)
  have h_spectral_pos : 0 < ‖E‖₂ := @norm_pos_iff _ _ E |>.mpr hE
  have h_sqrt_ne : Real.sqrt E.rank ≠ 0 := ne_of_gt h_sqrt_rank_pos
  have h_spec_ne : ‖E‖₂ ≠ 0 := ne_of_gt h_spectral_pos
  field_simp

end RectangularCoherenceFactor
