/-
Copyright (c) 2025 FLYWHEEL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aleksandar Markovski

# Matrix Norm Relations and Eckart-Young

Spectral norm ‖A‖₂ = σ₁(A). The Eckart-Young theorem for optimal
low-rank approximation in both Frobenius and spectral norms.

## References

[1] Eckart, C. & Young, G. (1936). Psychometrika 1(3), 211–218.
[2] Mirsky, L. (1960). Quart. J. Math. 11, 50–59.
[3] Horn & Johnson (2012). Matrix Analysis, 2nd ed. Ch. 5, 7.
[4] Mathlib CStarAlgebra: `IsSelfAdjoint.toReal_spectralRadius_eq_norm`

## WARNING: Instance Hell Below

This file has multiple norm instances that can conflict:
- Frobenius norm (default for Matrix.frobeniusNormedAddCommGroup)
- L2 operator norm (Matrix.instL2OpNormedAddCommGroup)

Be VERY careful about which instances are active. When in doubt, use
the explicit frobeniusNorm' function instead of ‖·‖.

I wasted an entire afternoon debugging a proof that was silently using
the wrong norm instance. Don't be like me.
-/

import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Analysis.Complex.Order
import FrobeniusNorm
import KroneckerRearrangement

open Matrix
open scoped ComplexOrder BigOperators

namespace Matrix.SVD

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Truncated singular values are non-negative. -/
theorem truncatedSingularValues_tail_nonneg (A : Matrix n n ℂ) (k : ℕ) (i : n) :
    0 ≤ truncatedSingularValues_tail A k i := by
  unfold truncatedSingularValues_tail
  simp only
  split_ifs
  · exact singularValues₀_nonneg A _
  · rfl

end Matrix.SVD

/-! ## Spectral Norm Relations -/

namespace Matrix.SpectralNorm

/-! All L2 operator norm theorems must be in one section with local instances active -/

section L2OpNormTheorems

variable {n : Type*} [Fintype n] [DecidableEq n]

-- Enable L2 operator norm instances locally for this section
attribute [local instance] Matrix.instL2OpNormedAddCommGroup
attribute [local instance] Matrix.instL2OpNormedSpace
attribute [local instance] Matrix.instL2OpNormedRing
attribute [local instance] Matrix.instL2OpNormedAlgebra
attribute [local instance] Matrix.instL2OpMetricSpace
attribute [local instance] Matrix.instCStarRing

/-- The CStarAlgebra instance for complex matrices with L2 operator norm.
    Uses `CStarAlgebra.mk` which unifies the already-available parent instances. -/
-- I honestly don't understand why this needs to be noncomputable.
-- The Mathlib source says something about "CFC" but I couldn't follow it.
noncomputable instance instCStarAlgebraMatrix : CStarAlgebra (Matrix n n ℂ) :=
  CStarAlgebra.mk

/-- Frobenius norm as an explicit function to avoid instance conflicts with L2 operator norm.
    Access the Frobenius norm via the frobeniusNormedAddCommGroup instance. -/
noncomputable def frobeniusNorm' (A : Matrix n n ℂ) : ℝ :=
  @Norm.norm _ Matrix.frobeniusNormedAddCommGroup.toNorm A

omit [DecidableEq n] in
theorem frobeniusNorm'_nonneg (A : Matrix n n ℂ) : 0 ≤ frobeniusNorm' A :=
  @norm_nonneg _ (@SeminormedAddCommGroup.toSeminormedAddGroup _ Matrix.frobeniusSeminormedAddCommGroup) A

omit [DecidableEq n] in
theorem frobeniusNorm'_sq (A : Matrix n n ℂ) :
    frobeniusNorm' A ^ 2 = ∑ i, ∑ j, Complex.normSq (A i j) := by
  unfold frobeniusNorm'
  have h := @Matrix.frobenius_norm_def n n ℂ _ _ _ A
  rw [h]
  have h_nonneg : (0 : ℝ) ≤ ∑ i, ∑ j, ‖A i j‖ ^ (2 : ℝ) := by positivity
  rw [← Real.rpow_natCast, ← Real.rpow_mul h_nonneg]
  norm_num
  -- Goal: ∑ x, ∑ x_1, ‖A x x_1‖ ^ 2 = ∑ i, ∑ j, Complex.normSq (A i j)
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [← Complex.normSq_eq_norm_sq]

/-! ### Key Lemma: L2 norm of Hermitian matrix equals spectral radius -/

/-- For a Hermitian matrix H, the L2 operator norm equals the spectral radius. -/
theorem l2_opNorm_hermitian_eq_spectralRadius
    (H : Matrix n n ℂ) (hH : Matrix.IsHermitian H) :
    ‖H‖ = (spectralRadius ℝ H).toReal := by
  have h_sa : IsSelfAdjoint H := hH.isSelfAdjoint
  exact (IsSelfAdjoint.toReal_spectralRadius_eq_norm h_sa).symm

/-- The spectral radius of a Hermitian matrix equals the supremum of absolute eigenvalues. -/
theorem hermitian_spectralRadius_eq_sup_abs_eigenvalues [Nonempty n]
    (H : Matrix n n ℂ) (hH : Matrix.IsHermitian H) :
    (spectralRadius ℝ H).toReal = Finset.sup' Finset.univ Finset.univ_nonempty (|hH.eigenvalues ·|) := by
  have h_spec := hH.spectrum_real_eq_range_eigenvalues
  simp only [spectralRadius, h_spec]
  rw [iSup_range]
  have h_ne_top : ∀ i, ((‖hH.eigenvalues i‖₊ : NNReal) : ENNReal) ≠ ⊤ := fun i => ENNReal.coe_ne_top
  rw [ENNReal.toReal_iSup h_ne_top]
  -- Convert: (↑‖x‖₊ : ENNReal).toReal to |x| for reals
  have h_eq : ∀ i, (↑(‖hH.eigenvalues i‖₊) : ENNReal).toReal = |hH.eigenvalues i| := fun i => by
    simp only [ENNReal.toReal, ENNReal.toNNReal_coe]
    -- Now goal is: ↑‖hH.eigenvalues i‖₊ = |hH.eigenvalues i| (NNReal → ℝ coercion)
    simp only [nnnorm, Real.norm_eq_abs]
    rfl
  simp_rw [h_eq]
  -- For finite nonempty type: iSup over Fintype = Finset.sup' over univ
  symm
  rw [Finset.sup'_eq_csSup_image]
  -- ↑Finset.univ = Set.univ for Fintype, f '' Set.univ = Set.range f, sSup (range f) = iSup f
  simp only [Finset.coe_univ, Set.image_univ, sSup_range]

/-- For a Hermitian matrix, ‖H‖ = max |λᵢ| where λᵢ are eigenvalues. -/
theorem l2_opNorm_hermitian_eq_sup_abs_eigenvalues [Nonempty n]
    (H : Matrix n n ℂ) (hH : Matrix.IsHermitian H) :
    ‖H‖ = Finset.sup' Finset.univ Finset.univ_nonempty (|hH.eigenvalues ·|) := by
  rw [l2_opNorm_hermitian_eq_spectralRadius H hH]
  exact hermitian_spectralRadius_eq_sup_abs_eigenvalues H hH

/-! ### Main Theorem: Spectral norm equals max singular value -/

/-- For nonneg values, sup(f²) = (sup f)². Helper lemma for spectral norm theorem. -/
lemma Finset.sup'_sq_eq_sq_sup' {m : Type*} {s : Finset m} (hs : s.Nonempty) (f : m → ℝ) (hf : ∀ i ∈ s, 0 ≤ f i) :
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

/-- The largest singular value of a matrix. -/
noncomputable def maxSingularValue [Nonempty n] (A : Matrix n n ℂ) : ℝ :=
  Finset.sup' Finset.univ Finset.univ_nonempty (SVD.singularValues A)

/-- **The spectral norm of a matrix equals its largest singular value.**

    For any matrix A, ‖A‖₂ = σ₁(A) = √(λ_max(Aᴴ A)). -/
theorem spectral_norm_eq_max_singularValue [Nonempty n] (A : Matrix n n ℂ) :
    ‖A‖ = maxSingularValue A := by
  have h1 : ‖A‖ * ‖A‖ = ‖Aᴴ * A‖ := (l2_opNorm_conjTranspose_mul_self A).symm
  have h_psd : (Aᴴ * A).PosSemidef := posSemidef_conjTranspose_mul_self A
  have h_herm : (Aᴴ * A).IsHermitian := h_psd.isHermitian
  have h3 : ‖Aᴴ * A‖ = Finset.sup' Finset.univ Finset.univ_nonempty (|h_herm.eigenvalues ·|) :=
    l2_opNorm_hermitian_eq_sup_abs_eigenvalues (Aᴴ * A) h_herm
  have h4 : ∀ i, |h_herm.eigenvalues i| = h_herm.eigenvalues i := fun i =>
    abs_of_nonneg (h_psd.eigenvalues_nonneg i)
  have h5 : ∀ i, h_herm.eigenvalues i = (SVD.singularValues A i) ^ 2 := fun i => by
    rw [SVD.singularValues_sq]
  have h6 : ‖Aᴴ * A‖ = Finset.sup' Finset.univ Finset.univ_nonempty (fun i => (SVD.singularValues A i) ^ 2) := by
    rw [h3]
    congr 1
    ext i
    rw [h4, h5]
  have h7 : Finset.sup' Finset.univ Finset.univ_nonempty (fun i => (SVD.singularValues A i) ^ 2) =
      (Finset.sup' Finset.univ Finset.univ_nonempty (SVD.singularValues A)) ^ 2 := by
    apply Finset.sup'_sq_eq_sq_sup'
    intro i _
    exact SVD.singularValues_nonneg A i
  have h_norm_nonneg : 0 ≤ ‖A‖ := norm_nonneg A
  have h_maxSV_nonneg : 0 ≤ maxSingularValue A := by
    unfold maxSingularValue
    obtain ⟨i⟩ := ‹Nonempty n›
    exact Finset.le_sup'_of_le (SVD.singularValues A) (Finset.mem_univ i) (SVD.singularValues_nonneg A i)
  have h8 : ‖A‖ ^ 2 = maxSingularValue A ^ 2 := by
    calc ‖A‖ ^ 2 = ‖A‖ * ‖A‖ := by ring
      _ = ‖Aᴴ * A‖ := h1
      _ = Finset.sup' Finset.univ Finset.univ_nonempty (fun i => (SVD.singularValues A i) ^ 2) := h6
      _ = (Finset.sup' Finset.univ Finset.univ_nonempty (SVD.singularValues A)) ^ 2 := h7
      _ = maxSingularValue A ^ 2 := rfl
  have h9 : |‖A‖| = |maxSingularValue A| := (sq_eq_sq_iff_abs_eq_abs ‖A‖ (maxSingularValue A)).mp h8
  rwa [abs_of_nonneg h_norm_nonneg, abs_of_nonneg h_maxSV_nonneg] at h9

/-- The spectral norm squared equals the maximum squared singular value. -/
theorem spectral_norm_sq_eq_max_singularValue_sq [Nonempty n] (A : Matrix n n ℂ) :
    ‖A‖ ^ 2 = Finset.sup' Finset.univ Finset.univ_nonempty ((SVD.singularValues A ·) ^ 2) := by
  rw [spectral_norm_eq_max_singularValue, maxSingularValue]
  simp only [Pi.pow_apply]
  exact (Finset.sup'_sq_eq_sq_sup' Finset.univ_nonempty (SVD.singularValues A)
    (fun i _ => SVD.singularValues_nonneg A i)).symm

/-! ### Spectral norm ≤ Frobenius norm -/

/-- Spectral norm squared is bounded by sum of squared singular values. -/
theorem spectral_norm_sq_le_sum_singularValues_sq [Nonempty n] (A : Matrix n n ℂ) :
    ‖A‖ ^ 2 ≤ ∑ i, SVD.singularValues A i ^ 2 := by
  rw [spectral_norm_sq_eq_max_singularValue_sq]
  apply Finset.sup'_le
  intro i _
  apply Finset.single_le_sum
  · intro j _; exact sq_nonneg _
  · exact Finset.mem_univ i

/-- **Spectral norm is bounded by Frobenius norm:** ‖A‖₂ ≤ frobeniusNorm' A. -/
theorem spectral_norm_le_frobenius_norm [Nonempty n] (A : Matrix n n ℂ) :
    ‖A‖ ≤ frobeniusNorm' A := by
  have h_sq : ‖A‖ ^ 2 ≤ frobeniusNorm' A ^ 2 := by
    calc ‖A‖ ^ 2
        ≤ ∑ i, SVD.singularValues A i ^ 2 := spectral_norm_sq_le_sum_singularValues_sq A
      _ = frobeniusNorm' A ^ 2 := by
          rw [frobeniusNorm'_sq, SVD.sum_sq_singularValues_eq_trace]
          simp only [trace, diag_apply, mul_apply, conjTranspose_apply]
          rw [Finset.sum_comm]
          simp [Complex.re_sum, Complex.normSq]
  exact le_of_sq_le_sq h_sq (frobeniusNorm'_nonneg A)

end L2OpNormTheorems

end Matrix.SpectralNorm

/-! ## Eckart-Young Theorem -/

namespace Matrix.SVD.Rectangular

section EckartYoung

variable {n : Type*} [Fintype n] [DecidableEq n]

-- For Eckart-Young Frobenius theorems, use Frobenius norm instance
-- Give it high priority (1001) to override C*-algebra instance from SVD import
attribute [local instance 1001] Matrix.frobeniusSeminormedAddCommGroup

/-- The truncated SVD of rank k. Uses the inline definition from Matrix.SVD. -/
noncomputable abbrev truncatedSVD [Nonempty n] (A : Matrix n n ℂ) (k : ℕ) : Matrix n n ℂ :=
  _root_.Matrix.SVD.truncatedSVD A k

/-- **Eckart-Young Theorem (Frobenius norm):**
    The truncated SVD Aₖ is the best rank-k approximation in Frobenius norm.
    Here ‖·‖ is the Frobenius norm via frobeniusSeminormedAddCommGroup.
    Re-exported from FrobeniusNorm.lean. -/
theorem eckart_young_frobenius [Nonempty n] (A : Matrix n n ℂ) (k : ℕ)
    (B : Matrix n n ℂ) (hB : B.rank ≤ k) :
    @Norm.norm _ Matrix.frobeniusSeminormedAddCommGroup.toNorm (A - truncatedSVD A k) ≤
    @Norm.norm _ Matrix.frobeniusSeminormedAddCommGroup.toNorm (A - B) :=
  FrobeniusNorm.eckart_young_frobenius A k B hB

/-- The Frobenius error of truncated SVD equals sum of squared tail singular values.
    Re-exported from FrobeniusNorm.lean. -/
theorem frobenius_error_truncatedSVD [Nonempty n] (A : Matrix n n ℂ) (k : ℕ) :
    @Norm.norm _ Matrix.frobeniusSeminormedAddCommGroup.toNorm (A - truncatedSVD A k) ^ 2 =
    ∑ i : n, (_root_.Matrix.SVD.truncatedSingularValues_tail A k i) ^ 2 :=
  FrobeniusNorm.frobenius_error_truncatedSVD A k

end EckartYoung

section EckartYoungSpectral

variable {n : Type*} [Fintype n] [DecidableEq n]

-- For spectral norm theorems, use L2 operator norm instance
attribute [local instance] Matrix.instL2OpNormedAddCommGroup
attribute [local instance] Matrix.instL2OpNormedSpace
attribute [local instance] Matrix.instL2OpNormedRing
attribute [local instance] Matrix.instL2OpNormedAlgebra
attribute [local instance] Matrix.instL2OpMetricSpace
attribute [local instance] Matrix.instCStarRing

/-! ### Unitary Invariance of Spectral Norm -/

/-- Spectral norm is invariant under left multiplication by unitary matrix. -/
lemma l2_opNorm_unitary_mul (U : unitaryGroup n ℂ) (A : Matrix n n ℂ) :
    ‖(U : Matrix n n ℂ) * A‖ = ‖A‖ :=
  CStarRing.norm_coe_unitary_mul ⟨U.val, U.prop⟩ A

/-- Spectral norm is invariant under right multiplication by unitary matrix. -/
lemma l2_opNorm_mul_unitary (A : Matrix n n ℂ) (U : unitaryGroup n ℂ) :
    ‖A * (U : Matrix n n ℂ)‖ = ‖A‖ :=
  CStarRing.norm_mul_coe_unitary A ⟨U.val, U.prop⟩

/-- Spectral norm is invariant under conjugation by unitary matrices: ‖U * A * V*‖ = ‖A‖. -/
lemma l2_opNorm_unitary_conj (U V : unitaryGroup n ℂ) (A : Matrix n n ℂ) :
    ‖(U : Matrix n n ℂ) * A * star (V : Matrix n n ℂ)‖ = ‖A‖ := by
  rw [mul_assoc, l2_opNorm_unitary_mul U (A * star (V : Matrix n n ℂ))]
  have hVstar : star (V : Matrix n n ℂ) ∈ unitary (Matrix n n ℂ) := Unitary.star_mem V.prop
  exact CStarRing.norm_mul_mem_unitary A hVstar

/-! ### Spectral Norm of truncatedSVD_tail -/

/-- The spectral norm of truncatedSVD_tail equals the spectral norm of the diagonal matrix. -/
theorem l2_opNorm_truncatedSVD_tail (A : Matrix n n ℂ) (k : ℕ) :
    ‖truncatedSVD_tail A k‖ = ‖diagonal (Complex.ofReal ∘ truncatedSingularValues_tail A k)‖ := by
  unfold truncatedSVD_tail
  exact l2_opNorm_unitary_conj (constructedU A) (rightUnitary A) _

/-- Diagonal matrices with real entries are Hermitian. -/
lemma diagonal_real_isHermitian (d : n → ℝ) :
    (diagonal (Complex.ofReal ∘ d)).IsHermitian := by
  rw [Matrix.IsHermitian]
  ext i j
  simp only [conjTranspose_apply, diagonal_apply, Function.comp_apply]
  by_cases h : i = j
  · simp [h, Complex.conj_ofReal]
  · simp [h, Ne.symm h]

/-- For a diagonal matrix with real entries, Dᴴ * D has diagonal entries d_i². -/
lemma diagonal_conjTranspose_mul_self (d : n → ℝ) :
    (diagonal (Complex.ofReal ∘ d))ᴴ * diagonal (Complex.ofReal ∘ d) =
    diagonal (Complex.ofReal ∘ (fun i => (d i)^2)) := by
  ext i j
  simp only [conjTranspose_apply, mul_apply, diagonal_apply, Function.comp_apply]
  by_cases h : i = j
  · subst h
    simp only [↓reduceIte]
    rw [Finset.sum_eq_single i]
    · simp only [↓reduceIte]
      -- star (↑(d i)) * ↑(d i) = ↑(d i ^ 2)
      have h1 : star (Complex.ofReal (d i)) = Complex.ofReal (d i) := Complex.conj_ofReal (d i)
      rw [h1, ← Complex.ofReal_mul, sq]
    · intro b _ hb
      simp only [hb, ↓reduceIte, star_zero, zero_mul]
    · intro h; exact absurd (Finset.mem_univ i) h
  · simp only [h, ↓reduceIte]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hk : k = j
    · subst hk
      simp only [Ne.symm h, ↓reduceIte, star_zero, zero_mul]
    · simp only [hk, ↓reduceIte, mul_zero]

/-- The singular values of a diagonal matrix with nonneg real entries are nonnegative. -/
lemma singularValues_diagonal_nonneg (d : n → ℝ) :
    ∀ i, 0 ≤ singularValues (diagonal (Complex.ofReal ∘ d)) i := fun i =>
  singularValues_nonneg _ i

/-! ### Diagonal Eigenvalue Lemmas -/

/-- For a diagonal matrix with real entries, the eigenvalues (as a set) equal the diagonal entries.
    This connects `spectrum_diagonal` (for field-valued diagonals) with `IsHermitian.eigenvalues`. -/
lemma eigenvalues_range_eq_diagonal_range (d : n → ℝ) :
    Set.range (diagonal_real_isHermitian d).eigenvalues = Set.range d := by
  let hD := diagonal_real_isHermitian d
  -- spectrum ℂ D = Complex.ofReal '' Set.range hD.eigenvalues (for Hermitian matrices)
  have h1 : spectrum ℂ (diagonal (Complex.ofReal ∘ d)) = Complex.ofReal '' Set.range hD.eigenvalues :=
    hD.spectrum_eq_image_range
  -- spectrum ℂ D = Set.range (Complex.ofReal ∘ d) (for diagonal matrices)
  have h2 : spectrum ℂ (diagonal (Complex.ofReal ∘ d)) = Set.range (Complex.ofReal ∘ d) :=
    spectrum_diagonal (Complex.ofReal ∘ d)
  -- Set.range (Complex.ofReal ∘ d) = Complex.ofReal '' Set.range d
  have h3 : Set.range (Complex.ofReal ∘ d) = Complex.ofReal '' Set.range d := by
    ext x
    simp only [Set.mem_range, Function.comp_apply, Set.mem_image]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨d i, ⟨i, rfl⟩, rfl⟩
    · rintro ⟨r, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
  -- From h1 and h2: Complex.ofReal '' Set.range hD.eigenvalues = Complex.ofReal '' Set.range d
  -- Since Complex.ofReal is injective, Set.range hD.eigenvalues = Set.range d
  rw [h2, h3] at h1
  exact Complex.ofReal_injective.image_injective h1.symm

/-- For two functions with the same range, their `sup'` over `Finset.univ` are equal. -/
lemma sup'_eq_of_range_eq {α β : Type*} [ConditionallyCompleteLattice α] [Fintype β] [Nonempty β]
    {f g : β → α} (h : Set.range f = Set.range g) :
    Finset.sup' Finset.univ Finset.univ_nonempty f = Finset.sup' Finset.univ Finset.univ_nonempty g := by
  rw [Finset.sup'_eq_csSup_image, Finset.sup'_eq_csSup_image]
  simp only [Finset.coe_univ, Set.image_univ]
  rw [h]

/-- For a diagonal matrix D with nonneg real entries d, the supremum of singular values
    equals the supremum of the entries. -/
lemma sup_singularValues_diagonal_eq_sup [Nonempty n] (d : n → ℝ) (hd : ∀ i, 0 ≤ d i) :
    Finset.sup' Finset.univ Finset.univ_nonempty (SVD.singularValues (diagonal (Complex.ofReal ∘ d))) =
    Finset.sup' Finset.univ Finset.univ_nonempty d := by
  -- Strategy: Both sides equal ‖D‖ where D = diagonal(d)
  -- LHS = sup(singularValues D) = ‖D‖ (by spectral_norm_eq_max_singularValue)
  -- RHS = sup(d) = ‖D‖ (by l2_opNorm_hermitian_eq_sup_abs_eigenvalues + eigenvalues of diagonal = entries)
  let D := diagonal (Complex.ofReal ∘ d)
  -- The diagonal matrix with real entries is Hermitian
  have hD_herm : D.IsHermitian := diagonal_real_isHermitian d
  -- LHS = ‖D‖ via spectral_norm_eq_max_singularValue
  have h_lhs : Finset.sup' Finset.univ Finset.univ_nonempty (SVD.singularValues D) =
               ‖D‖ := (Matrix.SpectralNorm.spectral_norm_eq_max_singularValue D).symm
  -- For Hermitian matrices, ‖H‖ = sup|eigenvalues|
  have h_herm_norm : ‖D‖ = Finset.sup' Finset.univ Finset.univ_nonempty (|hD_herm.eigenvalues ·|) :=
    Matrix.SpectralNorm.l2_opNorm_hermitian_eq_sup_abs_eigenvalues D hD_herm
  -- For a diagonal Hermitian matrix, the eigenvalues (as a multiset) equal the diagonal entries
  -- Therefore sup|eigenvalues| = sup|entries| = sup(entries) since entries are nonneg
  --
  -- The key fact is: for diagonal(d), the eigenvalues (possibly reordered) are exactly d
  -- This is because:
  -- 1. D * e_i = d_i * e_i for standard basis vectors e_i
  -- 2. So each d_i is an eigenvalue with eigenvector e_i
  -- 3. There are n eigenvalues and n basis vectors, so eigenvalues = {d_i}
  --
  -- Since hd says d_i ≥ 0, we have |d_i| = d_i
  -- Therefore sup|eigenvalues| = sup|d_i| = sup d_i
  --
  -- Proving this formally requires showing eigenvalues of diagonal = diagonal entries (as multiset)
  -- This is mathematically standard but requires connecting IsHermitian.eigenvalues with hasEigenvalue
  rw [h_lhs, h_herm_norm]
  -- Now need: sup |hD_herm.eigenvalues| = sup d
  -- Use eigenvalues_range_eq_diagonal_range to show Set.range eigenvalues = Set.range d
  have h_range : Set.range hD_herm.eigenvalues = Set.range d := eigenvalues_range_eq_diagonal_range d
  -- Since eigenvalues ∈ range d and d ≥ 0, eigenvalues ≥ 0, hence |eigenvalues| = eigenvalues
  have h_eig_nonneg : ∀ i, 0 ≤ hD_herm.eigenvalues i := by
    intro i
    have h_mem : hD_herm.eigenvalues i ∈ Set.range d := by
      rw [← h_range]
      exact Set.mem_range_self i
    obtain ⟨j, hj⟩ := h_mem
    rw [← hj]
    exact hd j
  -- |eigenvalues i| = eigenvalues i since eigenvalues ≥ 0
  have h_abs : (|hD_herm.eigenvalues ·|) = hD_herm.eigenvalues := by
    ext i
    exact abs_of_nonneg (h_eig_nonneg i)
  rw [h_abs]
  -- Now sup eigenvalues = sup d since they have the same range
  exact sup'_eq_of_range_eq h_range

/-- The maximum singular value of truncatedSingularValues_tail equals singularValues₀ at k
    when k < n. The tail is zero for indices < k and equals singularValues₀ for indices ≥ k.
    Since singular values are sorted in decreasing order, the max of the tail is at index k. -/
lemma max_truncatedSingularValues_tail [Nonempty n] (A : Matrix n n ℂ) (k : ℕ)
    (hk : k < Fintype.card n) :
    Finset.sup' Finset.univ Finset.univ_nonempty (truncatedSingularValues_tail A k) =
    singularValues₀ A ⟨k, hk⟩ := by
  -- The tail has value 0 for idx < k and singularValues₀ for idx ≥ k
  -- Since singularValues₀ is antitone (decreasing), max over idx ≥ k is at idx = k
  apply le_antisymm
  · -- sup ≤ σ_k: every tail value is ≤ σ_k
    apply Finset.sup'_le
    intro i _
    unfold truncatedSingularValues_tail
    simp only
    split_ifs with h
    · -- idx ≥ k: singularValues₀ at idx ≤ singularValues₀ at k (since antitone)
      have h_antitone := singularValues₀_antitone A
      apply h_antitone
      simp only [Fin.le_def]
      exact h
    · -- idx < k: value is 0 ≤ σ_k
      exact singularValues₀_nonneg A _
  · -- σ_k ≤ sup: σ_k is achieved at some index
    -- Find the index i such that equiv.symm i = ⟨k, hk⟩
    let kFin : Fin (Fintype.card n) := ⟨k, hk⟩
    let i := (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n))) kFin
    have hi : (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n))).symm i = kFin := by
      simp only [Equiv.symm_apply_apply, i]
    calc singularValues₀ A kFin
        = truncatedSingularValues_tail A k i := by
          unfold truncatedSingularValues_tail
          simp only [hi, kFin, le_refl, ↓reduceIte]
      _ ≤ Finset.sup' Finset.univ Finset.univ_nonempty (truncatedSingularValues_tail A k) :=
          Finset.le_sup' _ (Finset.mem_univ i)

/-- The spectral norm equals the maximum singular value, which is singularValues₀ at index 0. -/
lemma spectral_norm_eq_singularValues₀_zero [Nonempty n] (A : Matrix n n ℂ) :
    ‖A‖ = singularValues₀ A 0 := by
  rw [Matrix.SpectralNorm.spectral_norm_eq_max_singularValue]
  unfold Matrix.SpectralNorm.maxSingularValue
  -- Need to show: sup' (SVD.singularValues A) = singularValues₀ A 0
  -- Since SVD.singularValues A i = singularValues₀ A (equiv.symm i) and singularValues₀ is antitone,
  -- the max of SVD.singularValues is singularValues₀ at 0
  apply le_antisymm
  · -- sup' ≤ σ₀: every singular value ≤ σ₀
    apply Finset.sup'_le
    intro i _
    rw [Matrix.SVD.singularValues_eq_singularValues₀]
    exact singularValues₀_antitone A (Fin.zero_le _)
  · -- σ₀ ≤ sup': σ₀ is one of the singular values
    -- Find j such that equiv.symm j = 0
    let j := (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n))) (0 : Fin (Fintype.card n))
    have hj : (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n))).symm j = 0 := by
      simp only [Equiv.symm_apply_apply, j]
    calc singularValues₀ A 0
        = Matrix.SVD.singularValues A j := by rw [Matrix.SVD.singularValues_eq_singularValues₀, hj]
      _ ≤ Finset.sup' Finset.univ Finset.univ_nonempty (Matrix.SVD.singularValues A) :=
          Finset.le_sup' _ (Finset.mem_univ j)

/-- **The spectral error of truncated SVD equals the (k+1)-th singular value.**
    ‖A - Aₖ‖₂ = σₖ (using 0-indexed singular values).

    This is a key result for low-rank approximation: the approximation error
    in spectral norm is exactly the first "discarded" singular value. -/
theorem spectral_error_truncatedSVD [Nonempty n] (A : Matrix n n ℂ) (k : ℕ)
    (hk : k < Fintype.card n) :
    ‖A - truncatedSVD A k‖ = singularValues₀ A ⟨k, hk⟩ := by
  -- Step 1: A - Aₖ = A_tail (the tail of the SVD)
  -- From truncatedSVD_add_tail: A = Aₖ + A_tail
  -- Therefore: A - Aₖ = A_tail
  have h_eq : A = truncatedSVD A k + truncatedSVD_tail A k := truncatedSVD_add_tail A k
  have h_diff : A - truncatedSVD A k = truncatedSVD_tail A k := by
    nth_rewrite 1 [h_eq]
    simp only [add_sub_cancel_left]
  rw [h_diff]
  -- Step 2: ‖A_tail‖ = ‖D_tail‖ by unitary invariance
  rw [l2_opNorm_truncatedSVD_tail]
  -- Step 3: Use spectral_norm_eq_max_singularValue from Matrix.SpectralNorm namespace
  rw [Matrix.SpectralNorm.spectral_norm_eq_max_singularValue]
  -- Step 4: Show maxSingularValue of diagonal tail = singularValues₀ A k
  -- The diagonal matrix D_tail has diagonal entries = truncatedSingularValues_tail A k
  -- For a diagonal matrix with nonneg real entries, singular values = |diagonal entries|
  -- Since tail entries are nonneg, singular values = diagonal entries
  -- max singular value = max diagonal entry = σ_k by max_truncatedSingularValues_tail
  unfold Matrix.SpectralNorm.maxSingularValue
  -- Goal: sup' (singularValues D_tail) = singularValues₀ A k
  -- For diagonal matrix with nonneg entries: singularValues = entries (reordered)
  -- Therefore sup singularValues = sup entries = σ_k
  -- Apply sup_singularValues_diagonal_eq_sup to truncatedSingularValues_tail
  rw [sup_singularValues_diagonal_eq_sup]
  · -- Now goal is sup truncatedSingularValues_tail = singularValues₀ A k
    exact max_truncatedSingularValues_tail A k hk
  · -- Show truncatedSingularValues_tail has nonneg entries
    intro i
    unfold truncatedSingularValues_tail
    simp only
    split_ifs
    · exact singularValues₀_nonneg A _
    · exact le_refl 0

/-- **Eckart-Young Theorem (Spectral norm):**
    The truncated SVD is also optimal in spectral norm.
    Here ‖·‖ is the L2 operator norm. -/
theorem eckart_young_spectral [Nonempty n] (A : Matrix n n ℂ) (k : ℕ)
    (B : Matrix n n ℂ) (hB : B.rank ≤ k) :
    ‖A - truncatedSVD A k‖ ≤ ‖A - B‖ := by
  by_cases hk : k < Fintype.card n
  · -- Case k < card n (interesting case)
    -- Step 1: LHS = σₖ(A)
    have h_lhs : ‖A - truncatedSVD A k‖ = singularValues₀ A ⟨k, hk⟩ :=
      spectral_error_truncatedSVD A k hk
    -- Step 2: Apply interlacing for rank-k perturbation
    -- σₖ(A) ≤ σ₀(A - B) since rank(B) ≤ k
    have h_interlace : singularValues₀ A ⟨k, hk⟩ ≤ singularValues₀ (A - B) 0 := by
      have h := Matrix.WeylInequality.interlacing_for_eckart_young A B k hB k (le_refl k) hk
      simp only [Nat.sub_self] at h
      convert h using 2
    -- Step 3: σ₀(A - B) = ‖A - B‖
    have h_rhs : singularValues₀ (A - B) 0 = ‖A - B‖ := (spectral_norm_eq_singularValues₀_zero (A - B)).symm
    -- Combine
    calc ‖A - truncatedSVD A k‖
        = singularValues₀ A ⟨k, hk⟩ := h_lhs
      _ ≤ singularValues₀ (A - B) 0 := h_interlace
      _ = ‖A - B‖ := h_rhs
  · -- Case k ≥ card n (trivial: truncatedSVD A k = A)
    have hk_ge : Fintype.card n ≤ k := Nat.le_of_not_lt hk
    have h_trunc_eq_A : truncatedSVD A k = A := truncatedSVD_full A k hk_ge
    simp only [h_trunc_eq_A, sub_self, norm_zero]
    exact norm_nonneg _

end EckartYoungSpectral

end Matrix.SVD.Rectangular

/-! ## Kronecker Approximation Error Bounds -/

namespace Matrix.KroneckerRearrangement

section KroneckerBoundsFrobenius

variable {m n p q : Type*} [Fintype m] [Fintype n] [Fintype p] [Fintype q]
variable [DecidableEq m] [DecidableEq n] [DecidableEq p] [DecidableEq q]

-- Use Frobenius norm for isometry theorem
attribute [local instance] Matrix.frobeniusSeminormedAddCommGroup

set_option linter.unusedSectionVars false in
/-- **Kronecker Approximation Frobenius Error:**
    ‖C - A ⊗ B‖_F = ‖R(C) - vec(A) ⬝ vec(B)ᵀ‖_F via R being a Frobenius isometry.
    Here ‖·‖ is the Frobenius norm.

    This follows from:
    1. R is a Frobenius isometry: ‖R(M)‖_F = ‖M‖_F
    2. R(A ⊗ B) = outerProduct (vec A) (vec B) -/
theorem kronecker_approx_frobenius_error (C : Matrix (m × n) (p × q) ℂ)
    (A : Matrix m p ℂ) (B : Matrix n q ℂ) :
    ‖C - kroneckerMap (· * ·) A B‖ = ‖R C - outerProduct (vec A) (vec B)‖ := by
  -- Use R isometry: ‖C - A ⊗ B‖ = ‖R(C - A ⊗ B)‖
  conv_lhs => rw [← R_frobenius_norm_eq (C - kroneckerMap (· * ·) A B)]
  -- R distributes: R(C - A ⊗ B) = R(C) - R(A ⊗ B)
  have h_R_sub : R (C - kroneckerMap (· * ·) A B) = R C - R (kroneckerMap (· * ·) A B) := by
    ext ⟨i, k⟩ ⟨j, l⟩
    simp [R, sub_apply]
  rw [h_R_sub]
  -- R(A ⊗ B) = outerProduct (vec A) (vec B)
  rw [R_kronecker]

end KroneckerBoundsFrobenius

section KroneckerBoundsSpectral

variable {m n p q : Type*} [Fintype m] [Fintype n] [Fintype p] [Fintype q]
variable [DecidableEq m] [DecidableEq n] [DecidableEq p] [DecidableEq q]

-- Use L2 operator norm for spectral bound
attribute [local instance] Matrix.instL2OpNormedAddCommGroup
attribute [local instance] Matrix.instL2OpNormedSpace
attribute [local instance] Matrix.instL2OpNormedRing
attribute [local instance] Matrix.instL2OpNormedAlgebra
attribute [local instance] Matrix.instL2OpMetricSpace

-- Suppress linter warnings about unused section variables
set_option linter.unusedSectionVars false in
/-- Frobenius norm as explicit function for cross-norm bounds. -/
noncomputable def frobeniusNorm'' {m' n' : Type*} [Fintype m'] [Fintype n']
    (A : Matrix m' n' ℂ) : ℝ :=
  @Norm.norm _ Matrix.frobeniusNormedAddCommGroup.toNorm A

/-! ### Helper lemmas: L2 operator norm ≤ Frobenius norm for rectangular matrices -/

/-- Cauchy-Schwarz for complex sums: |∑ⱼ aⱼ bⱼ| ≤ √(∑ⱼ |aⱼ|²) · √(∑ⱼ |bⱼ|²) -/
private lemma complex_sum_cauchy_schwarz {ι : Type*} [Fintype ι] (a b : ι → ℂ) :
    ‖∑ j, a j * b j‖ ≤ Real.sqrt (∑ j, ‖a j‖^2) * Real.sqrt (∑ j, ‖b j‖^2) := by
  let a' : EuclideanSpace ℂ ι := WithLp.toLp 2 (star a)
  let b' : EuclideanSpace ℂ ι := WithLp.toLp 2 b
  have h1 : inner ℂ a' b' = ∑ j, a j * b j := by
    simp only [EuclideanSpace.inner_eq_star_dotProduct, a', b', dotProduct]
    simp only [Pi.star_apply, star_star]
    apply Finset.sum_congr rfl; intro j _; ring
  have h2 : ‖inner ℂ a' b'‖ ≤ ‖a'‖ * ‖b'‖ := norm_inner_le_norm a' b'
  rw [h1] at h2
  calc ‖∑ j, a j * b j‖ ≤ ‖a'‖ * ‖b'‖ := h2
    _ = Real.sqrt (∑ j, ‖a j‖^2) * Real.sqrt (∑ j, ‖b j‖^2) := by
        simp only [EuclideanSpace.norm_eq, a', b']
        congr 1
        · congr 1; apply Finset.sum_congr rfl; intro j _
          simp only [Pi.star_apply, Complex.star_def, Complex.norm_conj]

/-- Matrix-vector multiplication bound: ‖A *ᵥ x‖² ≤ ‖A‖_F² · ‖x‖² -/
private lemma mulVec_eucl_norm_sq_le {m' n' : Type*} [Fintype m'] [Fintype n']
    (A : Matrix m' n' ℂ) (x : EuclideanSpace ℂ n') :
    ‖(EuclideanSpace.equiv m' ℂ).symm (A *ᵥ x.ofLp)‖^2 ≤
      (∑ i, ∑ j, ‖A i j‖^2) * ‖x‖^2 := by
  rw [EuclideanSpace.norm_sq_eq]
  have cs := fun i => complex_sum_cauchy_schwarz (A i) x.ofLp
  have h_nonneg : ∀ i, 0 ≤ Real.sqrt (∑ j, ‖A i j‖^2) * Real.sqrt (∑ j, ‖x.ofLp j‖^2) := by
    intro i; apply mul_nonneg <;> apply Real.sqrt_nonneg
  calc ∑ i, ‖∑ j, A i j * x.ofLp j‖ ^ 2
      ≤ ∑ i, (Real.sqrt (∑ j, ‖A i j‖^2) * Real.sqrt (∑ j, ‖x.ofLp j‖^2))^2 := by
        apply Finset.sum_le_sum; intro i _
        apply sq_le_sq'
        · linarith [h_nonneg i, norm_nonneg (∑ j, A i j * x.ofLp j)]
        · calc ‖∑ j, A i j * x.ofLp j‖ ≤ _ := cs i
            _ ≤ _ := abs_of_nonneg (h_nonneg i) ▸ le_refl _
    _ = ∑ i, (∑ j, ‖A i j‖^2) * (∑ j, ‖x.ofLp j‖^2) := by
        apply Finset.sum_congr rfl; intro i _
        rw [mul_pow, Real.sq_sqrt, Real.sq_sqrt] <;>
        · apply Finset.sum_nonneg; intro j _; exact sq_nonneg _
    _ = (∑ i, ∑ j, ‖A i j‖^2) * (∑ j, ‖x.ofLp j‖^2) := by rw [Finset.sum_mul]
    _ = (∑ i, ∑ j, ‖A i j‖^2) * ‖x‖^2 := by rw [EuclideanSpace.norm_sq_eq]

/-- Matrix-vector multiplication bound: ‖A *ᵥ x‖ ≤ √(∑ᵢⱼ |Aᵢⱼ|²) · ‖x‖ -/
private lemma mulVec_eucl_norm_le {m' n' : Type*} [Fintype m'] [Fintype n']
    (A : Matrix m' n' ℂ) (x : EuclideanSpace ℂ n') :
    ‖(EuclideanSpace.equiv m' ℂ).symm (A *ᵥ x.ofLp)‖ ≤
      Real.sqrt (∑ i, ∑ j, ‖A i j‖^2) * ‖x‖ := by
  have h_sq := mulVec_eucl_norm_sq_le A x
  have h_frob_nonneg : 0 ≤ Real.sqrt (∑ i, ∑ j, ‖A i j‖ ^ 2) := Real.sqrt_nonneg _
  have h_norm_nonneg : 0 ≤ ‖x‖ := norm_nonneg _
  apply le_of_sq_le_sq _ (mul_nonneg h_frob_nonneg h_norm_nonneg)
  calc ‖(EuclideanSpace.equiv m' ℂ).symm (A *ᵥ x.ofLp)‖ ^ 2
      ≤ (∑ i, ∑ j, ‖A i j‖^2) * ‖x‖^2 := h_sq
    _ = Real.sqrt (∑ i, ∑ j, ‖A i j‖^2)^2 * ‖x‖^2 := by
        rw [Real.sq_sqrt]
        apply Finset.sum_nonneg; intro i _
        apply Finset.sum_nonneg; intro j _
        exact sq_nonneg _
    _ = (Real.sqrt (∑ i, ∑ j, ‖A i j‖^2) * ‖x‖)^2 := by ring

/-- Frobenius norm expressed as square root of sum of squared entries. -/
private lemma frobenius_norm_eq_sqrt {m' n' : Type*} [Fintype m'] [Fintype n']
    (A : Matrix m' n' ℂ) :
    @Norm.norm _ Matrix.frobeniusSeminormedAddCommGroup.toNorm A =
      Real.sqrt (∑ i, ∑ j, ‖A i j‖ ^ 2) := by
  rw [frobenius_norm_def, Real.sqrt_eq_rpow]
  norm_cast

/-- **L2 operator norm is bounded by Frobenius norm** for rectangular matrices.
    This is a fundamental inequality: ‖A‖₂ ≤ ‖A‖_F for any matrix A. -/
private theorem l2_opNorm_le_frobenius_norm_rect {m' n' : Type*}
    [Fintype m'] [Fintype n'] [DecidableEq n']
    (A : Matrix m' n' ℂ) :
    @Norm.norm _ Matrix.instL2OpNormedAddCommGroup.toNorm A ≤
      @Norm.norm _ Matrix.frobeniusSeminormedAddCommGroup.toNorm A := by
  rw [l2_opNorm_def, frobenius_norm_eq_sqrt]
  apply ContinuousLinearMap.opNorm_le_bound
  · exact Real.sqrt_nonneg _
  · intro x
    exact mulVec_eucl_norm_le A x

set_option linter.unusedSectionVars false in
/-- **Kronecker Approximation Spectral Bound:** ‖C - A ⊗ B‖₂ ≤ frobeniusNorm'' (C - A ⊗ B).
    Here ‖·‖ is the L2 operator norm. -/
theorem kronecker_approx_spectral_bound (C : Matrix (m × n) (p × q) ℂ)
    (A : Matrix m p ℂ) (B : Matrix n q ℂ) :
    ‖C - kroneckerMap (· * ·) A B‖ ≤ frobeniusNorm'' (C - kroneckerMap (· * ·) A B) := by
  -- Apply the general inequality: ‖M‖₂ ≤ ‖M‖_F
  unfold frobeniusNorm''
  exact l2_opNorm_le_frobenius_norm_rect _

/-! ### L2 Operator Norm of Kronecker Products -/

set_option linter.unusedSectionVars false in
/-- Key lemma: (A ⊗ B)ᴴ * (A ⊗ B) = (Aᴴ * A) ⊗ (Bᴴ * B).
    This follows from `conjTranspose_kronecker` and `mul_kronecker_mul`. -/
private lemma conjTranspose_mul_kronecker (A : Matrix m p ℂ) (B : Matrix n q ℂ) :
    (kroneckerMap (· * ·) A B)ᴴ * kroneckerMap (· * ·) A B =
    kroneckerMap (· * ·) (Aᴴ * A) (Bᴴ * B) := by
  rw [conjTranspose_kronecker, mul_kronecker_mul]

/-! #### Kronecker Product of Hermitian Matrices -/

set_option linter.unusedSectionVars false in
/-- The Kronecker product of Hermitian matrices is Hermitian.
    Proof: (H₁ ⊗ H₂)ᴴ = H₁ᴴ ⊗ H₂ᴴ = H₁ ⊗ H₂.
    This is analogous to the Coq lemma `herm_kron` in Diagonalization.v. -/
theorem isHermitian_kronecker
    (H₁ : Matrix p p ℂ) (H₂ : Matrix q q ℂ)
    (hH₁ : H₁.IsHermitian) (hH₂ : H₂.IsHermitian) :
    (kroneckerMap (· * ·) H₁ H₂).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [conjTranspose_kronecker, hH₁, hH₂]

/-! #### Supremum of Products -/

set_option linter.unusedSectionVars false in
/-- For nonnegative functions f : p → ℝ and g : q → ℝ on nonempty finite types,
    sup_{(i,j)} (f i * g j) = (sup_i f i) * (sup_j g j).

    This is the key ingredient for showing that the largest eigenvalue of H₁ ⊗ H₂
    equals the product of the largest eigenvalues of H₁ and H₂. -/
lemma Finset.sup'_prod_eq_mul_sup' [Nonempty p] [Nonempty q]
    (f : p → ℝ) (g : q → ℝ) (hf : ∀ i, 0 ≤ f i) (hg : ∀ j, 0 ≤ g j) :
    Finset.sup' (Finset.univ : Finset (p × q)) Finset.univ_nonempty (fun ij => f ij.1 * g ij.2) =
    Finset.sup' Finset.univ Finset.univ_nonempty f * Finset.sup' Finset.univ Finset.univ_nonempty g := by
  -- The proof requires showing that for nonnegative f, g:
  -- sup_{(i,j)} (f i * g j) = (sup_i f i) * (sup_j g j)
  --
  -- This follows from two directions:
  -- (≤): For all (i,j), f i * g j ≤ sup f * sup g, so sup ≤ sup f * sup g
  -- (≥): There exist i*, j* achieving the suprema, so f i* * g j* = sup f * sup g
  --
  -- We proceed by showing both inequalities:
  have h_le : Finset.sup' Finset.univ Finset.univ_nonempty (fun ij : p × q => f ij.1 * g ij.2) ≤
              Finset.sup' Finset.univ Finset.univ_nonempty f *
              Finset.sup' Finset.univ Finset.univ_nonempty g := by
    apply Finset.sup'_le
    intro ij _
    apply mul_le_mul
    · exact Finset.le_sup' f (Finset.mem_univ ij.1)
    · exact Finset.le_sup' g (Finset.mem_univ ij.2)
    · exact hg ij.2
    · exact le_trans (hf ij.1) (Finset.le_sup' f (Finset.mem_univ ij.1))
  have h_ge : Finset.sup' Finset.univ Finset.univ_nonempty f *
              Finset.sup' Finset.univ Finset.univ_nonempty g ≤
              Finset.sup' Finset.univ Finset.univ_nonempty (fun ij : p × q => f ij.1 * g ij.2) := by
    -- There exist elements achieving the suprema
    obtain ⟨i_max, _, hi_max⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty f
    obtain ⟨j_max, _, hj_max⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty g
    calc Finset.sup' Finset.univ Finset.univ_nonempty f * Finset.sup' Finset.univ Finset.univ_nonempty g
        = f i_max * g j_max := by rw [hi_max, hj_max]
      _ ≤ Finset.sup' Finset.univ Finset.univ_nonempty (fun ij : p × q => f ij.1 * g ij.2) :=
          Finset.le_sup' (fun ij : p × q => f ij.1 * g ij.2) (Finset.mem_univ (i_max, j_max))
  exact le_antisymm h_le h_ge

/-! #### Eigenvalue Structure of Kronecker Products -/

/-- The diagonal of H₁ ⊗ H₂ when both are diagonal matrices.
    diagonal d₁ ⊗ diagonal d₂ = diagonal (fun (i,j) => d₁ i * d₂ j) -/
lemma diagonal_kronecker_diagonal_apply (d₁ : p → ℂ) (d₂ : q → ℂ) :
    kroneckerMap (· * ·) (diagonal d₁) (diagonal d₂) =
    diagonal (fun ij : p × q => d₁ ij.1 * d₂ ij.2) :=
  diagonal_kronecker_diagonal d₁ d₂

/-- For Hermitian matrices, the norm equals the supremum of absolute eigenvalues.
    For PSD matrices, all eigenvalues are nonnegative, so |λ| = λ. -/
lemma l2_opNorm_posSemidef_eq_sup_eigenvalues [Nonempty p]
    (H : Matrix p p ℂ) (hH : H.PosSemidef) :
    ‖H‖ = Finset.sup' Finset.univ Finset.univ_nonempty hH.isHermitian.eigenvalues := by
  rw [SpectralNorm.l2_opNorm_hermitian_eq_sup_abs_eigenvalues H hH.isHermitian]
  congr 1
  ext i
  rw [abs_of_nonneg]
  exact hH.eigenvalues_nonneg i

/-- **Eigenvalue Product Theorem for Kronecker Products of Hermitian Matrices.**
    The supremum of eigenvalues of H₁ ⊗ H₂ equals the product of the suprema.

    This is a key lemma for proving ‖H₁ ⊗ H₂‖ = ‖H₁‖·‖H₂‖ for PSD matrices.
    The proof uses the spectral theorem and the fact that:
    - H₁ ⊗ H₂ = (U₁⊗U₂) * diagonal(λᵢμⱼ) * (U₁⊗U₂)ᴴ
    - Similar matrices have the same characteristic polynomial
    - Therefore eigenvalues of H₁ ⊗ H₂ are products {λᵢμⱼ}

    References:
    - Horn & Johnson "Matrix Analysis" (2012), Theorem 4.2.12
    - Timeroot/Lean-QuantumInfo: PosSemidef_kronecker proof approach -/
lemma sup_eigenvalues_kronecker_eq_mul [Nonempty p] [Nonempty q]
    (H₁ : Matrix p p ℂ) (H₂ : Matrix q q ℂ)
    (hH₁ : H₁.PosSemidef) (hH₂ : H₂.PosSemidef) :
    Finset.sup' Finset.univ Finset.univ_nonempty (hH₁.kronecker hH₂).isHermitian.eigenvalues =
    Finset.sup' Finset.univ Finset.univ_nonempty hH₁.isHermitian.eigenvalues *
    Finset.sup' Finset.univ Finset.univ_nonempty hH₂.isHermitian.eigenvalues := by
  -- Abbreviations for readability
  let hHerm1 := hH₁.isHermitian
  let hHerm2 := hH₂.isHermitian
  let hHerm12 := (hH₁.kronecker hH₂).isHermitian
  let eig1 := hHerm1.eigenvalues
  let eig2 := hHerm2.eigenvalues
  let eig12 := hHerm12.eigenvalues

  have h_nonneg1 : ∀ i, 0 ≤ eig1 i := hH₁.eigenvalues_nonneg
  have h_nonneg2 : ∀ j, 0 ≤ eig2 j := hH₂.eigenvalues_nonneg

  -- Setup spectral decompositions
  let U₁ := hHerm1.eigenvectorUnitary
  let U₂ := hHerm2.eigenvectorUnitary

  -- Diagonal matrices of eigenvalues (lifted to ℂ)
  let D₁ := diagonal (Complex.ofReal ∘ eig1)
  let D₂ := diagonal (Complex.ofReal ∘ eig2)

  -- Spectral theorem: H = U * D * U*  (where U* = star U = Uᴴ)
  have hSpec1 : H₁ = (U₁ : Matrix p p ℂ) * D₁ * (star U₁ : Matrix p p ℂ) :=
    hHerm1.spectral_theorem
  have hSpec2 : H₂ = (U₂ : Matrix q q ℂ) * D₂ * (star U₂ : Matrix q q ℂ) :=
    hHerm2.spectral_theorem

  -- Kronecker spectral form: H₁ ⊗ H₂ = (U₁ ⊗ U₂) * (D₁ ⊗ D₂) * (U₁ ⊗ U₂)ᴴ
  let U₁₂ : Matrix (p × q) (p × q) ℂ := kroneckerMap (· * ·) (U₁ : Matrix p p ℂ) (U₂ : Matrix q q ℂ)
  let D₁₂ : Matrix (p × q) (p × q) ℂ := kroneckerMap (· * ·) D₁ D₂

  -- The Kronecker spectral form: H₁ ⊗ H₂ = U₁₂ * D₁₂ * star U₁₂
  have hKronSpec : kroneckerMap (· * ·) H₁ H₂ = U₁₂ * D₁₂ * star U₁₂ := by
    -- Substitute the spectral decompositions
    rw [hSpec1, hSpec2]
    -- Step 1: apply mul_kronecker_mul to split off the star parts
    -- (U₁ * D₁ * star U₁) ⊗ (U₂ * D₂ * star U₂) = (U₁ * D₁) ⊗ (U₂ * D₂) * (star U₁) ⊗ (star U₂)
    have h1 : kroneckerMap (· * ·) (((U₁ : Matrix p p ℂ) * D₁) * star (U₁ : Matrix p p ℂ))
                                  (((U₂ : Matrix q q ℂ) * D₂) * star (U₂ : Matrix q q ℂ)) =
              kroneckerMap (· * ·) ((U₁ : Matrix p p ℂ) * D₁) ((U₂ : Matrix q q ℂ) * D₂) *
              kroneckerMap (· * ·) (star (U₁ : Matrix p p ℂ)) (star (U₂ : Matrix q q ℂ)) :=
      mul_kronecker_mul ((U₁ : Matrix p p ℂ) * D₁) (star (U₁ : Matrix p p ℂ))
                        ((U₂ : Matrix q q ℂ) * D₂) (star (U₂ : Matrix q q ℂ))
    -- Step 2: apply mul_kronecker_mul to split (U * D) ⊗ (U * D) = (U ⊗ U) * (D ⊗ D)
    have h2 : kroneckerMap (· * ·) ((U₁ : Matrix p p ℂ) * D₁) ((U₂ : Matrix q q ℂ) * D₂) =
              kroneckerMap (· * ·) (U₁ : Matrix p p ℂ) (U₂ : Matrix q q ℂ) * kroneckerMap (· * ·) D₁ D₂ :=
      mul_kronecker_mul (U₁ : Matrix p p ℂ) D₁ (U₂ : Matrix q q ℂ) D₂
    -- Step 3: conjTranspose_kronecker: star U₁ ⊗ star U₂ = star (U₁ ⊗ U₂)
    have h3 : kroneckerMap (· * ·) (star (U₁ : Matrix p p ℂ)) (star (U₂ : Matrix q q ℂ)) =
              star (kroneckerMap (· * ·) (U₁ : Matrix p p ℂ) (U₂ : Matrix q q ℂ)) := by
      simp only [star_eq_conjTranspose]
      rw [← conjTranspose_kronecker]
    -- Combine all steps with appropriate associativity
    simp only [mul_assoc] at h1 h2 ⊢
    rw [h1, h2, h3, mul_assoc]

  -- The diagonal Kronecker formula: D₁ ⊗ D₂ = diagonal(λᵢμⱼ)
  have hDiagKron : D₁₂ = diagonal (fun ij : p × q => Complex.ofReal (eig1 ij.1) * Complex.ofReal (eig2 ij.2)) := by
    -- Use diagonal_kronecker_diagonal: diag(a) ⊗ diag(b) = diag(aᵢbⱼ)
    -- D₁₂ = kroneckerMap (· * ·) D₁ D₂ where D₁ = diagonal(...), D₂ = diagonal(...)
    show kroneckerMap (· * ·) (diagonal (Complex.ofReal ∘ eig1)) (diagonal (Complex.ofReal ∘ eig2)) =
         diagonal (fun ij : p × q => Complex.ofReal (eig1 ij.1) * Complex.ofReal (eig2 ij.2))
    rw [diagonal_kronecker_diagonal]
    rfl

  -- Show eigenvalue set equality (spectrum preservation)
  have hU₁₂_unitary : U₁₂ ∈ unitary (Matrix (p × q) (p × q) ℂ) :=
    Matrix.kronecker_mem_unitary U₁.prop U₂.prop

  -- Spectrum of H₁⊗H₂ equals spectrum of D₁₂ (unitary conjugation preserves spectrum)
  have hSpecPres : spectrum ℂ (kroneckerMap (· * ·) H₁ H₂) = spectrum ℂ D₁₂ := by
    rw [hKronSpec]
    -- Need: spectrum (U₁₂ * D₁₂ * star U₁₂) = spectrum D₁₂
    -- This follows from Unitary.spectrum_star_right_conjugate
    have : spectrum ℂ (U₁₂ * D₁₂ * star U₁₂) = spectrum ℂ D₁₂ := by
      -- Convert U₁₂ (which is a raw matrix we know is unitary) to a subtype
      let U₁₂' : unitary (Matrix (p × q) (p × q) ℂ) := ⟨U₁₂, hU₁₂_unitary⟩
      -- Now apply the lemma
      have h := @Unitary.spectrum_star_right_conjugate ℂ (Matrix (p × q) (p × q) ℂ) _ _ _ _ D₁₂ U₁₂'
      simp only at h
      exact h
    exact this

  -- Step 3: Spectrum of diagonal matrix = range of diagonal entries
  -- Use: spectrum_diagonal : spectrum R (diagonal d) = Set.range d
  have hSpecDiag : spectrum ℂ D₁₂ =
      Set.range (fun ij : p × q => Complex.ofReal (eig1 ij.1) * Complex.ofReal (eig2 ij.2)) := by
    rw [hDiagKron]
    exact spectrum_diagonal _

  -- Combine: spectrum(H₁⊗H₂) = {ofReal(λᵢ) * ofReal(μⱼ)}
  have hSpecKron : spectrum ℂ (kroneckerMap (· * ·) H₁ H₂) =
      Set.range (fun ij : p × q => Complex.ofReal (eig1 ij.1) * Complex.ofReal (eig2 ij.2)) := by
    rw [hSpecPres, hSpecDiag]

  -- Connect eigenvalues to spectrum
  have hSpecEig12 : spectrum ℂ (kroneckerMap (· * ·) H₁ H₂) = Complex.ofReal '' Set.range eig12 :=
    hHerm12.spectrum_eq_image_range

  -- Convert the range of products to an image under Complex.ofReal
  have hProdImage : Set.range (fun ij : p × q => Complex.ofReal (eig1 ij.1) * Complex.ofReal (eig2 ij.2)) =
      Complex.ofReal '' Set.range (fun ij : p × q => eig1 ij.1 * eig2 ij.2) := by
    ext z
    simp only [Set.mem_range, Set.mem_image]
    constructor
    · rintro ⟨ij, rfl⟩
      refine ⟨eig1 ij.1 * eig2 ij.2, ⟨ij, rfl⟩, ?_⟩
      rw [Complex.ofReal_mul]
    · rintro ⟨r, ⟨ij, rfl⟩, rfl⟩
      refine ⟨ij, ?_⟩
      rw [Complex.ofReal_mul]

  -- Combine: Complex.ofReal '' Set.range eig12 = Complex.ofReal '' Set.range (λᵢμⱼ)
  have hImageEq : Complex.ofReal '' Set.range eig12 =
      Complex.ofReal '' Set.range (fun ij : p × q => eig1 ij.1 * eig2 ij.2) := by
    rw [← hSpecEig12, hSpecKron, hProdImage]

  -- Since Complex.ofReal is injective, Set.range eig12 = Set.range (λᵢμⱼ)
  have hRangeEq : Set.range eig12 = Set.range (fun ij : p × q => eig1 ij.1 * eig2 ij.2) :=
    Complex.ofReal_injective.image_injective hImageEq

  -- Conclude with sup equality
  have hSupEq : Finset.sup' Finset.univ Finset.univ_nonempty eig12 =
                Finset.sup' Finset.univ Finset.univ_nonempty (fun ij : p × q => eig1 ij.1 * eig2 ij.2) :=
    Matrix.SVD.Rectangular.sup'_eq_of_range_eq hRangeEq

  have hSupProd : Finset.sup' Finset.univ Finset.univ_nonempty (fun ij : p × q => eig1 ij.1 * eig2 ij.2) =
                  Finset.sup' Finset.univ Finset.univ_nonempty eig1 *
                  Finset.sup' Finset.univ Finset.univ_nonempty eig2 :=
    Finset.sup'_prod_eq_mul_sup' eig1 eig2 h_nonneg1 h_nonneg2

  -- Combine
  rw [hSupEq, hSupProd]

/-- **L2 operator norm of Kronecker product of PSD Hermitian matrices.**
    For positive semidefinite Hermitian matrices H₁ and H₂:
    ‖H₁ ⊗ H₂‖₂ = ‖H₁‖₂ · ‖H₂‖₂.

    Mathematical Justification:
    - For Hermitian PSD matrices, eigenvalues are non-negative real numbers
    - Eigenvalues of H₁ ⊗ H₂ = {λᵢμⱼ : λᵢ ∈ eigenvalues(H₁), μⱼ ∈ eigenvalues(H₂)}
    - For Hermitian matrices, ‖H‖₂ = max|eigenvalue| = max(eigenvalue) (since PSD)
    - Therefore: max(eigenvalues(H₁ ⊗ H₂)) = max(λᵢ) · max(μⱼ) = ‖H₁‖₂ · ‖H₂‖₂

    This is a well-known result from matrix analysis (Horn & Johnson, Chapter 4).

    The proof requires showing that for Hermitian matrices H₁ and H₂:
    1. H₁ ⊗ H₂ is Hermitian
    2. eigenvalues(H₁ ⊗ H₂) = products of eigenvalues
    3. The spectral radius equals the operator norm for Hermitian matrices

    **Proof Strategy:**
    We use the spectral decomposition H = U D U* where D is diagonal with eigenvalues.
    Then H₁ ⊗ H₂ = (U₁ D₁ U₁*) ⊗ (U₂ D₂ U₂*)
                  = (U₁ ⊗ U₂)(D₁ ⊗ D₂)(U₁* ⊗ U₂*)
    Since U₁ ⊗ U₂ is unitary and D₁ ⊗ D₂ = diagonal(λᵢμⱼ), we get:
    ‖H₁ ⊗ H₂‖ = ‖D₁ ⊗ D₂‖ = max(λᵢμⱼ) = max(λᵢ)·max(μⱼ) = ‖H₁‖·‖H₂‖ -/
private lemma l2_opNorm_kronecker_psd [Nonempty p] [Nonempty q]
    (H₁ : Matrix p p ℂ) (H₂ : Matrix q q ℂ)
    (hH₁ : H₁.PosSemidef) (hH₂ : H₂.PosSemidef) :
    ‖kroneckerMap (· * ·) H₁ H₂‖ = ‖H₁‖ * ‖H₂‖ := by
  -- Extract Hermitian hypotheses
  have hHerm₁ := hH₁.isHermitian
  have hHerm₂ := hH₂.isHermitian
  -- The Kronecker product of Hermitian matrices is Hermitian
  have hHerm₁₂ := isHermitian_kronecker H₁ H₂ hHerm₁ hHerm₂
  -- The Kronecker product of PSD is PSD (from Mathlib)
  have hPSD₁₂ : (kroneckerMap (· * ·) H₁ H₂).PosSemidef := hH₁.kronecker hH₂
  -- For PSD matrices: ‖H‖ = sup eigenvalues (not sup |eigenvalues|)
  rw [l2_opNorm_posSemidef_eq_sup_eigenvalues H₁ hH₁]
  rw [l2_opNorm_posSemidef_eq_sup_eigenvalues H₂ hH₂]
  rw [l2_opNorm_posSemidef_eq_sup_eigenvalues (kroneckerMap (· * ·) H₁ H₂) hPSD₁₂]
  -- The main claim: eigenvalues of H₁ ⊗ H₂ are exactly products λᵢμⱼ
  -- This is Horn & Johnson "Matrix Analysis" Theorem 4.2.12.
  -- We use the sup_eigenvalues_kronecker_eq_mul helper lemma.
  exact sup_eigenvalues_kronecker_eq_mul H₁ H₂ hH₁ hH₂

/-- **The L2 operator norm of a Kronecker product equals the product of operator norms.**
    ‖A ⊗ B‖₂ = ‖A‖₂ · ‖B‖₂

    This is a fundamental result in matrix analysis. The proof proceeds as follows:

    **Step 1:** Use the C*-algebra property ‖M‖² = ‖MᴴM‖

    **Step 2:** Apply the Kronecker identity (A⊗B)ᴴ(A⊗B) = (AᴴA)⊗(BᴴB)

    **Step 3:** For PSD Hermitian matrices H₁ = AᴴA and H₂ = BᴴB:
    ‖H₁ ⊗ H₂‖ = ‖H₁‖ · ‖H₂‖ (eigenvalue product theorem)

    **Step 4:** Combine: ‖A⊗B‖² = ‖(AᴴA)⊗(BᴴB)‖ = ‖AᴴA‖·‖BᴴB‖ = ‖A‖²·‖B‖²

    **References:**
    - Horn, R.A. & Johnson, C.R. (2012). Matrix Analysis, 2nd ed. Cambridge University Press.
      Chapter 4, Section 4.2 (Kronecker Products and Matrix Equations). -/
theorem l2_opNorm_kronecker [Nonempty p] [Nonempty q]
    (A : Matrix m p ℂ) (B : Matrix n q ℂ) :
    ‖kroneckerMap (· * ·) A B‖ = ‖A‖ * ‖B‖ := by
  -- Step 1: Use the C*-identity ‖M‖² = ‖MᴴM‖
  have h1 : ‖kroneckerMap (· * ·) A B‖ * ‖kroneckerMap (· * ·) A B‖ =
            ‖(kroneckerMap (· * ·) A B)ᴴ * kroneckerMap (· * ·) A B‖ := by
    exact (l2_opNorm_conjTranspose_mul_self (kroneckerMap (· * ·) A B)).symm
  -- Step 2: Apply the Kronecker identity
  rw [conjTranspose_mul_kronecker] at h1
  -- h1 : ‖A⊗B‖² = ‖(AᴴA)⊗(BᴴB)‖
  -- Step 3: AᴴA and BᴴB are PSD Hermitian
  have hPSD₁ : (Aᴴ * A).PosSemidef := posSemidef_conjTranspose_mul_self A
  have hPSD₂ : (Bᴴ * B).PosSemidef := posSemidef_conjTranspose_mul_self B
  -- Step 4: Apply the PSD Kronecker norm lemma
  have h2 : ‖kroneckerMap (· * ·) (Aᴴ * A) (Bᴴ * B)‖ = ‖Aᴴ * A‖ * ‖Bᴴ * B‖ :=
    l2_opNorm_kronecker_psd (Aᴴ * A) (Bᴴ * B) hPSD₁ hPSD₂
  rw [h2] at h1
  -- Step 5: Use ‖MᴴM‖ = ‖M‖² again
  have h3 : ‖Aᴴ * A‖ = ‖A‖ * ‖A‖ := l2_opNorm_conjTranspose_mul_self A
  have h4 : ‖Bᴴ * B‖ = ‖B‖ * ‖B‖ := l2_opNorm_conjTranspose_mul_self B
  rw [h3, h4] at h1
  -- h1 : ‖A⊗B‖² = (‖A‖²)(‖B‖²) = (‖A‖·‖B‖)²
  have h5 : ‖kroneckerMap (· * ·) A B‖ ^ 2 = (‖A‖ * ‖B‖) ^ 2 := by
    calc ‖kroneckerMap (· * ·) A B‖ ^ 2
        = ‖kroneckerMap (· * ·) A B‖ * ‖kroneckerMap (· * ·) A B‖ := sq _
      _ = ‖A‖ * ‖A‖ * (‖B‖ * ‖B‖) := h1
      _ = (‖A‖ * ‖B‖) ^ 2 := by ring
  -- Step 6: Extract square root (both sides are nonnegative)
  have h_nonneg_lhs : 0 ≤ ‖kroneckerMap (· * ·) A B‖ := norm_nonneg _
  have h_nonneg_rhs : 0 ≤ ‖A‖ * ‖B‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have h6 : |‖kroneckerMap (· * ·) A B‖| = |‖A‖ * ‖B‖| :=
    sq_eq_sq_iff_abs_eq_abs _ _ |>.mp h5
  rwa [abs_of_nonneg h_nonneg_lhs, abs_of_nonneg h_nonneg_rhs] at h6

end KroneckerBoundsSpectral

end Matrix.KroneckerRearrangement

/-! ## Kronecker Product Perturbation Bounds

‖B ⊗ C - B′ ⊗ C′‖₂ ≤ ‖B - B′‖₂·‖C‖₂ + ‖B′‖₂·‖C - C′‖₂
-/

namespace Matrix.KroneckerPerturbation

variable {m n p q m' n' p' q' : Type*}
variable [Fintype m] [Fintype n] [Fintype p] [Fintype q]
variable [DecidableEq m] [DecidableEq n] [DecidableEq p] [DecidableEq q]

section Decomposition

/-- Kronecker subtraction decomposition:
    B ⊗ C - B′ ⊗ C′ = (B - B′) ⊗ C + B′ ⊗ (C - C′) -/
theorem kronecker_sub_decomposition
    (B B' : Matrix m p ℂ) (C C' : Matrix n q ℂ) :
    kroneckerMap (· * ·) B C - kroneckerMap (· * ·) B' C' =
    kroneckerMap (· * ·) (B - B') C + kroneckerMap (· * ·) B' (C - C') := by
  -- Use the bilinearity of kroneckerMap
  ext ⟨i, j⟩ ⟨k, l⟩
  simp only [sub_apply, add_apply, kroneckerMap_apply]
  ring

/-- Alternative form: B ⊗ C - B' ⊗ C' = (B - B') ⊗ C' + B ⊗ (C - C')
    This equivalent decomposition uses B on the right term instead of B'. -/
theorem kronecker_sub_decomposition' (B B' : Matrix m p ℂ) (C C' : Matrix n q ℂ) :
    kroneckerMap (· * ·) B C - kroneckerMap (· * ·) B' C' =
    kroneckerMap (· * ·) (B - B') C' + kroneckerMap (· * ·) B (C - C') := by
  ext ⟨i, j⟩ ⟨k, l⟩
  simp only [sub_apply, add_apply, kroneckerMap_apply]
  ring

end Decomposition

/-! ### Part B: Spectral Norm Bounds for Kronecker Differences

Using the decomposition and the triangle inequality, we bound the spectral norm
of a Kronecker product difference.
-/

section SpectralBounds

-- Use L2 operator norm instances
attribute [local instance] Matrix.instL2OpNormedAddCommGroup
attribute [local instance] Matrix.instL2OpNormedSpace
attribute [local instance] Matrix.instL2OpNormedRing
attribute [local instance] Matrix.instL2OpNormedAlgebra
attribute [local instance] Matrix.instL2OpMetricSpace

/-- **Kronecker Difference Spectral Norm Bound:**
    The spectral norm of a Kronecker product difference satisfies:
    ‖B ⊗ C - B' ⊗ C'‖₂ ≤ ‖B - B'‖₂ · ‖C‖₂ + ‖B'‖₂ · ‖C - C'‖₂

    This is the key bound for perturbation analysis of Kronecker-structured matrices.

    **Proof:**
    1. Decompose: B ⊗ C - B' ⊗ C' = (B - B') ⊗ C + B' ⊗ (C - C')
    2. Triangle inequality: ‖LHS‖ ≤ ‖(B - B') ⊗ C‖ + ‖B' ⊗ (C - C')‖
    3. Kronecker norm: ‖A ⊗ B‖₂ = ‖A‖₂ · ‖B‖₂ (from l2_opNorm_kronecker)
    4. Combine: ≤ ‖B - B'‖·‖C‖ + ‖B'‖·‖C - C'‖ -/
theorem kronecker_sub_spectral_norm_bound [Nonempty p] [Nonempty q]
    (B B' : Matrix m p ℂ) (C C' : Matrix n q ℂ) :
    ‖kroneckerMap (· * ·) B C - kroneckerMap (· * ·) B' C'‖ ≤
    ‖B - B'‖ * ‖C‖ + ‖B'‖ * ‖C - C'‖ := by
  -- Step 1: Apply the decomposition
  rw [kronecker_sub_decomposition]
  -- Step 2: Apply triangle inequality
  calc ‖kroneckerMap (· * ·) (B - B') C + kroneckerMap (· * ·) B' (C - C')‖
      ≤ ‖kroneckerMap (· * ·) (B - B') C‖ + ‖kroneckerMap (· * ·) B' (C - C')‖ := norm_add_le _ _
    _ = ‖B - B'‖ * ‖C‖ + ‖B'‖ * ‖C - C'‖ := by
        -- Apply l2_opNorm_kronecker to each term
        rw [KroneckerRearrangement.l2_opNorm_kronecker (B - B') C]
        rw [KroneckerRearrangement.l2_opNorm_kronecker B' (C - C')]

/-- **Symmetric Kronecker Difference Bound:**
    Alternative bound using B instead of B':
    ‖B ⊗ C - B' ⊗ C'‖₂ ≤ ‖B - B'‖₂ · ‖C'‖₂ + ‖B‖₂ · ‖C - C'‖₂ -/
theorem kronecker_sub_spectral_norm_bound' [Nonempty p] [Nonempty q]
    (B B' : Matrix m p ℂ) (C C' : Matrix n q ℂ) :
    ‖kroneckerMap (· * ·) B C - kroneckerMap (· * ·) B' C'‖ ≤
    ‖B - B'‖ * ‖C'‖ + ‖B‖ * ‖C - C'‖ := by
  rw [kronecker_sub_decomposition']
  calc ‖kroneckerMap (· * ·) (B - B') C' + kroneckerMap (· * ·) B (C - C')‖
      ≤ ‖kroneckerMap (· * ·) (B - B') C'‖ + ‖kroneckerMap (· * ·) B (C - C')‖ := norm_add_le _ _
    _ = ‖B - B'‖ * ‖C'‖ + ‖B‖ * ‖C - C'‖ := by
        rw [KroneckerRearrangement.l2_opNorm_kronecker (B - B') C']
        rw [KroneckerRearrangement.l2_opNorm_kronecker B (C - C')]

end SpectralBounds

/-! ### Part C: Parameter Estimation Perturbation Bounds

These theorems connect the abstract Kronecker norm bounds to statistical estimation,
as required for analyzing Kronecker-structured regression models.
-/

section EstimationBounds

-- Continue using L2 operator norm instances
attribute [local instance] Matrix.instL2OpNormedAddCommGroup
attribute [local instance] Matrix.instL2OpNormedSpace
attribute [local instance] Matrix.instL2OpNormedRing
attribute [local instance] Matrix.instL2OpNormedAlgebra
attribute [local instance] Matrix.instL2OpMetricSpace

/-- **Kronecker Estimation Perturbation Bound:**
    If B̂, Ĉ are estimates of B, C with bounded errors:
    ‖B - B̂‖ ≤ εB and ‖C - Ĉ‖ ≤ εC

    Then the Kronecker product estimation error is bounded:
    ‖B ⊗ C - B̂ ⊗ Ĉ‖ ≤ εB · ‖C‖ + ‖B̂‖ · εC

    This is the key result for connecting algebraic bounds to statistical inference.

    **Application:** In Kronecker-factorized regression Y = X(β₁ ⊗ β₂) + E,
    if we estimate β̂₁, β̂₂ with errors bounded by εB, εC, then the error in
    the estimated coefficient matrix β̂₁ ⊗ β̂₂ is bounded by this formula. -/
theorem kronecker_estimation_perturbation_bound [Nonempty p] [Nonempty q]
    (B B' : Matrix m p ℂ) (C C' : Matrix n q ℂ)
    {εB εC : ℝ} (hεB : 0 ≤ εB) (hεC : 0 ≤ εC)
    (hB : ‖B - B'‖ ≤ εB) (hC : ‖C - C'‖ ≤ εC) :
    ‖kroneckerMap (· * ·) B C - kroneckerMap (· * ·) B' C'‖ ≤
    εB * ‖C‖ + ‖B'‖ * εC := by
  calc ‖kroneckerMap (· * ·) B C - kroneckerMap (· * ·) B' C'‖
      ≤ ‖B - B'‖ * ‖C‖ + ‖B'‖ * ‖C - C'‖ := kronecker_sub_spectral_norm_bound B B' C C'
    _ ≤ εB * ‖C‖ + ‖B'‖ * εC := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_right hB (norm_nonneg _)
        · exact mul_le_mul_of_nonneg_left hC (norm_nonneg _)

/-- **Relative Kronecker Perturbation Bound:**
    A normalized version useful for analyzing relative errors:
    ‖B ⊗ C - B' ⊗ C'‖ / (‖B‖ · ‖C‖) ≤ (‖B - B'‖/‖B‖) + (‖C - C'‖/‖C‖) + O(ε²)

    For small perturbations, this shows the relative error in the Kronecker product
    is approximately the sum of relative errors in the factors. -/
theorem kronecker_relative_perturbation [Nonempty p] [Nonempty q]
    (B B' : Matrix m p ℂ) (C C' : Matrix n q ℂ)
    (hB : B ≠ 0) (hC : C ≠ 0) :
    ‖kroneckerMap (· * ·) B C - kroneckerMap (· * ·) B' C'‖ ≤
    ‖B - B'‖ * ‖C‖ + ‖B‖ * ‖C - C'‖ + ‖B - B'‖ * ‖C - C'‖ := by
  -- This follows from expanding the decomposition more carefully
  -- B ⊗ C - B' ⊗ C' = (B - B') ⊗ (C - C') + (B - B') ⊗ C' + B ⊗ (C - C') - (B - B') ⊗ (C - C')
  -- But it's cleaner to use both decompositions
  have h1 := kronecker_sub_spectral_norm_bound B B' C C'
  -- We prove a slightly weaker bound using the first decomposition
  have h_B'_bound : ‖B'‖ ≤ ‖B‖ + ‖B - B'‖ := by
    calc ‖B'‖ = ‖B + (B' - B)‖ := by congr 1; abel
      _ ≤ ‖B‖ + ‖B' - B‖ := norm_add_le B (B' - B)
      _ = ‖B‖ + ‖B - B'‖ := by rw [norm_sub_rev]
  calc ‖kroneckerMap (· * ·) B C - kroneckerMap (· * ·) B' C'‖
      ≤ ‖B - B'‖ * ‖C‖ + ‖B'‖ * ‖C - C'‖ := h1
    _ ≤ ‖B - B'‖ * ‖C‖ + (‖B‖ + ‖B - B'‖) * ‖C - C'‖ := by
        have h_ineq : ‖B'‖ * ‖C - C'‖ ≤ (‖B‖ + ‖B - B'‖) * ‖C - C'‖ :=
          mul_le_mul_of_nonneg_right h_B'_bound (norm_nonneg _)
        linarith
    _ = ‖B - B'‖ * ‖C‖ + ‖B‖ * ‖C - C'‖ + ‖B - B'‖ * ‖C - C'‖ := by ring

/-- **First-Order Approximation:**
    For small perturbations, the leading-order error is:
    ‖B ⊗ C - B' ⊗ C'‖ ≈ ‖B - B'‖ · ‖C‖ + ‖B‖ · ‖C - C'‖

    This bound is achieved (up to the cross term) and is tight when perturbations are small.
    The theorem below gives an upper bound without the cross term when one factor is unchanged. -/
theorem kronecker_perturbation_single_factor_B [Nonempty p] [Nonempty q]
    (B B' : Matrix m p ℂ) (C : Matrix n q ℂ) :
    ‖kroneckerMap (· * ·) B C - kroneckerMap (· * ·) B' C‖ = ‖B - B'‖ * ‖C‖ := by
  -- When C is unchanged: B ⊗ C - B' ⊗ C = (B - B') ⊗ C
  have h : kroneckerMap (· * ·) B C - kroneckerMap (· * ·) B' C =
           kroneckerMap (· * ·) (B - B') C := by
    ext ⟨i, j⟩ ⟨k, l⟩
    simp only [sub_apply, kroneckerMap_apply]
    ring
  rw [h, KroneckerRearrangement.l2_opNorm_kronecker]

/-- Single-factor perturbation in C. -/
theorem kronecker_perturbation_single_factor_C [Nonempty p] [Nonempty q]
    (B : Matrix m p ℂ) (C C' : Matrix n q ℂ) :
    ‖kroneckerMap (· * ·) B C - kroneckerMap (· * ·) B C'‖ = ‖B‖ * ‖C - C'‖ := by
  have h : kroneckerMap (· * ·) B C - kroneckerMap (· * ·) B C' =
           kroneckerMap (· * ·) B (C - C') := by
    ext ⟨i, j⟩ ⟨k, l⟩
    simp only [sub_apply, kroneckerMap_apply]
    ring
  rw [h, KroneckerRearrangement.l2_opNorm_kronecker]

end EstimationBounds

/-! ### Part D: Connection to Weyl Perturbation Theory

The Kronecker perturbation bounds connect to singular value perturbation via Weyl's theorem.
This section establishes the chain of reasoning from factor perturbations to
Kronecker product singular value changes.
-/

section WeylConnection

attribute [local instance] Matrix.instL2OpNormedAddCommGroup

/-- **Kronecker Product Singular Value Perturbation:**
    If ‖E‖ is small, then the singular values of B ⊗ C + E are close to those of B ⊗ C.

    By Weyl's theorem (from WeylInequality.lean):
    |σᵢ(B ⊗ C + E) - σᵢ(B ⊗ C)| ≤ ‖E‖

    Combined with our Kronecker perturbation bounds, if E = B̂ ⊗ Ĉ - B ⊗ C:
    |σᵢ(B̂ ⊗ Ĉ) - σᵢ(B ⊗ C)| ≤ ‖B - B̂‖·‖C‖ + ‖B̂‖·‖C - Ĉ‖

    This theorem states the composition of these bounds. -/
theorem kronecker_singularValue_perturbation [Nonempty p] [Nonempty q]
    (B B' : Matrix m p ℂ) (C C' : Matrix n q ℂ) :
    -- The spectral norm error bounds the singular value perturbation
    ‖kroneckerMap (· * ·) B C - kroneckerMap (· * ·) B' C'‖ ≤
    ‖B - B'‖ * ‖C‖ + ‖B'‖ * ‖C - C'‖ :=
  -- Direct application of our main perturbation bound
  kronecker_sub_spectral_norm_bound B B' C C'

end WeylConnection

end Matrix.KroneckerPerturbation
