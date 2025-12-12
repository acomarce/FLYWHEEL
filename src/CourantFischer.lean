/-
Copyright (c) 2025 FLYWHEEL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aleksandar Markovski
-/
import Mathlib
import SVD

/-!
# Courant-Fischer Min-Max Theorem

λₖ(A) = max_{dim V = k} min_{x ∈ V, ‖x‖=1} R(A,x) = min_{dim W = n-k+1} max_{x ∈ W, ‖x‖=1} R(A,x)

## References

[1] Courant, R. & Hilbert, D. (1924). Methoden der Mathematischen Physik.
[2] Fischer, E. (1908). Über quadratische Formen mit reellen Koeffizienten.
[3] Horn & Johnson (2012), Thm 4.2.11.

## TODO
- [ ] Generalize to normal matrices (not just Hermitian)?
- [ ] The min-max direction is done, still need max-min formulation
- [ ] Consider refactoring eigenspace_span_finrank - it's getting long
-/

-- HACK: importing all of Mathlib is slow, but I kept getting random missing lemmas
-- when trying to import specific files. Fix later.

open scoped Matrix ComplexOrder
open Finset Matrix BigOperators

variable {n : Type*} [DecidableEq n] [Fintype n] [Nonempty n]

namespace CourantFischer

section SubspaceDimensionTools

variable {K : Type*} [DivisionRing K]
variable {E : Type*} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

-- NOTE(amarkovski): I'm not 100% sure if we need FiniteDimensional instances here
-- or if they can be inferred. Leaving explicit for now.

-- Old attempt that didn't work:
-- theorem subspace_intersection_nontrivial' (V W : Submodule K E) ... := by
--   apply Submodule.ne_bot_iff.mpr
--   -- stuck here, couldn't figure out how to extract witness

/-- If two finite-dimensional subspaces have dimensions summing to more than the
ambient space, their intersection is nontrivial. -/
theorem subspace_intersection_nontrivial
    (V W : Submodule K E) [FiniteDimensional K V] [FiniteDimensional K W]
    (hdim : Module.finrank K V + Module.finrank K W > Module.finrank K E) :
    V ⊓ W ≠ ⊥ := by
  intro h_eq_bot
  have h_inf_zero : Module.finrank K ↥(V ⊓ W) = 0 := by
    rw [h_eq_bot]
    exact finrank_bot K E
  have h_grassmann := Submodule.finrank_sup_add_finrank_inf_eq V W
  have h_sup_le : Module.finrank K ↥(V ⊔ W) ≤ Module.finrank K E :=
    Submodule.finrank_le (V ⊔ W)
  rw [h_inf_zero, add_zero] at h_grassmann
  omega

/-- Extract a nonzero element from the intersection. -/
theorem exists_nonzero_in_intersection
    (V W : Submodule K E) [FiniteDimensional K V] [FiniteDimensional K W]
    (hdim : Module.finrank K V + Module.finrank K W > Module.finrank K E) :
    ∃ x : E, x ≠ 0 ∧ x ∈ V ∧ x ∈ W := by
  have h_ne_bot : V ⊓ W ≠ ⊥ := subspace_intersection_nontrivial V W hdim
  obtain ⟨x, hx_mem, hx_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h_ne_bot
  rw [Submodule.mem_inf] at hx_mem
  exact ⟨x, hx_ne, hx_mem.1, hx_mem.2⟩

/-- The dimension of the intersection satisfies the Grassmann bound. -/
theorem finrank_inf_ge_of_sum_gt
    (V W : Submodule K E) [FiniteDimensional K V] [FiniteDimensional K W]
    (hdim : Module.finrank K V + Module.finrank K W > Module.finrank K E) :
    Module.finrank K ↥(V ⊓ W) ≥ Module.finrank K V + Module.finrank K W - Module.finrank K E := by
  have h_grassmann := Submodule.finrank_sup_add_finrank_inf_eq V W
  have h_sup_le : Module.finrank K ↥(V ⊔ W) ≤ Module.finrank K E :=
    Submodule.finrank_le (V ⊔ W)
  omega

end SubspaceDimensionTools

section EigenspaceDimension

variable {n : Type*} [DecidableEq n] [Fintype n]

/-- The span of the first k eigenvectors has dimension min(k, n). -/
theorem eigenspace_span_finrank (A : Matrix n n ℂ) (hA : A.IsHermitian) (k : ℕ) :
    ∃ (V : Submodule ℂ (EuclideanSpace ℂ n)), Module.finrank ℂ V = min k (Fintype.card n) := by
  have h_finrank_ambient : Module.finrank ℂ (EuclideanSpace ℂ n) = Fintype.card n :=
    finrank_euclideanSpace
  by_cases hk : k ≤ Fintype.card n
  · let basis := hA.eigenvectorBasis
    let equiv := Fintype.equivFin n
    let vectors : Fin k → EuclideanSpace ℂ n := fun i =>
      basis (equiv.symm (Fin.castLE hk i))
    use Submodule.span ℂ (Set.range vectors)
    have h_orthonormal : Orthonormal ℂ basis := basis.orthonormal
    have h_li : LinearIndependent ℂ vectors := by
      apply h_orthonormal.linearIndependent.comp
      intro i j hij
      simp only [Equiv.apply_eq_iff_eq, Fin.castLE_inj] at hij
      exact hij
    rw [finrank_span_eq_card h_li, Fintype.card_fin, Nat.min_eq_left hk]
  · push_neg at hk
    use ⊤
    rw [finrank_top, h_finrank_ambient, Nat.min_eq_right (le_of_lt hk)]

/-- For k ≤ n, there exists a k-dimensional subspace spanned by the first k eigenvectors. -/
theorem exists_eigenspace_of_dim (A : Matrix n n ℂ) (hA : A.IsHermitian) (k : ℕ)
    (hk : k ≤ Fintype.card n) :
    ∃ (V : Submodule ℂ (EuclideanSpace ℂ n)), Module.finrank ℂ V = k := by
  obtain ⟨V, hV⟩ := eigenspace_span_finrank A hA k
  use V
  simp only [Nat.min_eq_left hk] at hV
  exact hV

end EigenspaceDimension

-- Rayleigh quotient R(x) = ⟨Ax, x⟩ / ‖x‖², central to eigenvalue charaterization
section RayleighQuotient

section RayleighQuotient

variable {n : Type*} [DecidableEq n] [Fintype n] [Nonempty n]

/-! ### Core Identity: Rayleigh quotient as weighted sum of eigenvalues -/

omit [Nonempty n] in
/-- The inner product of Ax with x equals the eigenvalue-weighted sum of squared coefficients
in the eigenbasis expansion.

Mathematical statement:
  ⟨Ax, x⟩ = ∑ᵢ |⟨uᵢ, x⟩|² · λᵢ  where {uᵢ} is the eigenbasis
-/
theorem inner_toEuclideanLin_eq_eigenvalue_sum
    (A : Matrix n n ℂ) (hA : A.IsHermitian) (x : EuclideanSpace ℂ n) :
    @inner ℂ (EuclideanSpace ℂ n) _ (Matrix.toEuclideanLin A x) x =
      ∑ i, (↑(‖@inner ℂ (EuclideanSpace ℂ n) _ (hA.eigenvectorBasis i) x‖ ^ 2) : ℂ) * hA.eigenvalues i := by
  -- Use Parseval's identity: ⟨Ax, x⟩ = ∑ᵢ ⟨Ax, uᵢ⟩ * ⟨uᵢ, x⟩
  rw [← hA.eigenvectorBasis.sum_inner_mul_inner (Matrix.toEuclideanLin A x) x]
  apply Finset.sum_congr rfl
  intro i _
  -- Goal: ⟨Ax, uᵢ⟩ * ⟨uᵢ, x⟩ = |⟨uᵢ, x⟩|² * λᵢ
  -- Use the symmetric property: ⟨Ax, uᵢ⟩ = ⟨x, Auᵢ⟩ = ⟨x, λᵢuᵢ⟩ = λᵢ⟨x, uᵢ⟩
  have hSym : (Matrix.toEuclideanLin A).IsSymmetric := isHermitian_iff_isSymmetric.mp hA
  -- A uᵢ = λᵢ uᵢ
  have hEigen : Matrix.toEuclideanLin A (hA.eigenvectorBasis i) =
      (hA.eigenvalues i : ℂ) • (hA.eigenvectorBasis i) := by
    ext j
    have := hA.mulVec_eigenvectorBasis i
    simp only [Matrix.toEuclideanLin_apply] at this ⊢
    exact congr_fun this j
  -- ⟨Ax, uᵢ⟩ = conj(⟨uᵢ, Ax⟩) = conj(⟨Auᵢ, x⟩) = conj(⟨λᵢuᵢ, x⟩) = conj(λᵢ) * conj(⟨uᵢ, x⟩)
  -- Since λᵢ is real: = λᵢ * ⟨x, uᵢ⟩
  calc @inner ℂ (EuclideanSpace ℂ n) _ (Matrix.toEuclideanLin A x) (hA.eigenvectorBasis i) *
        @inner ℂ (EuclideanSpace ℂ n) _ (hA.eigenvectorBasis i) x
      = starRingEnd ℂ (@inner ℂ (EuclideanSpace ℂ n) _ (hA.eigenvectorBasis i) (Matrix.toEuclideanLin A x)) *
        @inner ℂ (EuclideanSpace ℂ n) _ (hA.eigenvectorBasis i) x := by
          rw [inner_conj_symm]
    _ = starRingEnd ℂ (@inner ℂ (EuclideanSpace ℂ n) _ (Matrix.toEuclideanLin A (hA.eigenvectorBasis i)) x) *
        @inner ℂ (EuclideanSpace ℂ n) _ (hA.eigenvectorBasis i) x := by
          rw [hSym (hA.eigenvectorBasis i) x]
    _ = starRingEnd ℂ (@inner ℂ (EuclideanSpace ℂ n) _ ((hA.eigenvalues i : ℂ) • hA.eigenvectorBasis i) x) *
        @inner ℂ (EuclideanSpace ℂ n) _ (hA.eigenvectorBasis i) x := by
          rw [hEigen]
    _ = starRingEnd ℂ (starRingEnd ℂ (hA.eigenvalues i : ℂ) *
          @inner ℂ (EuclideanSpace ℂ n) _ (hA.eigenvectorBasis i) x) *
        @inner ℂ (EuclideanSpace ℂ n) _ (hA.eigenvectorBasis i) x := by
          rw [inner_smul_left]
    _ = (hA.eigenvalues i : ℂ) * starRingEnd ℂ (@inner ℂ (EuclideanSpace ℂ n) _ (hA.eigenvectorBasis i) x) *
        @inner ℂ (EuclideanSpace ℂ n) _ (hA.eigenvectorBasis i) x := by
          simp only [map_mul, Complex.conj_ofReal]
    _ = (hA.eigenvalues i : ℂ) * (starRingEnd ℂ (@inner ℂ (EuclideanSpace ℂ n) _ (hA.eigenvectorBasis i) x) *
        @inner ℂ (EuclideanSpace ℂ n) _ (hA.eigenvectorBasis i) x) := by ring
    _ = (hA.eigenvalues i : ℂ) * (Complex.normSq (@inner ℂ (EuclideanSpace ℂ n) _ (hA.eigenvectorBasis i) x)) := by
          rw [Complex.normSq_eq_conj_mul_self]
    _ = (hA.eigenvalues i : ℂ) * ↑(‖@inner ℂ (EuclideanSpace ℂ n) _ (hA.eigenvectorBasis i) x‖ ^ 2) := by
          rw [Complex.normSq_eq_norm_sq]
    _ = ↑(‖@inner ℂ (EuclideanSpace ℂ n) _ (hA.eigenvectorBasis i) x‖ ^ 2) * (hA.eigenvalues i : ℂ) := by ring

omit [Nonempty n] in
/-- The Rayleigh quotient on an eigenvector equals the corresponding eigenvalue.

R(uᵢ) = λᵢ for eigenvector uᵢ. -/
theorem rayleigh_eq_eigenvalue_on_eigenvector
    (A : Matrix n n ℂ) (hA : A.IsHermitian) (i : n) :
    let v := hA.eigenvectorBasis i
    (@inner ℂ (EuclideanSpace ℂ n) _ (Matrix.toEuclideanLin A v) v).re = hA.eigenvalues i := by
  intro v
  -- The eigenvector equation gives A*v = λ*v
  -- So ⟨Av, v⟩ = ⟨λv, v⟩ = λ⟨v, v⟩ = λ (since v is unit)
  have h_eigen : Matrix.toEuclideanLin A v = (hA.eigenvalues i : ℂ) • v := by
    have := hA.mulVec_eigenvectorBasis i
    ext j
    simp only [Matrix.toEuclideanLin_apply] at this ⊢
    exact congr_fun this j
  rw [h_eigen]
  simp only [inner_smul_left]
  have h_unit : ‖v‖ = 1 := hA.eigenvectorBasis.orthonormal.1 i
  rw [inner_self_eq_norm_sq_to_K, h_unit]
  simp only [Complex.conj_ofReal]; norm_num

omit [Nonempty n] in
/-- The Rayleigh quotient equals the eigenvalue-weighted sum of squared coefficients.

For a unit vector x: Re⟨Ax, x⟩ = ∑ᵢ |⟨uᵢ, x⟩|² · λᵢ -/
theorem rayleigh_eq_eigenvalue_weighted_sum
    (A : Matrix n n ℂ) (hA : A.IsHermitian) (x : EuclideanSpace ℂ n) (_hx : ‖x‖ = 1) :
    (@inner ℂ (EuclideanSpace ℂ n) _ (Matrix.toEuclideanLin A x) x).re =
      ∑ i, ‖@inner ℂ (EuclideanSpace ℂ n) _ (hA.eigenvectorBasis i) x‖ ^ 2 * hA.eigenvalues i := by
  have h := inner_toEuclideanLin_eq_eigenvalue_sum A hA x
  rw [h, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  -- Goal: (↑‖...‖ ^ 2 * ↑eigenvalues i).re = ‖...‖ ^ 2 * eigenvalues i
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.ofReal_re]

omit [Nonempty n] in
/-- Parseval's identity: sum of squared inner products with eigenbasis equals squared norm. -/
theorem eigencoeff_sum_eq_norm_sq
    (A : Matrix n n ℂ) (hA : A.IsHermitian) (x : EuclideanSpace ℂ n) :
    ∑ i, ‖@inner ℂ (EuclideanSpace ℂ n) _ (hA.eigenvectorBasis i) x‖ ^ 2 = ‖x‖ ^ 2 :=
  hA.eigenvectorBasis.sum_sq_norm_inner_right x

omit [Nonempty n] in
/-- For a unit vector, the eigencoefficients sum to 1. -/
theorem eigencoeff_sum_eq_one
    (A : Matrix n n ℂ) (hA : A.IsHermitian) (x : EuclideanSpace ℂ n) (hx : ‖x‖ = 1) :
    ∑ i, ‖@inner ℂ (EuclideanSpace ℂ n) _ (hA.eigenvectorBasis i) x‖ ^ 2 = 1 := by
  rw [eigencoeff_sum_eq_norm_sq A hA x, hx, one_pow]

omit [Nonempty n] in
/-- The eigencoefficients are non-negative. -/
theorem eigencoeff_nonneg (A : Matrix n n ℂ) (hA : A.IsHermitian)
    (x : EuclideanSpace ℂ n) (i : n) :
    0 ≤ ‖@inner ℂ (EuclideanSpace ℂ n) _ (hA.eigenvectorBasis i) x‖ ^ 2 := sq_nonneg _

/-! ### Rayleigh Quotient Bounds -/

omit [Nonempty n] in
/-- Helper: eigenvalues i = eigenvalues₀ composed with the canonical equivalence.
This relates the two indexing schemes: eigenvalues : n → ℝ and eigenvalues₀ : Fin (card n) → ℝ.
Both produce the same sorted eigenvalues. -/
theorem eigenvalues_eq_eigenvalues₀_comp
    (A : Matrix n n ℂ) (hA : A.IsHermitian) (i : n) :
    hA.eigenvalues i = hA.eigenvalues₀ ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm i) :=
  Matrix.IsHermitian.eigenvalues.eq_1 hA i

/-- The Rayleigh quotient is bounded above by the largest eigenvalue.

For a unit vector x: Re⟨Ax, x⟩ ≤ λ_max -/
theorem rayleigh_le_eigenvalue_max
    (A : Matrix n n ℂ) (hA : A.IsHermitian) (x : EuclideanSpace ℂ n) (hx : ‖x‖ = 1) :
    (@inner ℂ (EuclideanSpace ℂ n) _ (Matrix.toEuclideanLin A x) x).re ≤ hA.eigenvalues₀ 0 := by
  rw [rayleigh_eq_eigenvalue_weighted_sum A hA x hx]
  have h_sum_one := eigencoeff_sum_eq_one A hA x hx
  -- eigenvalues₀ is sorted in descending order, so eigenvalues₀ 0 is the maximum
  have h_le : ∀ i, hA.eigenvalues i ≤ hA.eigenvalues₀ 0 := by
    intro i
    have h_mono := hA.eigenvalues₀_antitone
    rw [eigenvalues_eq_eigenvalues₀_comp A hA i]
    exact h_mono (Fin.zero_le _)
  calc ∑ i, ‖@inner ℂ (EuclideanSpace ℂ n) _ (hA.eigenvectorBasis i) x‖ ^ 2 * hA.eigenvalues i
      ≤ ∑ i, ‖@inner ℂ (EuclideanSpace ℂ n) _ (hA.eigenvectorBasis i) x‖ ^ 2 * hA.eigenvalues₀ 0 := by
        apply Finset.sum_le_sum
        intro i _
        apply mul_le_mul_of_nonneg_left (h_le i) (eigencoeff_nonneg A hA x i)
    _ = (∑ i, ‖@inner ℂ (EuclideanSpace ℂ n) _ (hA.eigenvectorBasis i) x‖ ^ 2) * hA.eigenvalues₀ 0 := by
        rw [Finset.sum_mul]
    _ = 1 * hA.eigenvalues₀ 0 := by rw [h_sum_one]
    _ = hA.eigenvalues₀ 0 := one_mul _

/-- The Rayleigh quotient is bounded below by the smallest eigenvalue.

For a unit vector x: Re⟨Ax, x⟩ ≥ λ_min -/
theorem rayleigh_ge_eigenvalue_min
    (A : Matrix n n ℂ) (hA : A.IsHermitian) (x : EuclideanSpace ℂ n) (hx : ‖x‖ = 1) :
    (@inner ℂ (EuclideanSpace ℂ n) _ (Matrix.toEuclideanLin A x) x).re ≥
      hA.eigenvalues₀ ⟨Fintype.card n - 1, Nat.sub_lt (Fintype.card_pos) Nat.one_pos⟩ := by
  rw [rayleigh_eq_eigenvalue_weighted_sum A hA x hx]
  have h_sum_one := eigencoeff_sum_eq_one A hA x hx
  let n_last : Fin (Fintype.card n) := ⟨Fintype.card n - 1, Nat.sub_lt (Fintype.card_pos) Nat.one_pos⟩
  have h_ge : ∀ i, hA.eigenvalues i ≥ hA.eigenvalues₀ n_last := by
    intro i
    have h_mono := hA.eigenvalues₀_antitone
    rw [eigenvalues_eq_eigenvalues₀_comp A hA i]
    have h_le : (Fintype.equivOfCardEq (Fintype.card_fin _)).symm i ≤ n_last :=
      Fin.mk_le_mk.mpr (Nat.le_sub_one_of_lt ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm i).isLt)
    exact h_mono h_le
  calc ∑ i, ‖@inner ℂ (EuclideanSpace ℂ n) _ (hA.eigenvectorBasis i) x‖ ^ 2 * hA.eigenvalues i
      ≥ ∑ i, ‖@inner ℂ (EuclideanSpace ℂ n) _ (hA.eigenvectorBasis i) x‖ ^ 2 * hA.eigenvalues₀ n_last := by
        apply Finset.sum_le_sum
        intro i _
        apply mul_le_mul_of_nonneg_left (h_ge i) (eigencoeff_nonneg A hA x i)
    _ = (∑ i, ‖@inner ℂ (EuclideanSpace ℂ n) _ (hA.eigenvectorBasis i) x‖ ^ 2) * hA.eigenvalues₀ n_last := by
        rw [Finset.sum_mul]
    _ = 1 * hA.eigenvalues₀ n_last := by rw [h_sum_one]
    _ = hA.eigenvalues₀ n_last := one_mul _

/-! ### Achievability -/

/-- The Rayleigh quotient achieves its maximum λ_max on the corresponding eigenvector. -/
theorem rayleigh_achieves_max (A : Matrix n n ℂ) (hA : A.IsHermitian) :
    let v := hA.eigenvectorBasis ((Fintype.equivOfCardEq (Fintype.card_fin _)) 0)
    (@inner ℂ (EuclideanSpace ℂ n) _ (Matrix.toEuclideanLin A v) v).re = hA.eigenvalues₀ 0 := by
  intro v
  have h_eigen_eq : hA.eigenvalues ((Fintype.equivOfCardEq (Fintype.card_fin _)) 0) = hA.eigenvalues₀ 0 := by
    rw [eigenvalues_eq_eigenvalues₀_comp A hA]
    simp only [Equiv.symm_apply_apply]
  rw [rayleigh_eq_eigenvalue_on_eigenvector A hA _, h_eigen_eq]

/-- The Rayleigh quotient achieves its minimum λ_min on the corresponding eigenvector. -/
theorem rayleigh_achieves_min (A : Matrix n n ℂ) (hA : A.IsHermitian) :
    let n_last : Fin (Fintype.card n) := ⟨Fintype.card n - 1, Nat.sub_lt Fintype.card_pos Nat.one_pos⟩
    let v := hA.eigenvectorBasis ((Fintype.equivOfCardEq (Fintype.card_fin _)) n_last)
    (@inner ℂ (EuclideanSpace ℂ n) _ (Matrix.toEuclideanLin A v) v).re = hA.eigenvalues₀ n_last := by
  intro n_last v
  have h_eigen_eq : hA.eigenvalues ((Fintype.equivOfCardEq (Fintype.card_fin _)) n_last) = hA.eigenvalues₀ n_last := by
    rw [eigenvalues_eq_eigenvalues₀_comp A hA]
    simp only [Equiv.symm_apply_apply]
  rw [rayleigh_eq_eigenvalue_on_eigenvector A hA _, h_eigen_eq]

/-! ### Subspace-Restricted Bounds -/

/-- The span of a subset of eigenvectors. -/
def eigenvectorSpan (hA : Matrix.IsHermitian (A : Matrix n n ℂ))
    (S : Finset n) : Submodule ℂ (EuclideanSpace ℂ n) :=
  Submodule.span ℂ (Set.range (fun i : S => hA.eigenvectorBasis i.val))

/-- The span of the first k eigenvectors (in sorted eigenvalue order). -/
def eigenvectorSpanHead (hA : Matrix.IsHermitian (A : Matrix n n ℂ))
    (k : Fin (Fintype.card n + 1)) : Submodule ℂ (EuclideanSpace ℂ n) :=
  Submodule.span ℂ (Set.range (fun i : Fin k =>
    hA.eigenvectorBasis ((Fintype.equivOfCardEq (Fintype.card_fin _)) (Fin.castLE (Nat.lt_succ_iff.mp k.isLt) i))))

/-- The span of eigenvectors from index k to n-1 (tail of sorted order). -/
def eigenvectorSpanTail (hA : Matrix.IsHermitian (A : Matrix n n ℂ))
    (k : Fin (Fintype.card n)) : Submodule ℂ (EuclideanSpace ℂ n) :=
  Submodule.span ℂ (Set.range (fun i : Fin (Fintype.card n - k) =>
    hA.eigenvectorBasis ((Fintype.equivOfCardEq (Fintype.card_fin _)) ⟨k + i, by omega⟩)))

omit [Nonempty n] in
/-- A head eigenvector (index < k) is orthogonal to any vector in the tail span. -/
theorem inner_eigenvectorHead_eigenvectorSpanTail_eq_zero
    (A : Matrix n n ℂ) (hA : A.IsHermitian) (k : Fin (Fintype.card n))
    (j : n) (hj : (Fintype.equivOfCardEq (Fintype.card_fin _)).symm j < k)
    (x : EuclideanSpace ℂ n) (hx : x ∈ eigenvectorSpanTail hA k) :
    @inner ℂ (EuclideanSpace ℂ n) _ (hA.eigenvectorBasis j) x = 0 := by
  have hOrtho := hA.eigenvectorBasis.orthonormal
  -- Inner product with each generator is zero by orthonormality
  have hOrthGen : ∀ m : Fin (Fintype.card n - k),
      @inner ℂ (EuclideanSpace ℂ n) _ (hA.eigenvectorBasis j)
        (hA.eigenvectorBasis ((Fintype.equivOfCardEq (Fintype.card_fin _)) ⟨k + m, by omega⟩)) = 0 := by
    intro m
    apply hOrtho.inner_eq_zero
    intro heq
    have h1 : (Fintype.equivOfCardEq (Fintype.card_fin _)).symm j = ⟨k + m, by omega⟩ := by
      rw [heq]; simp only [Equiv.symm_apply_apply]
    rw [h1] at hj
    simp only [Fin.lt_def] at hj
    omega
  -- Extend to span by linearity
  unfold eigenvectorSpanTail at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    simp only [Set.mem_range] at hy
    obtain ⟨m, rfl⟩ := hy
    exact hOrthGen m
  | zero => exact inner_zero_right _
  | add _ _ _ _ iha ihb => rw [inner_add_right, iha, ihb, add_zero]
  | smul c _ _ ih => rw [inner_smul_right, ih, mul_zero]

omit [Nonempty n] in
/-- On the span of eigenvectors {uₖ, ..., uₙ₋₁}, the Rayleigh quotient is bounded above by λₖ. -/
theorem rayleigh_le_on_eigenvectorSpanTail
    (A : Matrix n n ℂ) (hA : A.IsHermitian) (k : Fin (Fintype.card n))
    (x : EuclideanSpace ℂ n) (hx : ‖x‖ = 1) (hspan : x ∈ eigenvectorSpanTail hA k) :
    (@inner ℂ (EuclideanSpace ℂ n) _ (Matrix.toEuclideanLin A x) x).re ≤ hA.eigenvalues₀ k := by
  -- For j in the head (index < k), ⟨uⱼ, x⟩ = 0 by orthogonality
  have h_head_zero : ∀ j : n,
      (Fintype.equivOfCardEq (Fintype.card_fin _)).symm j < k →
      @inner ℂ (EuclideanSpace ℂ n) _ (hA.eigenvectorBasis j) x = 0 :=
    fun j hj => inner_eigenvectorHead_eigenvectorSpanTail_eq_zero A hA k j hj x hspan

  -- Use the Rayleigh quotient formula: R(x) = ∑ᵢ |⟨uᵢ, x⟩|² λᵢ
  rw [rayleigh_eq_eigenvalue_weighted_sum A hA x hx]

  -- Now we bound the sum
  calc ∑ i, ‖@inner ℂ (EuclideanSpace ℂ n) _ (hA.eigenvectorBasis i) x‖ ^ 2 * hA.eigenvalues i
      ≤ ∑ i, ‖@inner ℂ (EuclideanSpace ℂ n) _ (hA.eigenvectorBasis i) x‖ ^ 2 * hA.eigenvalues₀ k := by
        apply Finset.sum_le_sum
        intro i _
        by_cases h : (Fintype.equivOfCardEq (Fintype.card_fin _)).symm i < k
        · -- Head case: coefficient is 0
          simp only [h_head_zero i h, norm_zero, sq, zero_mul, mul_zero, le_refl]
        · -- Tail case: eigenvalue ≤ λₖ
          apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
          push_neg at h
          rw [eigenvalues_eq_eigenvalues₀_comp A hA i]
          exact hA.eigenvalues₀_antitone h
    _ = (∑ i, ‖@inner ℂ (EuclideanSpace ℂ n) _ (hA.eigenvectorBasis i) x‖ ^ 2) * hA.eigenvalues₀ k := by
        rw [Finset.sum_mul]
    _ = 1 * hA.eigenvalues₀ k := by
        rw [eigencoeff_sum_eq_one A hA x hx]
    _ = hA.eigenvalues₀ k := one_mul _

omit [Nonempty n] in
/-- A tail eigenvector (index ≥ k) is orthogonal to any vector in the head span. -/
theorem inner_eigenvectorTail_eigenvectorSpanHead_eq_zero
    (A : Matrix n n ℂ) (hA : A.IsHermitian) (k : Fin (Fintype.card n + 1))
    (j : n) (hj : ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm j).val ≥ k.val)
    (x : EuclideanSpace ℂ n) (hx : x ∈ eigenvectorSpanHead hA k) :
    @inner ℂ (EuclideanSpace ℂ n) _ (hA.eigenvectorBasis j) x = 0 := by
  have hOrtho := hA.eigenvectorBasis.orthonormal
  -- Inner product with each generator is zero by orthonormality
  have hOrthGen : ∀ m : Fin k,
      @inner ℂ (EuclideanSpace ℂ n) _ (hA.eigenvectorBasis j)
        (hA.eigenvectorBasis ((Fintype.equivOfCardEq (Fintype.card_fin _))
          (Fin.castLE (Nat.lt_succ_iff.mp k.isLt) m))) = 0 := by
    intro m
    apply hOrtho.inner_eq_zero
    intro heq
    -- From heq and hj, we get a contradiction
    have h1 : (Fintype.equivOfCardEq (Fintype.card_fin _)).symm j =
        Fin.castLE (Nat.lt_succ_iff.mp k.isLt) m := by
      rw [heq]; simp only [Equiv.symm_apply_apply]
    have h2 : ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm j).val = m.val := by
      rw [h1]; simp only [Fin.coe_castLE]
    omega
  -- Extend to span by linearity
  unfold eigenvectorSpanHead at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    simp only [Set.mem_range] at hy
    obtain ⟨m, rfl⟩ := hy
    exact hOrthGen m
  | zero => exact inner_zero_right _
  | add _ _ _ _ iha ihb => rw [inner_add_right, iha, ihb, add_zero]
  | smul c _ _ ih => rw [inner_smul_right, ih, mul_zero]

omit [Nonempty n] in
/-- On the span of eigenvectors {u₀, ..., uₖ₋₁}, the Rayleigh quotient is bounded below by λₖ₋₁. -/
theorem rayleigh_ge_on_eigenvectorSpanHead
    (A : Matrix n n ℂ) (hA : A.IsHermitian) (k : Fin (Fintype.card n + 1)) (hk : 0 < k)
    (x : EuclideanSpace ℂ n) (hx : ‖x‖ = 1) (hspan : x ∈ eigenvectorSpanHead hA k) :
    (@inner ℂ (EuclideanSpace ℂ n) _ (Matrix.toEuclideanLin A x) x).re ≥
      hA.eigenvalues₀ ⟨k - 1, by omega⟩ := by
  -- For j in the tail (index ≥ k), ⟨uⱼ, x⟩ = 0 by orthogonality
  have h_tail_zero : ∀ j : n,
      ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm j).val ≥ k.val →
      @inner ℂ (EuclideanSpace ℂ n) _ (hA.eigenvectorBasis j) x = 0 :=
    fun j hj => inner_eigenvectorTail_eigenvectorSpanHead_eq_zero A hA k j hj x hspan

  -- Use the Rayleigh quotient formula: R(x) = ∑ᵢ |⟨uᵢ, x⟩|² λᵢ
  rw [rayleigh_eq_eigenvalue_weighted_sum A hA x hx]

  -- For the lower bound, we use λₖ₋₁ since that's the smallest eigenvalue in the head
  let k_pred : Fin (Fintype.card n) := ⟨k.val - 1, by omega⟩

  -- Now we bound the sum from below
  calc ∑ i, ‖@inner ℂ (EuclideanSpace ℂ n) _ (hA.eigenvectorBasis i) x‖ ^ 2 * hA.eigenvalues i
      ≥ ∑ i, ‖@inner ℂ (EuclideanSpace ℂ n) _ (hA.eigenvectorBasis i) x‖ ^ 2 * hA.eigenvalues₀ k_pred := by
        apply Finset.sum_le_sum
        intro i _
        by_cases h : ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm i).val < k.val
        · -- Head case: eigenvalue ≥ λₖ₋₁ (since eigenvalues are decreasing and i < k means λᵢ ≥ λₖ₋₁)
          apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
          rw [eigenvalues_eq_eigenvalues₀_comp A hA i]
          apply hA.eigenvalues₀_antitone
          -- Goal: (equivOfCardEq _).symm i ≤ k_pred
          show ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm i) ≤ k_pred
          simp only [Fin.le_iff_val_le_val]
          -- Now goal is (symm i).val ≤ k_pred.val = k.val - 1
          -- We have h : (symm i).val < k.val and hk : k.val > 0
          have hk_pos : k.val > 0 := hk
          have : k_pred.val = k.val - 1 := rfl
          omega
        · -- Tail case: coefficient is 0
          have h' : ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm i).val ≥ k.val := by omega
          simp only [h_tail_zero i h', norm_zero, sq, zero_mul, mul_zero, le_refl]
    _ = (∑ i, ‖@inner ℂ (EuclideanSpace ℂ n) _ (hA.eigenvectorBasis i) x‖ ^ 2) * hA.eigenvalues₀ k_pred := by
        rw [Finset.sum_mul]
    _ = 1 * hA.eigenvalues₀ k_pred := by
        rw [eigencoeff_sum_eq_one A hA x hx]
    _ = hA.eigenvalues₀ ⟨k - 1, by omega⟩ := one_mul _

end RayleighQuotient

/-!
## Section 4: Courant-Fischer Min-Max

The Courant-Fischer theorem characterizes the k-th eigenvalue of a Hermitian matrix
as an optimization over k-dimensional subspaces.

**Max-Min Form:** λₖ₋₁ = max_{dim W = k} min_{x ∈ W, x ≠ 0} R(x)
**Min-Max Form:** λₖ₋₁ = min_{dim W = n-k+1} max_{x ∈ W, x ≠ 0} R(x)

where R(x) = Re⟨Ax, x⟩ / ‖x‖² is the Rayleigh quotient.
-/

section CourantFischerMain

variable {n : Type*} [DecidableEq n] [Fintype n] [Nonempty n]

/-! ### Definitions -/

/-- The type of k-dimensional subspaces of EuclideanSpace ℂ n. -/
def DimSubspace (n : ℕ) (k : ℕ) : Type :=
  { W : Submodule ℂ (EuclideanSpace ℂ (Fin n)) // Module.finrank ℂ W = k }

/-- The Rayleigh quotient R(x) = Re⟨Ax, x⟩ / ‖x‖². -/
noncomputable def rayleighQuotient (A : Matrix n n ℂ) (x : EuclideanSpace ℂ n) : ℝ :=
  (@inner ℂ (EuclideanSpace ℂ n) _ (Matrix.toEuclideanLin A x) x).re / ‖x‖^2

/-- The infimum of Rayleigh quotient over nonzero vectors in a subspace. -/
noncomputable def rayleighInf (A : Matrix n n ℂ) (_hA : A.IsHermitian)
    (W : Submodule ℂ (EuclideanSpace ℂ n)) : ℝ :=
  ⨅ x : { x : W // x.val ≠ 0 }, rayleighQuotient A x.val.val

/-- The supremum of Rayleigh quotient over nonzero vectors in a subspace. -/
noncomputable def rayleighSup (A : Matrix n n ℂ) (_hA : A.IsHermitian)
    (W : Submodule ℂ (EuclideanSpace ℂ n)) : ℝ :=
  ⨆ x : { x : W // x.val ≠ 0 }, rayleighQuotient A x.val.val

/-! ### Dimension Lemmas -/

/-- A subspace with positive finite rank contains nonzero vectors. -/
theorem exists_nonzero_of_finrank_pos {K : Type*} [DivisionRing K]
    {E : Type*} [AddCommGroup E] [Module K E]
    (W : Submodule K E) (h : 0 < Module.finrank K W) :
    ∃ x : W, x.val ≠ 0 := by
  by_contra hne
  push_neg at hne
  have : W = ⊥ := by
    ext x
    simp only [Submodule.mem_bot]
    constructor
    · intro hx
      exact hne ⟨x, hx⟩
    · intro hx
      rw [hx]
      exact W.zero_mem
  rw [this, finrank_bot K E] at h
  exact Nat.lt_irrefl 0 h

omit [Nonempty n] in
/-- The dimension of eigenvectorSpanHead equals k (when k ≤ n). -/
theorem finrank_eigenvectorSpanHead (A : Matrix n n ℂ) (hA : A.IsHermitian)
    (k : Fin (Fintype.card n + 1)) :
    Module.finrank ℂ (eigenvectorSpanHead hA k) = k.val := by
  -- Define the indexing function for the first k eigenvectors
  let f : Fin k → EuclideanSpace ℂ n := fun i =>
    hA.eigenvectorBasis ((Fintype.equivOfCardEq (Fintype.card_fin _))
      (Fin.castLE (Nat.lt_succ_iff.mp k.isLt) i))
  -- The span of f equals eigenvectorSpanHead by definition
  have h_span_eq : Submodule.span ℂ (Set.range f) = eigenvectorSpanHead hA k := by
    unfold eigenvectorSpanHead
    congr 1
  -- The function f is injective (it's a restriction of eigenvectorBasis composed with injective maps)
  have h_inj : Function.Injective f := by
    intro i j h
    simp only [f] at h
    have := hA.eigenvectorBasis.toBasis.injective h
    simp only [Equiv.apply_eq_iff_eq, Fin.castLE_inj] at this
    exact this
  -- The original eigenvector basis is orthonormal
  have h_ortho_basis := hA.eigenvectorBasis.orthonormal
  -- f is orthonormal by Orthonormal.comp (since it's a composition with injective function)
  have h_f_ortho : Orthonormal ℂ f := by
    apply Orthonormal.comp h_ortho_basis
    -- Need to show the composition function is injective
    intro i j h
    simp only at h
    have := Equiv.injective (Fintype.equivOfCardEq (Fintype.card_fin _)) h
    exact Fin.castLE_injective _ this
  -- Orthonormal implies linearly independent
  have h_li : LinearIndependent ℂ f := h_f_ortho.linearIndependent
  -- finrank of span = cardinality of index
  rw [← h_span_eq, finrank_span_eq_card h_li, Fintype.card_fin]

omit [Nonempty n] in
/-- The dimension of eigenvectorSpanTail equals n - k. -/
theorem finrank_eigenvectorSpanTail (A : Matrix n n ℂ) (hA : A.IsHermitian)
    (k : Fin (Fintype.card n)) :
    Module.finrank ℂ (eigenvectorSpanTail hA k) = Fintype.card n - k.val := by
  -- Define the indexing function for eigenvectors from k to n-1
  let f : Fin (Fintype.card n - k) → EuclideanSpace ℂ n := fun i =>
    hA.eigenvectorBasis ((Fintype.equivOfCardEq (Fintype.card_fin _)) ⟨k + i, by omega⟩)
  -- The span of f equals eigenvectorSpanTail by definition
  have h_span_eq : Submodule.span ℂ (Set.range f) = eigenvectorSpanTail hA k := by
    unfold eigenvectorSpanTail
    congr 1
  -- The function f is injective
  have h_inj : Function.Injective f := by
    intro i j h
    simp only [f] at h
    have := hA.eigenvectorBasis.toBasis.injective h
    simp only [Equiv.apply_eq_iff_eq, Fin.mk.injEq] at this
    exact Fin.ext (by omega : i.val = j.val)
  -- The original eigenvector basis is orthonormal
  have h_ortho_basis := hA.eigenvectorBasis.orthonormal
  -- f is orthonormal by Orthonormal.comp (since it's a composition with injective function)
  have h_f_ortho : Orthonormal ℂ f := by
    apply Orthonormal.comp h_ortho_basis
    -- Need to show the composition function is injective
    intro i j h
    simp only at h
    have := Equiv.injective (Fintype.equivOfCardEq (Fintype.card_fin _)) h
    simp only [Fin.mk.injEq] at this
    exact Fin.ext (by omega : i.val = j.val)
  -- Orthonormal implies linearly independent
  have h_li : LinearIndependent ℂ f := h_f_ortho.linearIndependent
  -- finrank of span = cardinality of index
  rw [← h_span_eq, finrank_span_eq_card h_li, Fintype.card_fin]

omit [Nonempty n] in
/-- The (k-1)-th eigenvector is in eigenvectorSpanHead k. -/
theorem eigenvector_mem_eigenvectorSpanHead (A : Matrix n n ℂ) (hA : A.IsHermitian)
    (k : Fin (Fintype.card n + 1)) (hk : 0 < k) :
    let k_pred : Fin (Fintype.card n) := ⟨k.val - 1, by omega⟩
    hA.eigenvectorBasis ((Fintype.equivOfCardEq (Fintype.card_fin _)) k_pred) ∈
      eigenvectorSpanHead hA k := by
  intro k_pred
  unfold eigenvectorSpanHead
  apply Submodule.subset_span
  simp only [Set.mem_range]
  use ⟨k.val - 1, by omega⟩
  congr 1

/-! ### Rayleigh Quotient on Unit Sphere -/

omit [Nonempty n] in
/-- Rayleigh quotient equals Re⟨Ax, x⟩ for unit vectors. -/
theorem rayleighQuotient_eq_inner_of_unit (A : Matrix n n ℂ) (x : EuclideanSpace ℂ n) (hx : ‖x‖ = 1) :
    rayleighQuotient A x = (@inner ℂ (EuclideanSpace ℂ n) _ (Matrix.toEuclideanLin A x) x).re := by
  unfold rayleighQuotient
  rw [hx, one_pow, div_one]

/-! ### Achievability: Eigenspace achieves the bound -/

omit [Nonempty n] in
/-- The (k-1)-th eigenvector achieves Rayleigh quotient λₖ₋₁ and is in eigenvectorSpanHead. -/
theorem rayleigh_achieves_on_eigenvectorSpanHead (A : Matrix n n ℂ) (hA : A.IsHermitian)
    (k : Fin (Fintype.card n + 1)) (hk : 0 < k) :
    let k_pred : Fin (Fintype.card n) := ⟨k.val - 1, by omega⟩
    let v := hA.eigenvectorBasis ((Fintype.equivOfCardEq (Fintype.card_fin _)) k_pred)
    v ∈ eigenvectorSpanHead hA k ∧
    (@inner ℂ (EuclideanSpace ℂ n) _ (Matrix.toEuclideanLin A v) v).re = hA.eigenvalues₀ k_pred := by
  intro k_pred v
  constructor
  · exact eigenvector_mem_eigenvectorSpanHead A hA k hk
  · -- v = u_{k-1} so R(v) = λ_{k-1}
    have h_eigen_eq : hA.eigenvalues ((Fintype.equivOfCardEq (Fintype.card_fin _)) k_pred) =
        hA.eigenvalues₀ k_pred := by
      rw [eigenvalues_eq_eigenvalues₀_comp A hA]
      simp only [Equiv.symm_apply_apply]
    rw [rayleigh_eq_eigenvalue_on_eigenvector A hA _, h_eigen_eq]

omit [Nonempty n] in
/-- On eigenvectorSpanHead k, the minimum Rayleigh quotient equals λₖ₋₁. -/
theorem rayleighInf_eigenvectorSpanHead_eq (A : Matrix n n ℂ) (hA : A.IsHermitian)
    (k : Fin (Fintype.card n + 1)) (hk : 0 < k) :
    ∃ x ∈ eigenvectorSpanHead hA k, x ≠ 0 ∧
      (@inner ℂ (EuclideanSpace ℂ n) _ (Matrix.toEuclideanLin A x) x).re / ‖x‖^2 =
        hA.eigenvalues₀ ⟨k.val - 1, by omega⟩ := by
  let k_pred : Fin (Fintype.card n) := ⟨k.val - 1, by omega⟩
  let v := hA.eigenvectorBasis ((Fintype.equivOfCardEq (Fintype.card_fin _)) k_pred)
  use v
  obtain ⟨hmem, hval⟩ := rayleigh_achieves_on_eigenvectorSpanHead A hA k hk
  refine ⟨hmem, ?_, ?_⟩
  · -- v ≠ 0 since it's a unit eigenvector
    have hunit : ‖v‖ = 1 := hA.eigenvectorBasis.orthonormal.1 _
    intro hzero
    rw [hzero, norm_zero] at hunit
    exact one_ne_zero hunit.symm
  · -- R(v) = λₖ₋₁
    have hunit : ‖v‖ = 1 := hA.eigenvectorBasis.orthonormal.1 _
    rw [hunit, one_pow, div_one]
    exact hval

/-! ### Intersection Argument -/

/-- Helper: Re(conj(c) * c * z) = ‖c‖^2 * Re(z) -/
theorem re_mul_conj_mul_self {z : ℂ} {c : ℂ} :
    (starRingEnd ℂ c * c * z).re = ‖c‖^2 * z.re := by
  have h1 : starRingEnd ℂ c * c = (Complex.normSq c : ℝ) := by
    rw [mul_comm, Complex.mul_conj]
  rw [h1, Complex.normSq_eq_norm_sq]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

/-- Helper: Re(z * c * conj(c)) = Re(z) * ‖c‖^2.
    This is useful when inner_smul operations produce (inner * c * conj(c)). -/
theorem re_mul_mul_conj_self {z : ℂ} {c : ℂ} :
    (z * c * starRingEnd ℂ c).re = z.re * ‖c‖^2 := by
  have h1 : c * starRingEnd ℂ c = (Complex.normSq c : ℝ) := Complex.mul_conj c
  rw [mul_assoc, h1, Complex.normSq_eq_norm_sq]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

omit [Nonempty n] in
/-- Helper for Rayleigh quotient scaling: For real scalar c ≠ 0,
    Re⟨A(c•x), c•x⟩ / ‖c•x‖² = Re⟨Ax, x⟩ / ‖x‖². -/
theorem rayleigh_scale_real {A : Matrix n n ℂ} {x : EuclideanSpace ℂ n}
    (hx : x ≠ 0) (c : ℝ) (hc : c ≠ 0) :
    (@inner ℂ (EuclideanSpace ℂ n) _ (Matrix.toEuclideanLin A ((c : ℂ) • x)) ((c : ℂ) • x)).re
      / ‖(c : ℂ) • x‖^2 =
    (@inner ℂ (EuclideanSpace ℂ n) _ (Matrix.toEuclideanLin A x) x).re / ‖x‖^2 := by
  simp only [map_smul, inner_smul_left, inner_smul_right, norm_smul, Complex.norm_real]
  -- Goal: (conj(c) * (c * inner)).re / (|c| * ‖x‖)^2 = inner.re / ‖x‖^2
  have h_conj_real : starRingEnd ℂ (c : ℂ) = (c : ℂ) := Complex.conj_ofReal c
  rw [h_conj_real]
  -- Now: ((c : ℂ) * ((c : ℂ) * inner)).re / (|c| * ‖x‖)^2 = inner.re / ‖x‖^2
  rw [← mul_assoc, ← Complex.ofReal_mul, mul_pow, Real.norm_eq_abs]
  -- Now: (↑(c * c) * inner).re / (|c|^2 * ‖x‖^2) = inner.re / ‖x‖^2
  rw [Complex.re_ofReal_mul]
  have h_c_sq : c * c = c^2 := sq c |>.symm
  rw [h_c_sq, sq_abs]
  have hx_norm_ne : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hc_sq_ne : c^2 ≠ 0 := pow_ne_zero 2 hc
  field_simp

omit [Nonempty n] in
/-- Helper for Rayleigh quotient scaling with complex scalar. -/
theorem rayleigh_scale_complex {A : Matrix n n ℂ} {x : EuclideanSpace ℂ n}
    (hx : x ≠ 0) (c : ℂ) (hc : c ≠ 0) :
    (@inner ℂ (EuclideanSpace ℂ n) _ (Matrix.toEuclideanLin A (c • x)) (c • x)).re / ‖c • x‖^2 =
    (@inner ℂ (EuclideanSpace ℂ n) _ (Matrix.toEuclideanLin A x) x).re / ‖x‖^2 := by
  simp only [map_smul, inner_smul_left, inner_smul_right, norm_smul]
  -- After inner_smul_left, inner_smul_right: goal becomes
  -- (c * conj(c) * inner).re / (‖c‖ * ‖x‖)^2 = inner.re / ‖x‖^2
  rw [← mul_assoc, mul_pow]
  -- Now: (c * conj(c) * inner).re / (‖c‖^2 * ‖x‖^2) = inner.re / ‖x‖^2
  -- c * conj(c) = ‖c‖^2 (as real)
  have h_conj_mul : c * starRingEnd ℂ c = (‖c‖^2 : ℝ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  -- So (c * conj(c) * inner).re = (‖c‖^2 * inner).re = ‖c‖^2 * inner.re
  have h_re : (c * starRingEnd ℂ c * @inner ℂ (EuclideanSpace ℂ n) _ (Matrix.toEuclideanLin A x) x).re =
      ‖c‖^2 * (@inner ℂ (EuclideanSpace ℂ n) _ (Matrix.toEuclideanLin A x) x).re := by
    rw [h_conj_mul]
    exact Complex.re_ofReal_mul _ _
  rw [h_re]
  have hx_norm_ne : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hc_norm_ne : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc
  have hc_norm_sq_ne : ‖c‖^2 ≠ 0 := pow_ne_zero 2 hc_norm_ne
  have hx_norm_sq_ne : ‖x‖^2 ≠ 0 := pow_ne_zero 2 hx_norm_ne
  field_simp

omit [Nonempty n] in
/-- Any k-dimensional subspace contains a nonzero vector with Rayleigh quotient ≤ λₖ₋₁. -/
theorem exists_vector_rayleigh_le_in_subspace (A : Matrix n n ℂ) (hA : A.IsHermitian)
    (k : Fin (Fintype.card n + 1)) (hk : 0 < k)
    (W : Submodule ℂ (EuclideanSpace ℂ n)) (hW : Module.finrank ℂ W = k.val) :
    ∃ x ∈ W, x ≠ 0 ∧
      (@inner ℂ (EuclideanSpace ℂ n) _ (Matrix.toEuclideanLin A x) x).re / ‖x‖^2 ≤
        hA.eigenvalues₀ ⟨k.val - 1, by omega⟩ := by
  -- Key dimension argument:
  -- W has dimension k
  -- eigenvectorSpanTail (k-1) has dimension n - (k-1) = n - k + 1
  -- Sum = k + (n - k + 1) = n + 1 > n
  -- So W ∩ Tail is nontrivial
  let k_pred : Fin (Fintype.card n) := ⟨k.val - 1, by omega⟩
  let Tail := eigenvectorSpanTail hA k_pred

  have hTail_dim : Module.finrank ℂ Tail = Fintype.card n - (k.val - 1) := by
    exact finrank_eigenvectorSpanTail A hA k_pred

  have h_ambient : Module.finrank ℂ (EuclideanSpace ℂ n) = Fintype.card n := finrank_euclideanSpace

  -- Dimension sum exceeds ambient
  have h_sum : Module.finrank ℂ W + Module.finrank ℂ Tail > Module.finrank ℂ (EuclideanSpace ℂ n) := by
    rw [hW, hTail_dim, h_ambient]
    omega

  -- Get nonzero vector in intersection
  obtain ⟨x, hx_ne, hx_W, hx_Tail⟩ := exists_nonzero_in_intersection W Tail h_sum

  use x, hx_W, hx_ne

  -- x ∈ Tail means R(x) ≤ λₖ₋₁
  have hx_unit_scaled : ∀ c : ℂ, c ≠ 0 →
      (@inner ℂ (EuclideanSpace ℂ n) _ (Matrix.toEuclideanLin A (c • x)) (c • x)).re / ‖c • x‖^2 =
      (@inner ℂ (EuclideanSpace ℂ n) _ (Matrix.toEuclideanLin A x) x).re / ‖x‖^2 := by
    intro c hc
    have hcx_ne : c • x ≠ 0 := by
      intro h
      rw [smul_eq_zero] at h
      cases h with
      | inl h => exact hc h
      | inr h => exact hx_ne h
    -- ⟨A(cx), cx⟩ = |c|² ⟨Ax, x⟩ and ‖cx‖² = |c|² ‖x‖²
    have hinner : @inner ℂ (EuclideanSpace ℂ n) _ (Matrix.toEuclideanLin A (c • x)) (c • x) =
        (starRingEnd ℂ c * c) • @inner ℂ (EuclideanSpace ℂ n) _ (Matrix.toEuclideanLin A x) x := by
      simp only [map_smul, inner_smul_left, inner_smul_right, smul_eq_mul]
      ring
    have hnorm : ‖c • x‖^2 = ‖c‖^2 * ‖x‖^2 := by
      rw [norm_smul, mul_pow]
    rw [hinner, hnorm]
    simp only [smul_eq_mul]
    -- Use re_mul_conj_mul_self: (starRingEnd ℂ c * c * z).re = ‖c‖^2 * z.re
    rw [re_mul_conj_mul_self]
    have h_normSq_pos : (0 : ℝ) < ‖c‖^2 := by
      apply sq_pos_of_pos
      rw [norm_pos_iff]
      exact hc
    have h_normx_pos : (0 : ℝ) < ‖x‖^2 := by
      apply sq_pos_of_pos
      rw [norm_pos_iff]
      exact hx_ne
    field_simp

  -- Normalize x to get a unit vector in Tail
  have hx_norm_pos : 0 < ‖x‖ := norm_pos_iff.mpr hx_ne
  let y := (1 / ‖x‖ : ℂ) • x
  have hy_unit : ‖y‖ = 1 := by
    simp only [y, norm_smul, one_div, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hx_norm_pos, inv_mul_cancel₀ (ne_of_gt hx_norm_pos)]

  -- y is still in Tail (submodule is closed under scalar mult)
  have hy_Tail : y ∈ Tail := Submodule.smul_mem Tail _ hx_Tail

  -- Derive Nonempty n from the fact that k > 0 implies Fintype.card n ≥ 1
  haveI : Nonempty n := by
    rw [← Fintype.card_pos_iff]
    omega

  -- Apply rayleigh_le_on_eigenvectorSpanTail to y
  have hy_rayleigh := rayleigh_le_on_eigenvectorSpanTail A hA k_pred y hy_unit hy_Tail

  -- R(y) = R(x) by scaling invariance
  have hR_eq : (@inner ℂ (EuclideanSpace ℂ n) _ (Matrix.toEuclideanLin A x) x).re / ‖x‖^2 =
      (@inner ℂ (EuclideanSpace ℂ n) _ (Matrix.toEuclideanLin A y) y).re := by
    -- y = (1/‖x‖) • x, and R(y) = R(x)/‖x‖² when ‖y‖ = 1
    have h_scale := hx_unit_scaled (1 / ‖x‖ : ℂ) (by
      simp only [one_div, ne_eq, inv_eq_zero, Complex.ofReal_eq_zero]
      exact ne_of_gt hx_norm_pos)
    simp only [y] at hy_unit ⊢
    rw [hy_unit, one_pow, div_one] at h_scale
    exact h_scale.symm

  rw [hR_eq]
  exact hy_rayleigh

/-! ### Courant-Fischer Main Theorems -/

/-- **Courant-Fischer Max-Min Theorem** (inequality direction ≤):
The k-th largest eigenvalue is an upper bound for the infimum Rayleigh quotient
on any k-dimensional subspace.

For any k-dimensional subspace W: min_{x ∈ W, x ≠ 0} R(x) ≤ λₖ₋₁ -/
theorem rayleighInf_le_eigenvalue (A : Matrix n n ℂ) (hA : A.IsHermitian)
    (k : Fin (Fintype.card n + 1)) (hk : 0 < k)
    (W : Submodule ℂ (EuclideanSpace ℂ n)) (hW : Module.finrank ℂ W = k.val) :
    rayleighInf A hA W ≤ hA.eigenvalues₀ ⟨k.val - 1, by omega⟩ := by
  -- By exists_vector_rayleigh_le_in_subspace, there exists x ∈ W with R(x) ≤ λₖ₋₁
  obtain ⟨x, hx_mem, hx_ne, hx_rayleigh⟩ := exists_vector_rayleigh_le_in_subspace A hA k hk W hW
  -- The infimum is ≤ any element, so rayleighInf ≤ R(x) ≤ λₖ₋₁
  unfold rayleighInf rayleighQuotient
  -- Construct the witness explicitly
  let witness : { v : W // v.val ≠ 0 } := ⟨⟨x, hx_mem⟩, hx_ne⟩
  refine ciInf_le_of_le ?bdd witness hx_rayleigh
  -- Boundedness: rayleigh quotient is bounded below by λ_min
  use hA.eigenvalues₀ ⟨Fintype.card n - 1, by omega⟩
  intro r ⟨y, hr⟩
  simp only at hr
  rw [← hr]
  -- y : { x : W // x.val ≠ 0 }, so y.val.val ≠ 0, hence ‖y.val.val‖ ≠ 0
  have hy : ‖y.val.val‖ ≠ 0 := norm_ne_zero_iff.mpr y.property
  have hy_pos : 0 < ‖y.val.val‖ := norm_pos_iff.mpr y.property
  let z := (1 / ‖y.val.val‖ : ℂ) • y.val.val
  have hz_unit : ‖z‖ = 1 := by
    simp only [z, norm_smul, one_div, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hy_pos, inv_mul_cancel₀ (ne_of_gt hy_pos)]
  have h_scale : (@inner ℂ (EuclideanSpace ℂ n) _ (Matrix.toEuclideanLin A y.val.val) y.val.val).re
      / ‖y.val.val‖^2 = (@inner ℂ (EuclideanSpace ℂ n) _ (Matrix.toEuclideanLin A z) z).re := by
    -- Use the rayleigh scaling helper
    have hy_ne : y.val.val ≠ 0 := y.property
    have hc_ne : (1 / ‖y.val.val‖ : ℂ) ≠ 0 := by
      simp only [one_div, ne_eq, inv_eq_zero, Complex.ofReal_eq_zero]
      exact ne_of_gt hy_pos
    have h := rayleigh_scale_complex (A := A) hy_ne (1 / ‖y.val.val‖ : ℂ) hc_ne
    simp only [z] at hz_unit ⊢
    rw [hz_unit, one_pow, div_one] at h
    exact h.symm
  rw [h_scale]
  exact rayleigh_ge_eigenvalue_min A hA z hz_unit

/-- Helper: Re((1 / r^2) * z) = Re(z) / r^2 for real r ≠ 0 -/
theorem re_mul_ofReal_one_div_sq {z : ℂ} {r : ℝ} (hr : r ≠ 0) :
    ((1 : ℂ) / (r^2 : ℝ) * z).re = z.re / r^2 := by
  have hr2_ne : r^2 ≠ 0 := pow_ne_zero 2 hr
  rw [one_div]
  -- Goal: ((↑(r ^ 2))⁻¹ * z).re = z.re / r ^ 2
  -- Use inv_ofReal (inverted): (↑r)⁻¹ = ↑(r⁻¹), so (↑(r^2))⁻¹ = ↑((r^2)⁻¹)
  rw [← Complex.ofReal_inv, Complex.re_ofReal_mul]
  rw [inv_eq_one_div, one_div_mul_eq_div]

omit [Nonempty n] in
/-- **Courant-Fischer Max-Min Theorem** (inequality direction ≥):
The eigenvalue λₖ₋₁ is achieved as the infimum on the span of first k eigenvectors. -/
theorem eigenvalue_le_rayleighInf_eigenvectorSpanHead (A : Matrix n n ℂ) (hA : A.IsHermitian)
    (k : Fin (Fintype.card n + 1)) (hk : 0 < k) :
    hA.eigenvalues₀ ⟨k.val - 1, by omega⟩ ≤ rayleighInf A hA (eigenvectorSpanHead hA k) := by
  -- Lower bound: rayleigh_ge_on_eigenvectorSpanHead shows R(x) ≥ λₖ₋₁ for all x in span
  unfold rayleighInf rayleighQuotient
  -- The span has positive dimension, so it contains nonzero vectors
  have hHead_dim : Module.finrank ℂ (eigenvectorSpanHead hA k) = k.val :=
    finrank_eigenvectorSpanHead A hA k
  have hHead_pos : 0 < Module.finrank ℂ (eigenvectorSpanHead hA k) := by
    rw [hHead_dim]; exact hk
  obtain ⟨⟨v, hv_mem⟩, hv_ne⟩ := exists_nonzero_of_finrank_pos (eigenvectorSpanHead hA k) hHead_pos
  haveI : Nonempty { x : (eigenvectorSpanHead hA k) // x.val ≠ 0 } := ⟨⟨⟨v, hv_mem⟩, hv_ne⟩⟩
  apply le_ciInf
  intro ⟨⟨x, hx_mem⟩, hx_ne⟩
  by_cases hx_norm : ‖x‖ = 0
  · exfalso; exact hx_ne (norm_eq_zero.mp hx_norm)
  · have hx_pos : 0 < ‖x‖ := norm_pos_iff.mpr (fun h => hx_ne h)
    -- Normalize x
    let y := (1 / ‖x‖ : ℂ) • x
    have hy_unit : ‖y‖ = 1 := by
      simp only [y, norm_smul, one_div, norm_inv]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx_pos, inv_mul_cancel₀ (ne_of_gt hx_pos)]
    have hy_mem : y ∈ eigenvectorSpanHead hA k := Submodule.smul_mem _ _ hx_mem
    have hy_rayleigh := rayleigh_ge_on_eigenvectorSpanHead A hA k hk y hy_unit hy_mem
    -- R(x) = R(y) by scaling
    have h_scale : (@inner ℂ (EuclideanSpace ℂ n) _ (Matrix.toEuclideanLin A x) x).re / ‖x‖^2 =
        (@inner ℂ (EuclideanSpace ℂ n) _ (Matrix.toEuclideanLin A y) y).re := by
      -- Use the rayleigh scaling helper
      have hx_ne' : x ≠ 0 := fun h => hx_ne h
      have hc_ne : (1 / ‖x‖ : ℂ) ≠ 0 := by
        simp only [one_div, ne_eq, inv_eq_zero, Complex.ofReal_eq_zero]
        exact ne_of_gt hx_pos
      have h := rayleigh_scale_complex (A := A) hx_ne' (1 / ‖x‖ : ℂ) hc_ne
      simp only [y] at hy_unit ⊢
      rw [hy_unit, one_pow, div_one] at h
      exact h.symm
    rw [h_scale]
    exact hy_rayleigh

/-- **Courant-Fischer Max-Min Theorem**: The k-th largest eigenvalue (λₖ₋₁ in 0-indexed sorted
order) equals the supremum over k-dimensional subspaces of the infimum Rayleigh quotient.

λₖ₋₁ = sup_{dim W = k} inf_{x ∈ W, x ≠ 0} Re⟨Ax, x⟩ / ‖x‖²

Note: This version states the key equalities and bounds. The full sup-inf characterization
requires additional infrastructure for conditional suprema. -/
theorem courantFischer_maxMin_bounds (A : Matrix n n ℂ) (hA : A.IsHermitian)
    (k : Fin (Fintype.card n + 1)) (hk : 0 < k) :
    -- The eigenspace achieves the bound
    rayleighInf A hA (eigenvectorSpanHead hA k) ≥ hA.eigenvalues₀ ⟨k.val - 1, by omega⟩ ∧
    -- And this is optimal (any k-dim subspace has inf ≤ λₖ₋₁)
    (∀ W : Submodule ℂ (EuclideanSpace ℂ n), Module.finrank ℂ W = k.val →
      (∃ x : W, x.val ≠ 0) → rayleighInf A hA W ≤ hA.eigenvalues₀ ⟨k.val - 1, by omega⟩) := by
  constructor
  · exact eigenvalue_le_rayleighInf_eigenvectorSpanHead A hA k hk
  · intro W hW _hW_nonempty
    exact rayleighInf_le_eigenvalue A hA k hk W hW

/-- **Courant-Fischer Min-Max Theorem** (inequality direction ≥):
For any (n-k+1)-dimensional subspace, the supremum Rayleigh quotient is ≥ λₖ₋₁. -/
theorem eigenvalue_le_rayleighSup (A : Matrix n n ℂ) (hA : A.IsHermitian)
    (k : Fin (Fintype.card n + 1)) (hk : 0 < k)
    (W : Submodule ℂ (EuclideanSpace ℂ n))
    (hW : Module.finrank ℂ W = Fintype.card n - k.val + 1) :
    hA.eigenvalues₀ ⟨k.val - 1, by omega⟩ ≤ rayleighSup A hA W := by
  -- Dual argument: W intersects eigenvectorSpanHead k nontrivially
  -- Any vector in the intersection has R(x) ≥ λₖ₋₁
  let Head := eigenvectorSpanHead hA k
  have hHead_dim : Module.finrank ℂ Head = k.val := finrank_eigenvectorSpanHead A hA k

  have h_ambient : Module.finrank ℂ (EuclideanSpace ℂ n) = Fintype.card n := finrank_euclideanSpace

  -- Dimension sum exceeds ambient: k + (n - k + 1) = n + 1 > n
  have h_sum : Module.finrank ℂ Head + Module.finrank ℂ W > Module.finrank ℂ (EuclideanSpace ℂ n) := by
    rw [hHead_dim, hW, h_ambient]
    omega

  -- Get nonzero vector in intersection
  obtain ⟨x, hx_ne, hx_Head, hx_W⟩ := exists_nonzero_in_intersection Head W h_sum

  -- x ∈ Head means R(x) ≥ λₖ₋₁
  have hx_norm_pos : 0 < ‖x‖ := norm_pos_iff.mpr hx_ne
  let y := (1 / ‖x‖ : ℂ) • x
  have hy_unit : ‖y‖ = 1 := by
    simp only [y, norm_smul, one_div, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hx_norm_pos, inv_mul_cancel₀ (ne_of_gt hx_norm_pos)]

  have hy_Head : y ∈ Head := Submodule.smul_mem Head _ hx_Head
  have hy_W : y ∈ W := Submodule.smul_mem W _ hx_W

  have hy_rayleigh := rayleigh_ge_on_eigenvectorSpanHead A hA k hk y hy_unit hy_Head

  -- rayleighSup ≥ R(y) ≥ λₖ₋₁
  unfold rayleighSup rayleighQuotient
  apply le_trans hy_rayleigh
  -- Construct the witness explicitly
  have hy_ne : y ≠ 0 := by
    intro h
    rw [h, norm_zero] at hy_unit
    exact zero_ne_one hy_unit
  let witness : { v : W // v.val ≠ 0 } := ⟨⟨y, hy_W⟩, hy_ne⟩
  have h_witness_norm : ‖(witness.val.val)‖ = 1 := hy_unit
  -- Prove boundedness
  have hBdd : BddAbove (Set.range fun (z : { v : W // v.val ≠ 0 }) =>
      (@inner ℂ (EuclideanSpace ℂ n) _ (Matrix.toEuclideanLin A z.val.val) z.val.val).re / ‖z.val.val‖^2) := by
    use hA.eigenvalues₀ 0
    intro r ⟨z, hr⟩
    rw [← hr]
    by_cases hz : ‖z.val.val‖ = 0
    · -- If ‖z.val.val‖ = 0, then z.val.val = 0, contradicting z : { x // x.val ≠ 0 }
      exfalso
      have : z.val.val = 0 := norm_eq_zero.mp hz
      exact z.property this
    · have hz_pos : 0 < ‖z.val.val‖ := norm_pos_iff.mpr (fun h => hz (by rw [h, norm_zero]))
      let w := (1 / ‖z.val.val‖ : ℂ) • z.val.val
      have hw_unit : ‖w‖ = 1 := by
        simp only [w, norm_smul, one_div, norm_inv, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hz_pos, inv_mul_cancel₀ (ne_of_gt hz_pos)]
      have h_scale : (@inner ℂ (EuclideanSpace ℂ n) _ (Matrix.toEuclideanLin A z.val.val) z.val.val).re
          / ‖z.val.val‖^2 = (@inner ℂ (EuclideanSpace ℂ n) _ (Matrix.toEuclideanLin A w) w).re := by
        -- Use the rayleigh scaling helper
        have hz_ne : z.val.val ≠ 0 := z.property
        have hc_ne : (1 / ‖z.val.val‖ : ℂ) ≠ 0 := by
          simp only [one_div, ne_eq, inv_eq_zero, Complex.ofReal_eq_zero]
          exact ne_of_gt hz_pos
        have h := rayleigh_scale_complex (A := A) hz_ne (1 / ‖z.val.val‖ : ℂ) hc_ne
        simp only [w] at hw_unit ⊢
        rw [hw_unit, one_pow, div_one] at h
        exact h.symm
      simp only []
      rw [h_scale]
      exact rayleigh_le_eigenvalue_max A hA w hw_unit
  -- Apply le_ciSup_of_le with explicit proof
  have hLe : (@inner ℂ (EuclideanSpace ℂ n) _ (Matrix.toEuclideanLin A y) y).re ≤
      (@inner ℂ (EuclideanSpace ℂ n) _ (Matrix.toEuclideanLin A witness.val.val) witness.val.val).re /
        ‖witness.val.val‖^2 := by
    rw [h_witness_norm, one_pow, div_one]
  exact le_ciSup_of_le hBdd witness hLe

omit [Nonempty n] in
/-- **Courant-Fischer Min-Max Theorem** (inequality direction ≤):
The tail eigenspace achieves the supremum = λₖ₋₁. -/
theorem rayleighSup_le_eigenvalue_eigenvectorSpanTail (A : Matrix n n ℂ) (hA : A.IsHermitian)
    (k : Fin (Fintype.card n + 1)) (hk : 0 < k) :
    let k_pred : Fin (Fintype.card n) := ⟨k.val - 1, by omega⟩
    rayleighSup A hA (eigenvectorSpanTail hA k_pred) ≤ hA.eigenvalues₀ k_pred := by
  intro k_pred
  unfold rayleighSup rayleighQuotient
  -- Need Nonempty for ciSup_le
  have h_dim : Module.finrank ℂ (eigenvectorSpanTail hA k_pred) = Fintype.card n - k_pred.val := by
    exact finrank_eigenvectorSpanTail A hA k_pred
  have h_dim_pos : 0 < Module.finrank ℂ (eigenvectorSpanTail hA k_pred) := by
    rw [h_dim]; omega
  have hTail_ne_bot : eigenvectorSpanTail hA k_pred ≠ ⊥ := by
    rwa [← Submodule.one_le_finrank_iff, Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero]
  obtain ⟨v, hv_mem, hv_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hTail_ne_bot
  haveI : Nonempty { x : (eigenvectorSpanTail hA k_pred) // (x : EuclideanSpace ℂ n) ≠ 0 } := ⟨⟨⟨v, hv_mem⟩, hv_ne⟩⟩
  apply ciSup_le
  intro ⟨⟨x, hx_mem⟩, hx_ne⟩
  by_cases hx_norm : ‖x‖ = 0
  · exfalso; exact hx_ne (norm_eq_zero.mp hx_norm)
  · have hx_pos : 0 < ‖x‖ := norm_pos_iff.mpr (fun h => hx_ne h)
    let y := (1 / ‖x‖ : ℂ) • x
    have hy_unit : ‖y‖ = 1 := by
      simp only [y, norm_smul, one_div, norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hx_pos, inv_mul_cancel₀ (ne_of_gt hx_pos)]
    have hy_mem : y ∈ eigenvectorSpanTail hA k_pred := Submodule.smul_mem _ _ hx_mem
    have hy_rayleigh := rayleigh_le_on_eigenvectorSpanTail A hA k_pred y hy_unit hy_mem
    -- R(x) = R(y) by scaling
    have h_scale : (@inner ℂ (EuclideanSpace ℂ n) _ (Matrix.toEuclideanLin A x) x).re / ‖x‖^2 =
        (@inner ℂ (EuclideanSpace ℂ n) _ (Matrix.toEuclideanLin A y) y).re := by
      -- Use the rayleigh scaling helper
      have hx_ne' : x ≠ 0 := fun h => hx_ne h
      have hc_ne : (1 / ‖x‖ : ℂ) ≠ 0 := by
        simp only [one_div, ne_eq, inv_eq_zero, Complex.ofReal_eq_zero]
        exact ne_of_gt hx_pos
      have h := rayleigh_scale_complex (A := A) hx_ne' (1 / ‖x‖ : ℂ) hc_ne
      simp only [y] at hy_unit ⊢
      rw [hy_unit, one_pow, div_one] at h
      exact h.symm
    rw [h_scale]
    exact hy_rayleigh

/-- **Courant-Fischer Min-Max Theorem**: Combined bounds statement.

λₖ₋₁ = inf_{dim W = n-k+1} sup_{x ∈ W, x ≠ 0} Re⟨Ax, x⟩ / ‖x‖² -/
theorem courantFischer_minMax_bounds (A : Matrix n n ℂ) (hA : A.IsHermitian)
    (k : Fin (Fintype.card n + 1)) (hk : 0 < k) (_hk' : k.val < Fintype.card n + 1) :
    -- The tail eigenspace achieves the bound
    let k_pred : Fin (Fintype.card n) := ⟨k.val - 1, by omega⟩
    rayleighSup A hA (eigenvectorSpanTail hA k_pred) ≤ hA.eigenvalues₀ k_pred ∧
    -- And this is optimal (any (n-k+1)-dim subspace has sup ≥ λₖ₋₁)
    (∀ W : Submodule ℂ (EuclideanSpace ℂ n),
      Module.finrank ℂ W = Fintype.card n - k.val + 1 →
      (∃ x : W, x.val ≠ 0) → hA.eigenvalues₀ k_pred ≤ rayleighSup A hA W) := by
  constructor
  · exact rayleighSup_le_eigenvalue_eigenvectorSpanTail A hA k hk
  · intro W hW _hW_nonempty
    exact eigenvalue_le_rayleighSup A hA k hk W hW

end CourantFischerMain

/-!
## Section 5: Application to Eckart-Young
-/

/-! ### Application to Eckart-Young

**IMPORTANT BUG NOTE (2025-12-07):**

The original `eckartYoungCoreLemma` stated:
  ∑ᵢ (tail σᵢ)² ≤ ∑ᵢ |σᵢ - Cᵢᵢ|²  for any rank-k matrix C

This is MATHEMATICALLY FALSE. Counterexample:
- n = 2, k = 1, A = diag(2,1), C = [[2,1],[2,1]]
- C has rank 1 and diagonal (2,1) = σ
- LHS = 1, RHS = 0, so 1 ≤ 0 is FALSE

The fundamental error: A rank-k matrix can have ALL diagonal entries nonzero
(unlike diagonal rank-k matrices which have at most k nonzero diagonal entries).

The Eckart-Young theorem IS TRUE, but requires using the FULL Frobenius norm
(including off-diagonal terms), not just diagonal deviations.

See `docs/SVD/EckartYoung-BugReport.md` for details.

The code below includes useful lemmas for the correct proof approach.
-/

section EckartYoungBridge

variable {n : Type*} [DecidableEq n] [Fintype n] [Nonempty n]

/-! ### Singular Value - Eigenvalue Connection -/

omit [Nonempty n] in
/-- The k-th sorted singular value squared equals the k-th sorted eigenvalue of AᴴA.
    This is the fundamental bridge between SVD and Courant-Fischer. -/
theorem singularValue₀_sq_eq_eigenvalue₀ (A : Matrix n n ℂ) (k : Fin (Fintype.card n)) :
    (Matrix.SVD.singularValues₀ A k)^2 =
      (posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues₀ k := by
  exact Matrix.SVD.singularValues₀_sq A k

/-! ### Rayleigh Quotient on AᴴA -/

omit [Nonempty n] in
/-- For unit vectors in the tail eigenvector span of AᴴA, the Rayleigh quotient
    is bounded by the k-th eigenvalue. This translates to ‖Ax‖² ≤ σₖ². -/
theorem rayleigh_AHA_tail_bound (A : Matrix n n ℂ) (k : Fin (Fintype.card n))
    (x : EuclideanSpace ℂ n) (hx_unit : ‖x‖ = 1) :
    let hAHA := (posSemidef_conjTranspose_mul_self A).isHermitian
    x ∈ eigenvectorSpanTail hAHA k →
      (@inner ℂ (EuclideanSpace ℂ n) _ (Matrix.toEuclideanLin (Aᴴ * A) x) x).re ≤
        hAHA.eigenvalues₀ k := by
  intro hAHA hx_tail
  exact rayleigh_le_on_eigenvectorSpanTail (Aᴴ * A) hAHA k x hx_unit hx_tail

omit [Nonempty n] in
/-- The squared norm ‖Ax‖² equals Re⟨AᴴAx, x⟩ for any vector x.
    This connects the SVD energy to the Rayleigh quotient of AᴴA. -/
theorem norm_sq_mul_eq_inner_AHA (A : Matrix n n ℂ) (x : EuclideanSpace ℂ n) :
    ‖(Matrix.toEuclideanLin A) x‖^2 =
      (@inner ℂ (EuclideanSpace ℂ n) _ (Matrix.toEuclideanLin (Aᴴ * A) x) x).re := by
  -- Step 1: ‖Ax‖² = Re⟨Ax, Ax⟩
  have h1 : ‖(Matrix.toEuclideanLin A) x‖^2 =
      (@inner ℂ (EuclideanSpace ℂ n) _ ((Matrix.toEuclideanLin A) x) ((Matrix.toEuclideanLin A) x)).re := by
    have := @inner_self_eq_norm_sq ℂ (EuclideanSpace ℂ n) _ _ _ ((Matrix.toEuclideanLin A) x)
    simp only [RCLike.re_to_complex] at this
    exact this.symm
  rw [h1]
  -- Step 2: Use adjoint: ⟨Ax, Ax⟩ = ⟨AᴴAx, x⟩
  -- The adjoint of toEuclideanLin A is toEuclideanLin Aᴴ
  have h_adj : Matrix.toEuclideanLin Aᴴ = LinearMap.adjoint (Matrix.toEuclideanLin A) :=
    Matrix.toEuclideanLin_conjTranspose_eq_adjoint A
  -- ⟨Ax, Ax⟩ = ⟨Aᴴ(Ax), x⟩ by adjoint property
  have h2 : @inner ℂ (EuclideanSpace ℂ n) _ ((Matrix.toEuclideanLin A) x) ((Matrix.toEuclideanLin A) x) =
      @inner ℂ (EuclideanSpace ℂ n) _ (Matrix.toEuclideanLin (Aᴴ * A) x) x := by
    rw [← LinearMap.adjoint_inner_left (Matrix.toEuclideanLin A) x ((Matrix.toEuclideanLin A) x)]
    rw [← h_adj]
    -- Need to show: toEuclideanLin Aᴴ (toEuclideanLin A x) = toEuclideanLin (Aᴴ * A) x
    congr 1
    -- Use the fact that toEuclideanLin preserves matrix multiplication
    simp only [Matrix.toEuclideanLin_apply, Matrix.mulVec_mulVec]
  rw [h2]

/-! ### Dimension Counting Lemmas -/

omit [Nonempty n] in
/-- The tail eigenvector span has dimension n - k.
    This follows from eigenvectorSpanTail being the span of n - k orthonormal vectors. -/
theorem tail_span_dim (A : Matrix n n ℂ) (k : Fin (Fintype.card n)) :
    let hAHA := (posSemidef_conjTranspose_mul_self A).isHermitian
    Module.finrank ℂ (eigenvectorSpanTail hAHA k) = Fintype.card n - k.val := by
  intro hAHA
  exact finrank_eigenvectorSpanTail (Aᴴ * A) hAHA k

omit [Nonempty n] in
/-- The kernel of C.toEuclideanLin has dimension at least n - rank(C).
    This follows from rank-nullity: finrank(range) + finrank(ker) = n.
    Note: We use toEuclideanLin (not mulVecLin) to get a submodule of EuclideanSpace ℂ n. -/
private lemma finrank_ker_toEuclideanLin_ge (C : Matrix n n ℂ) :
    Module.finrank ℂ (LinearMap.ker (Matrix.toEuclideanLin C)) ≥ Fintype.card n - C.rank := by
  -- rank = finrank(range), so finrank(ker) = n - rank
  have h_rn := LinearMap.finrank_range_add_finrank_ker (Matrix.toEuclideanLin C)
  -- finrank domain = Fintype.card n for EuclideanSpace ℂ n
  have h_domain : Module.finrank ℂ (EuclideanSpace ℂ n) = Fintype.card n :=
    finrank_euclideanSpace
  rw [h_domain] at h_rn
  -- rank C = finrank range C.toEuclideanLin
  -- The key insight: Matrix.rank is defined via mulVecLin, but toEuclideanLin
  -- is just mulVecLin composed with the WithLp equivalence, so their ranges
  -- have the same dimension.
  have h_rank_def : C.rank = Module.finrank ℂ (LinearMap.range (Matrix.toEuclideanLin C)) := by
    unfold Matrix.rank
    -- We need to show: finrank (range mulVecLin) = finrank (range toEuclideanLin)
    -- toEuclideanLin C = WithLp.toLp ∘ mulVecLin C ∘ WithLp.ofLp
    -- Since WithLp.toLp and WithLp.ofLp are bijective, the ranges have the same dimension
    have h_range_finrank :
        Module.finrank ℂ (LinearMap.range C.mulVecLin) =
        Module.finrank ℂ (LinearMap.range (Matrix.toEuclideanLin C)) := by
      -- Let e : (n → ℂ) ≃ₗ[ℂ] EuclideanSpace ℂ n
      let e : (n → ℂ) ≃ₗ[ℂ] EuclideanSpace ℂ n := (WithLp.linearEquiv 2 ℂ (n → ℂ)).symm
      -- Key relationship: toEuclideanLin C = e ∘ mulVecLin C ∘ e.symm
      have h_eq : ∀ v : EuclideanSpace ℂ n,
          Matrix.toEuclideanLin C v = e (C.mulVecLin (e.symm v)) := by
        intro v
        simp only [Matrix.toEuclideanLin_apply, Matrix.mulVecLin_apply, e]
        simp only [LinearEquiv.symm_symm, WithLp.linearEquiv_apply]
        rfl
      -- Range of toEuclideanLin C = map e (range mulVecLin C)
      have h_range : LinearMap.range (Matrix.toEuclideanLin C) =
          Submodule.map e.toLinearMap (LinearMap.range C.mulVecLin) := by
        ext x
        simp only [LinearMap.mem_range, Submodule.mem_map, LinearEquiv.coe_toLinearMap]
        constructor
        · rintro ⟨v, hv⟩
          use C.mulVecLin (e.symm v)
          refine ⟨⟨e.symm v, rfl⟩, ?_⟩
          rw [← hv, h_eq]
        · rintro ⟨y, ⟨w, hw⟩, hy⟩
          use e w
          rw [h_eq]
          simp only [LinearEquiv.symm_apply_apply]
          rw [← hy, hw]
      rw [h_range]
      -- finrank (map e (range mulVecLin C)) = finrank (range mulVecLin C)
      have h_equiv : (LinearMap.range C.mulVecLin) ≃ₗ[ℂ]
          (Submodule.map e.toLinearMap (LinearMap.range C.mulVecLin)) :=
        Submodule.equivMapOfInjective e.toLinearMap e.injective (LinearMap.range C.mulVecLin)
      exact h_equiv.finrank_eq
    exact h_range_finrank
  omega

omit [Nonempty n] in
/-- For a matrix C with rank(C) + k < n, there exists a unit vector x that is:
    1. In the kernel of C (so Cx = 0)
    2. In the tail eigenvector span of AᴴA (so ‖Ax‖² ≤ σₖ²)

    This is the dimension counting argument from Grassmann's formula.
    The hypothesis `hDim : Fintype.card n > C.rank + k` ensures the dimension sum
    exceeds n, guaranteeing a nontrivial intersection.

    NOTE: When rank(C) ≤ k and k ≥ n/2, the dimension sum may equal n exactly,
    in which case the intersection can be trivial. The hypothesis `hDim` excludes
    this edge case. In practice, for Eckart-Young applications where k is the
    approximation rank, k is typically small (k << n), so this hypothesis is mild.

    NOTE: This lemma is useful for bounding individual vectors, but NOT sufficient
    for proving the diagonal-only version of Eckart-Young (which is false). -/
theorem exists_unit_in_kernel_and_tail_span (A C : Matrix n n ℂ) (k : ℕ)
    (hk : k < Fintype.card n) (hDim : Fintype.card n > C.rank + k) :
    let hAHA := (posSemidef_conjTranspose_mul_self A).isHermitian
    let kFin : Fin (Fintype.card n) := ⟨k, hk⟩
    ∃ x : EuclideanSpace ℂ n, ‖x‖ = 1 ∧ C.mulVec x = 0 ∧ x ∈ eigenvectorSpanTail hAHA kFin := by
  intro hAHA kFin

  -- Define the two subspaces (both in EuclideanSpace ℂ n)
  let KerC := LinearMap.ker (Matrix.toEuclideanLin C)
  let TailSpan := eigenvectorSpanTail hAHA kFin

  -- Dimension bounds from rank-nullity and tail span definition
  have hKerC_dim : Module.finrank ℂ KerC ≥ Fintype.card n - C.rank :=
    finrank_ker_toEuclideanLin_ge C

  have hTail_dim : Module.finrank ℂ TailSpan = Fintype.card n - k :=
    finrank_eigenvectorSpanTail (Aᴴ * A) hAHA kFin

  -- Rewrite Fintype.card in terms of finrank for compatibility with exists_nonzero_in_intersection
  have hFinrank : Module.finrank ℂ (EuclideanSpace ℂ n) = Fintype.card n :=
    finrank_euclideanSpace

  -- Prove dimension sum exceeds finrank E
  have hSum : Module.finrank ℂ KerC + Module.finrank ℂ TailSpan > Module.finrank ℂ (EuclideanSpace ℂ n) := by
    rw [hFinrank]
    calc Module.finrank ℂ KerC + Module.finrank ℂ TailSpan
      _ ≥ (Fintype.card n - C.rank) + (Fintype.card n - k) := Nat.add_le_add hKerC_dim (le_of_eq hTail_dim.symm)
      _ > Fintype.card n := by omega

  -- Get nonzero vector in intersection via Grassmann's formula
  obtain ⟨x, hx_ne, hx_ker, hx_tail⟩ := exists_nonzero_in_intersection KerC TailSpan hSum

  -- Normalize to unit vector: y = x / ‖x‖ (scale by real inverse)
  have hx_norm_ne : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx_ne
  have hx_norm_pos : 0 < ‖x‖ := norm_pos_iff.mpr hx_ne
  let y := (‖x‖⁻¹ : ℝ) • x
  use y
  refine ⟨?_, ?_, ?_⟩
  · -- ‖y‖ = 1 (using real scalar)
    simp only [y, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm]
    rw [inv_mul_cancel₀ hx_norm_ne]
  · -- C.mulVec y = 0
    simp only [y]
    -- x is in the kernel of toEuclideanLin C
    have hx_toEuc_zero : Matrix.toEuclideanLin C x = 0 := LinearMap.mem_ker.mp hx_ker
    -- This means toLp (C *ᵥ ofLp x) = 0, so C *ᵥ ofLp x = 0
    simp only [Matrix.toEuclideanLin_apply] at hx_toEuc_zero
    have hx_mulVec_zero : C.mulVec (WithLp.ofLp x) = 0 := by
      have := WithLp.toLp_injective (p := 2) hx_toEuc_zero
      exact this
    -- For scalar multiplication: ofLp (c • x) = c • ofLp x
    have hOfLp_smul : WithLp.ofLp ((‖x‖⁻¹ : ℝ) • x) = (‖x‖⁻¹ : ℝ) • WithLp.ofLp x := rfl
    rw [hOfLp_smul, Matrix.mulVec_smul, hx_mulVec_zero, smul_zero]
  · -- y ∈ eigenvectorSpanTail
    exact Submodule.smul_mem TailSpan (‖x‖⁻¹ : ℝ) hx_tail

end EckartYoungBridge

end CourantFischer
