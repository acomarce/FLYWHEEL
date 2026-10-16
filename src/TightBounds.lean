/-
Copyright (c) 2025 FLYWHEEL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aleksandar Markovski

# Tight Bounds for Kronecker Approximation

The Frobenius error of a Kronecker approximation transfers exactly through R:
‖C - R⁻¹(X)‖_F = ‖R(C) - X‖_F (`frobenius_error_via_R_isometry`). For X the rank-1 truncated
SVD of R(C), this error is √(σ₂² + σ₃² + ⋯) for the singular values σᵢ of R(C), not σ₂.
That formula is not formalized here, because the repo has no rectangular Frobenius error
formula for `truncatedSVD_rect`.
Spectral bounds are upper only since R does NOT preserve ‖·‖₂.

## References

[1] Van Loan, C.F. & Pitsianis, N. (1993). Approximation with Kronecker
    Products. NATO ASI Series E, vol. 232, pp. 293–314.
[2] Eckart, C. & Young, G. (1936). The approximation of one matrix by
    another of lower rank. Psychometrika 1(3), 211–218.
[3] Horn & Johnson (2012). Matrix Analysis, 2nd ed. Cambridge. §7.4.

Counter-example for spectral preservation: anti-diagonal permutation.

## Implementation Status

Complete: no unproved goals. The former Part 5 coherence claim was false and has been
replaced by a note with an explicit counterexample.
-/

import MatrixNormRelations
import SpectralNormGap

open scoped ComplexOrder Matrix
open Matrix

namespace Matrix.TightBounds

variable {m n p q : Type*}
variable [Fintype m] [Fintype n] [Fintype p] [Fintype q]
variable [DecidableEq m] [DecidableEq n] [DecidableEq p] [DecidableEq q]

/-! ## Rectangular SVD infrastructure

R : M_(m×n,p×q) → M_(m×p,n×q) produces rectangular matrices.

XXX: This whole section is a bit of a mess. I originally tried to use
Mathlib's SVD directly but it only handles square matrices. Had to build
this rectangular version manually. There's probably a cleaner way...
-/

section RectangularSVD

-- dbg_trace "entering RectangularSVD section"  -- uncomment for debugging

/-- Sorted σᵢ for rectangular matrices. -/
-- TODO: consider renaming to `singularValuesRect` for consistency?
noncomputable def singularValues₀_rect {m' n' : Type*} [Fintype m'] [Fintype n'] [DecidableEq n']
    (A : Matrix m' n' ℂ) : Fin (min (Fintype.card m') (Fintype.card n')) → ℝ :=
  SVD.Rectangular.singularValues A

noncomputable def sigma2 {m' n' : Type*} [Fintype m'] [Fintype n'] [DecidableEq n']
    (A : Matrix m' n' ℂ) (h : 1 < min (Fintype.card m') (Fintype.card n')) : ℝ :=
  singularValues₀_rect A ⟨1, h⟩

noncomputable def sigma1 {m' n' : Type*} [Fintype m'] [Fintype n'] [DecidableEq n']
    (A : Matrix m' n' ℂ) (h : 0 < min (Fintype.card m') (Fintype.card n')) : ℝ :=
  singularValues₀_rect A ⟨0, h⟩

lemma singularValues₀_rect_nonneg {m' n' : Type*} [Fintype m'] [Fintype n']
    [DecidableEq m'] [DecidableEq n']
    (A : Matrix m' n' ℂ) (k : Fin (min (Fintype.card m') (Fintype.card n'))) :
    0 ≤ singularValues₀_rect A k :=
  SVD.Rectangular.singularValues_nonneg A k

lemma singularValues₀_rect_antitone {m' n' : Type*} [Fintype m'] [Fintype n']
    [DecidableEq m'] [DecidableEq n']
    (A : Matrix m' n' ℂ) : Antitone (singularValues₀_rect A) :=
  SVD.Rectangular.singularValues_antitone A

/-- The largest singular value equals the maxSingularValue (when nonempty).
    This follows from singular values being antitone (σ₀ is the maximum). -/
lemma sigma1_eq_maxSingularValue {m' n' : Type*} [Fintype m'] [Fintype n']
    [DecidableEq m'] [DecidableEq n']
    (h : 0 < min (Fintype.card m') (Fintype.card n'))
    (A : Matrix m' n' ℂ) :
    sigma1 A h = SVD.Rectangular.maxSingularValue h A := by
  unfold sigma1 singularValues₀_rect SVD.Rectangular.maxSingularValue
  apply le_antisymm
  · -- σ₀ ≤ sup' σ
    exact Finset.le_sup' _ (Finset.mem_univ _)
  · -- sup' σ ≤ σ₀ (since σ is antitone, max is at 0)
    apply Finset.sup'_le
    intro k _
    have h0 : (⟨0, h⟩ : Fin (min (Fintype.card m') (Fintype.card n'))) ≤ k :=
      Fin.mk_le_mk.mpr (Nat.zero_le _)
    exact SVD.Rectangular.singularValues_antitone A h0

/-- sigma2 ≤ sigma1 (singular values are sorted). -/
lemma sigma2_le_sigma1 {m' n' : Type*} [Fintype m'] [Fintype n']
    [DecidableEq m'] [DecidableEq n']
    (A : Matrix m' n' ℂ) (h1 : 1 < min (Fintype.card m') (Fintype.card n')) :
    sigma2 A h1 ≤ sigma1 A (Nat.lt_trans Nat.zero_lt_one h1) := by
  unfold sigma2 sigma1 singularValues₀_rect
  apply SVD.Rectangular.singularValues_antitone A
  exact Fin.mk_le_mk.mpr (Nat.zero_le _)

/-- Singular values squared equal the corresponding eigenvalues₀ for rectangular matrices. -/
lemma singularValues₀_rect_sq {m' n' : Type*} [Fintype m'] [Fintype n']
    [DecidableEq m'] [DecidableEq n']
    (A : Matrix m' n' ℂ) (k : Fin (min (Fintype.card m') (Fintype.card n'))) :
    (singularValues₀_rect A k) ^ 2 =
    (posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues₀
      (Fin.castLE (Nat.min_le_right _ _) k) :=
  SVD.Rectangular.singularValues_sq_rect A k

/-- Sum of squared singular values equals trace for rectangular matrices. -/
lemma sum_sq_singularValues₀_rect_eq_trace {m' n' : Type*} [Fintype m'] [Fintype n']
    [DecidableEq m'] [DecidableEq n']
    (A : Matrix m' n' ℂ) :
    ∑ k, (singularValues₀_rect A k) ^ 2 = Complex.re (Matrix.trace (Aᴴ * A)) :=
  SVD.Rectangular.sum_sq_singularValues_rect_eq_trace A

/-- Rank equals number of nonzero singular values for rectangular matrices. -/
lemma rank_eq_card_nonzero_singularValues₀_rect {m' n' : Type*} [Fintype m'] [Fintype n']
    [DecidableEq m'] [DecidableEq n']
    (A : Matrix m' n' ℂ) :
    A.rank = Fintype.card {k : Fin (min (Fintype.card m') (Fintype.card n')) //
                           singularValues₀_rect A k ≠ 0} :=
  SVD.Rectangular.rank_eq_card_nonzero_singularValues_rect A

end RectangularSVD

/-! ## Part 2: Truncated SVD for Rectangular Matrices

Define rank-k approximation for rectangular matrices and prove
the spectral error formula.
-/

section TruncatedSVDRect

/-! ### Definitions -/

/-- Truncated singular values for rectangular matrices: keeps top k, zeros the rest.
    Uses sorted singular values indexed by `Fin (min #m #n)`. -/
noncomputable def truncatedSingularValues_rect {m' n' : Type*} [Fintype m'] [Fintype n']
    [DecidableEq n']
    (A : Matrix m' n' ℂ) (k : ℕ) : Fin (min (Fintype.card m') (Fintype.card n')) → ℝ :=
  fun i => if i.val < k then SVD.Rectangular.singularValues A i else 0

/-- Truncated singular diagonal for rectangular matrices: like singularDiagonal but zeros beyond k.
    S(i, j) = σ_idx if idx < k and (i,j) corresponds to diagonal position idx, else 0. -/
noncomputable def truncatedSingularDiagonal_rect {m' n' : Type*} [Fintype m'] [Fintype n']
    [DecidableEq m'] [DecidableEq n']
    (A : Matrix m' n' ℂ) (k : ℕ) : Matrix m' n' ℂ := fun i j =>
  let fi : Fin (Fintype.card m') := SVD.Rectangular.eigenvaluesBijection m' i
  let fj : Fin (Fintype.card n') := SVD.Rectangular.eigenvaluesBijection n' j
  if h : fi.val = fj.val ∧ fi.val < min (Fintype.card m') (Fintype.card n') ∧ fi.val < k then
    Complex.ofReal (SVD.Rectangular.singularValues A ⟨fi.val, h.2.1⟩)
  else
    0

/-- Truncated SVD for rectangular matrices: the rank-k truncation of the SVD.
    Returns Aₖ = U * Sₖ * V* where Sₖ has only the top k singular values.
    Its optimality (rectangular Eckart-Young) is not formalized. -/
noncomputable def truncatedSVD_rect {m' n' : Type*} [Fintype m'] [Fintype n']
    [DecidableEq m'] [DecidableEq n']
    (A : Matrix m' n' ℂ) (k : ℕ) : Matrix m' n' ℂ :=
  let U := SVD.Rectangular.constructedU_rectangular A
  let V := SVD.Rectangular.rightUnitary A
  let Sk := truncatedSingularDiagonal_rect A k
  (U : Matrix m' m' ℂ) * Sk * star (V : Matrix n' n' ℂ)

/-! ### Basic Properties of Truncated Singular Values -/

/-- Truncated singular values are non-negative. -/
lemma truncatedSingularValues_rect_nonneg {m' n' : Type*} [Fintype m'] [Fintype n']
    [DecidableEq m'] [DecidableEq n']
    (A : Matrix m' n' ℂ) (k : ℕ) (i : Fin (min (Fintype.card m') (Fintype.card n'))) :
    0 ≤ truncatedSingularValues_rect A k i := by
  unfold truncatedSingularValues_rect
  split_ifs
  · exact SVD.Rectangular.singularValues_nonneg A i
  · rfl

/-- Truncated singular values equal original values for indices < k. -/
lemma truncatedSingularValues_rect_eq_of_lt {m' n' : Type*} [Fintype m'] [Fintype n']
    [DecidableEq m'] [DecidableEq n']
    (A : Matrix m' n' ℂ) (k : ℕ) (i : Fin (min (Fintype.card m') (Fintype.card n')))
    (hi : i.val < k) :
    truncatedSingularValues_rect A k i = SVD.Rectangular.singularValues A i := by
  unfold truncatedSingularValues_rect
  simp only [hi, ↓reduceIte]

/-- Truncated singular values are zero for indices ≥ k. -/
lemma truncatedSingularValues_rect_eq_zero_of_ge {m' n' : Type*} [Fintype m'] [Fintype n']
    [DecidableEq m'] [DecidableEq n']
    (A : Matrix m' n' ℂ) (k : ℕ) (i : Fin (min (Fintype.card m') (Fintype.card n')))
    (hi : k ≤ i.val) :
    truncatedSingularValues_rect A k i = 0 := by
  unfold truncatedSingularValues_rect
  simp only [Nat.not_lt.mpr hi, ↓reduceIte]

/-- The number of nonzero truncated singular values is at most k. -/
lemma card_truncatedSingularValues_rect_nonzero_le {m' n' : Type*} [Fintype m'] [Fintype n']
    [DecidableEq m'] [DecidableEq n']
    (A : Matrix m' n' ℂ) (k : ℕ) :
    Fintype.card { i : Fin (min (Fintype.card m') (Fintype.card n')) //
      truncatedSingularValues_rect A k i ≠ 0 } ≤ k := by
  -- Nonzero entries can only occur when i.val < k
  have h_subset : ∀ i, truncatedSingularValues_rect A k i ≠ 0 → i.val < k := by
    intro i hi
    by_contra h_not_lt
    push_neg at h_not_lt
    have := truncatedSingularValues_rect_eq_zero_of_ge A k i h_not_lt
    exact hi this
  -- Map nonzero indices to Fin k
  have h_inj : Function.Injective (fun (x : { i // truncatedSingularValues_rect A k i ≠ 0 }) =>
      (⟨x.val.val, h_subset x.val x.prop⟩ : Fin k)) := by
    intro ⟨x, hx⟩ ⟨y, hy⟩ h_eq
    simp only [Fin.mk.injEq] at h_eq
    exact Subtype.ext (Fin.ext h_eq)
  calc Fintype.card { i // truncatedSingularValues_rect A k i ≠ 0 }
      ≤ Fintype.card (Fin k) := Fintype.card_le_of_injective _ h_inj
    _ = k := Fintype.card_fin k

/-! ### Properties of Truncated Singular Diagonal -/

/-- Truncated singular diagonal equals full diagonal when k is large enough. -/
lemma truncatedSingularDiagonal_rect_full {m' n' : Type*} [Fintype m'] [Fintype n']
    [DecidableEq m'] [DecidableEq n']
    (A : Matrix m' n' ℂ) (k : ℕ) (hk : min (Fintype.card m') (Fintype.card n') ≤ k) :
    truncatedSingularDiagonal_rect A k = SVD.Rectangular.singularDiagonal A := by
  ext i j
  simp only [truncatedSingularDiagonal_rect, SVD.Rectangular.singularDiagonal]
  set fi := SVD.Rectangular.eigenvaluesBijection m' i with hfi
  set fj := SVD.Rectangular.eigenvaluesBijection n' j with hfj
  by_cases h : fi.val = fj.val ∧ fi.val < min (Fintype.card m') (Fintype.card n')
  · -- On the diagonal, all indices satisfy fi.val < k
    have hk' : fi.val < k := Nat.lt_of_lt_of_le h.2 hk
    have h3 : fi.val = fj.val ∧ fi.val < min (Fintype.card m') (Fintype.card n') ∧ fi.val < k :=
      ⟨h.1, h.2, hk'⟩
    rw [dif_pos h3, dif_pos h]
  · -- Off diagonal: both definitions give 0
    have h' : ¬(fi.val = fj.val ∧ fi.val < min (Fintype.card m') (Fintype.card n') ∧ fi.val < k) := by
      intro ⟨heq, hmin, _⟩
      exact h ⟨heq, hmin⟩
    rw [dif_neg h', dif_neg h]

/-- Truncated singular diagonal with k=0 is the zero matrix. -/
lemma truncatedSingularDiagonal_rect_zero {m' n' : Type*} [Fintype m'] [Fintype n']
    [DecidableEq m'] [DecidableEq n']
    (A : Matrix m' n' ℂ) :
    truncatedSingularDiagonal_rect A 0 = 0 := by
  ext i j
  simp only [truncatedSingularDiagonal_rect, Nat.not_lt_zero, and_false, ↓reduceDIte]
  rfl

/-! ### Main Theorems -/

/-- The truncated SVD with k = 0 is the zero matrix. -/
theorem truncatedSVD_rect_zero {m' n' : Type*} [Fintype m'] [Fintype n']
    [DecidableEq m'] [DecidableEq n']
    (A : Matrix m' n' ℂ) : truncatedSVD_rect A 0 = 0 := by
  unfold truncatedSVD_rect
  rw [truncatedSingularDiagonal_rect_zero]
  simp only [Matrix.mul_zero, Matrix.zero_mul]

/-- The truncated SVD with k ≥ min(#m, #n) equals the original matrix A.
    This uses the full rectangular SVD decomposition. -/
theorem truncatedSVD_rect_full {m' n' : Type*} [Fintype m'] [Fintype n']
    [DecidableEq m'] [DecidableEq n']
    (A : Matrix m' n' ℂ) (k : ℕ) (hk : min (Fintype.card m') (Fintype.card n') ≤ k) :
    truncatedSVD_rect A k = A := by
  unfold truncatedSVD_rect
  rw [truncatedSingularDiagonal_rect_full A k hk]
  -- Now we have U * S * V* = A by SVD decomposition
  have hAV := SVD.Rectangular.AV_eq_US_rectangular A
  have h_V_unitary := Matrix.mem_unitaryGroup_iff.mp (SVD.Rectangular.rightUnitary A).2
  calc (SVD.Rectangular.constructedU_rectangular A : Matrix m' m' ℂ) *
          SVD.Rectangular.singularDiagonal A * star (SVD.Rectangular.rightUnitary A : Matrix n' n' ℂ)
      = ((SVD.Rectangular.constructedU_rectangular A : Matrix m' m' ℂ) *
          SVD.Rectangular.singularDiagonal A) * star (SVD.Rectangular.rightUnitary A : Matrix n' n' ℂ) :=
        by rw [Matrix.mul_assoc]
    _ = (A * (SVD.Rectangular.rightUnitary A : Matrix n' n' ℂ)) *
        star (SVD.Rectangular.rightUnitary A : Matrix n' n' ℂ) := by rw [← hAV]
    _ = A * ((SVD.Rectangular.rightUnitary A : Matrix n' n' ℂ) *
        star (SVD.Rectangular.rightUnitary A : Matrix n' n' ℂ)) := by rw [Matrix.mul_assoc]
    _ = A * (1 : Matrix n' n' ℂ) := by rw [h_V_unitary]
    _ = A := Matrix.mul_one A

/-- The rank of the truncated rectangular SVD is at most k.
    Uses that unitary transformations preserve rank and diagonal rank ≤ k. -/
theorem truncatedSVD_rect_rank_le {m' n' : Type*} [Fintype m'] [Fintype n']
    [DecidableEq m'] [DecidableEq n']
    (A : Matrix m' n' ℂ) (k : ℕ) : (truncatedSVD_rect A k).rank ≤ k := by
  unfold truncatedSVD_rect
  let D := truncatedSingularDiagonal_rect A k
  let U := (SVD.Rectangular.constructedU_rectangular A : Matrix m' m' ℂ)
  let V := (SVD.Rectangular.rightUnitary A : Matrix n' n' ℂ)
  -- truncatedSVD_rect A k = U * D * V*
  -- rank(U * D * V*) ≤ rank(D) since U, V* are unitary (invertible)
  have hU_isUnit : IsUnit U.det :=
    UnitaryGroup.det_isUnit (SVD.Rectangular.constructedU_rectangular A)
  have hVstar_isUnit : IsUnit (star V).det := by
    have hV_isUnit : IsUnit V.det := UnitaryGroup.det_isUnit (SVD.Rectangular.rightUnitary A)
    rw [star_eq_conjTranspose, det_conjTranspose]
    exact hV_isUnit.star
  -- rank(U * D * V*) = rank(D * V*) = rank(D)
  have h1 : (U * D * star V).rank = (D * star V).rank := by
    rw [Matrix.mul_assoc]
    exact rank_mul_eq_right_of_isUnit_det U (D * star V) hU_isUnit
  have h2 : (D * star V).rank = D.rank := rank_mul_eq_left_of_isUnit_det (star V) D hVstar_isUnit
  -- rank(D) ≤ k: D has at most k nonzero diagonal entries
  -- The truncated diagonal has at most k nonzero entries on positions where idx < k
  have h3 : D.rank ≤ k := by
    by_cases hk : k = 0
    · subst hk
      have hD0 : D = 0 := truncatedSingularDiagonal_rect_zero A
      rw [hD0, rank_zero]
    · -- For k > 0, split into two cases based on whether k ≥ min(#m', #n')
      by_cases hk_large : min (Fintype.card m') (Fintype.card n') ≤ k
      · -- Case: k ≥ min(#m', #n')
        -- Then rank(D) ≤ min(#m', #n') ≤ k
        calc D.rank ≤ min (Fintype.card m') (Fintype.card n') :=
              SVD.Rectangular.rank_le_min_card D
          _ ≤ k := hk_large
      · -- Case: k < min(#m', #n')
        -- Column j of D vanishes unless eigenvaluesBijection(j) < k, so D = D * P
        -- with P the diagonal 0/1 projection onto those columns, and
        -- rank(D) ≤ rank(P) = #{j | eigenvaluesBijection(j) < k} ≤ k.
        classical
        have hDP : D = D * diagonal (fun j : n' =>
            if (SVD.Rectangular.eigenvaluesBijection n' j).val < k then (1 : ℂ) else 0) := by
          ext i j
          rw [mul_diagonal]
          by_cases hj : (SVD.Rectangular.eigenvaluesBijection n' j).val < k
          · rw [if_pos hj, mul_one]
          · rw [if_neg hj, mul_zero]
            show truncatedSingularDiagonal_rect A k i j = 0
            simp only [truncatedSingularDiagonal_rect]
            rw [dif_neg]
            rintro ⟨heq, -, hlt⟩
            omega
        have hP : (diagonal (fun j : n' =>
            if (SVD.Rectangular.eigenvaluesBijection n' j).val < k then (1 : ℂ) else 0)).rank
              ≤ k := by
          rw [rank_diagonal]
          calc Fintype.card {j : n' // (if (SVD.Rectangular.eigenvaluesBijection n' j).val < k
                  then (1 : ℂ) else 0) ≠ 0}
              ≤ Fintype.card (Fin k) :=
                Fintype.card_le_of_injective
                  (fun j => ⟨(SVD.Rectangular.eigenvaluesBijection n' j.1).val, by
                    by_contra h
                    exact j.2 (if_neg h)⟩)
                  (fun a b hab => by
                    apply Subtype.ext
                    apply (SVD.Rectangular.eigenvaluesBijection n').injective
                    apply Fin.ext
                    have h := congrArg Fin.val hab
                    simpa using h)
            _ = k := Fintype.card_fin k
        calc D.rank = (D * diagonal (fun j : n' =>
              if (SVD.Rectangular.eigenvaluesBijection n' j).val < k then (1 : ℂ) else 0)).rank := by
              rw [← hDP]
          _ ≤ _ := rank_mul_le_right _ _
          _ ≤ k := hP
  calc (U * D * star V).rank = (D * star V).rank := h1
    _ = D.rank := h2
    _ ≤ k := h3

end TruncatedSVDRect

/-! ## Part 3: Spectral Error Formula for Rectangular Matrices

The key result: ‖A - truncatedSVD_rect A k‖₂ = σₖ(A)

**Proof strategy:**
1. Define the tail: `truncatedSVD_rect_tail A k = A - truncatedSVD_rect A k`
2. Show the tail equals `U * Σ_tail * V*` where Σ_tail zeros the first k singular values
3. Use unitary invariance to get `‖tail‖ = ‖Σ_tail‖`
4. Show `‖Σ_tail‖ = σₖ(A)` since singular values are sorted (max of remaining = σₖ)
-/

section SpectralErrorRect

variable {m' n' : Type*} [Fintype m'] [Fintype n'] [DecidableEq m'] [DecidableEq n']

-- Enable L2 operator norm instances locally
attribute [local instance] Matrix.instL2OpNormedAddCommGroup
attribute [local instance] Matrix.instL2OpNormedSpace
attribute [local instance] Matrix.instL2OpNormedRing
attribute [local instance] Matrix.instL2OpNormedAlgebra
attribute [local instance] Matrix.instL2OpMetricSpace
attribute [local instance] Matrix.instCStarRing

/-! ### Definitions for Tail Components -/

/-- Tail singular values: zeros the first k entries, keeps σₖ, σₖ₊₁, ..., σᵣ₋₁.
    This is the complement of truncatedSingularValues_rect. -/
noncomputable def truncatedSingularValues_rect_tail
    (A : Matrix m' n' ℂ) (k : ℕ) : Fin (min (Fintype.card m') (Fintype.card n')) → ℝ :=
  fun i => if i.val < k then 0 else SVD.Rectangular.singularValues A i

/-- Tail singular values are non-negative. -/
lemma truncatedSingularValues_rect_tail_nonneg (A : Matrix m' n' ℂ) (k : ℕ)
    (i : Fin (min (Fintype.card m') (Fintype.card n'))) :
    0 ≤ truncatedSingularValues_rect_tail A k i := by
  unfold truncatedSingularValues_rect_tail
  split_ifs
  · rfl
  · exact SVD.Rectangular.singularValues_nonneg A i

omit [DecidableEq m'] in
/-- Tail singular values are zero for indices < k. -/
lemma truncatedSingularValues_rect_tail_eq_zero_of_lt (A : Matrix m' n' ℂ) (k : ℕ)
    (i : Fin (min (Fintype.card m') (Fintype.card n'))) (hi : i.val < k) :
    truncatedSingularValues_rect_tail A k i = 0 := by
  unfold truncatedSingularValues_rect_tail
  simp only [hi, ↓reduceIte]

omit [DecidableEq m'] in
/-- Tail singular values equal original values for indices ≥ k. -/
lemma truncatedSingularValues_rect_tail_eq_of_ge (A : Matrix m' n' ℂ) (k : ℕ)
    (i : Fin (min (Fintype.card m') (Fintype.card n'))) (hi : k ≤ i.val) :
    truncatedSingularValues_rect_tail A k i = SVD.Rectangular.singularValues A i := by
  unfold truncatedSingularValues_rect_tail
  simp only [Nat.not_lt.mpr hi, ↓reduceIte]

/-- Tail singular diagonal: keeps entries at positions ≥ k, zeros the first k. -/
noncomputable def truncatedSingularDiagonal_rect_tail (A : Matrix m' n' ℂ) (k : ℕ) : Matrix m' n' ℂ :=
  fun i j =>
    let fi : Fin (Fintype.card m') := SVD.Rectangular.eigenvaluesBijection m' i
    let fj : Fin (Fintype.card n') := SVD.Rectangular.eigenvaluesBijection n' j
    if h : fi.val = fj.val ∧ fi.val < min (Fintype.card m') (Fintype.card n') ∧ k ≤ fi.val then
      Complex.ofReal (SVD.Rectangular.singularValues A ⟨fi.val, h.2.1⟩)
    else
      0

/-- The tail of the truncated SVD: A - truncatedSVD_rect A k.
    This is the "discarded" portion containing singular values σₖ, σₖ₊₁, .... -/
noncomputable def truncatedSVD_rect_tail (A : Matrix m' n' ℂ) (k : ℕ) : Matrix m' n' ℂ :=
  A - truncatedSVD_rect A k

/-! ### Key Decomposition Lemmas -/

/-- The full singular diagonal equals truncated + tail diagonals. -/
lemma singularDiagonal_eq_truncated_add_tail (A : Matrix m' n' ℂ) (k : ℕ) :
    SVD.Rectangular.singularDiagonal A =
    truncatedSingularDiagonal_rect A k + truncatedSingularDiagonal_rect_tail A k := by
  ext i j
  simp only [Matrix.add_apply]
  unfold truncatedSingularDiagonal_rect truncatedSingularDiagonal_rect_tail
         SVD.Rectangular.singularDiagonal
  set fi := SVD.Rectangular.eigenvaluesBijection m' i
  set fj := SVD.Rectangular.eigenvaluesBijection n' j
  by_cases h_diag : fi.val = fj.val ∧ fi.val < min (Fintype.card m') (Fintype.card n')
  · -- On the diagonal
    by_cases hk : fi.val < k
    · -- Position < k: comes from truncated part
      have h1 : fi.val = fj.val ∧ fi.val < min (Fintype.card m') (Fintype.card n') ∧ fi.val < k :=
        ⟨h_diag.1, h_diag.2, hk⟩
      have h2 : ¬(fi.val = fj.val ∧ fi.val < min (Fintype.card m') (Fintype.card n') ∧ k ≤ fi.val) := by
        intro ⟨_, _, hge⟩
        exact Nat.not_lt.mpr hge hk
      rw [dif_pos h_diag, dif_pos h1, dif_neg h2, add_zero]
    · -- Position ≥ k: comes from tail part
      push_neg at hk
      have h1 : ¬(fi.val = fj.val ∧ fi.val < min (Fintype.card m') (Fintype.card n') ∧ fi.val < k) := by
        intro ⟨_, _, hlt⟩
        exact Nat.not_lt.mpr hk hlt
      have h2 : fi.val = fj.val ∧ fi.val < min (Fintype.card m') (Fintype.card n') ∧ k ≤ fi.val :=
        ⟨h_diag.1, h_diag.2, hk⟩
      rw [dif_pos h_diag, dif_neg h1, dif_pos h2, zero_add]
  · -- Off diagonal: all terms are zero
    have h1 : ¬(fi.val = fj.val ∧ fi.val < min (Fintype.card m') (Fintype.card n') ∧ fi.val < k) := by
      intro ⟨heq, hmin, _⟩
      exact h_diag ⟨heq, hmin⟩
    have h2 : ¬(fi.val = fj.val ∧ fi.val < min (Fintype.card m') (Fintype.card n') ∧ k ≤ fi.val) := by
      intro ⟨heq, hmin, _⟩
      exact h_diag ⟨heq, hmin⟩
    rw [dif_neg h_diag, dif_neg h1, dif_neg h2, add_zero]

/-- A = truncatedSVD_rect A k + truncatedSVD_rect_tail A k.
    The matrix decomposes into its best rank-k approximation plus a tail. -/
theorem truncatedSVD_rect_add_tail (A : Matrix m' n' ℂ) (k : ℕ) :
    A = truncatedSVD_rect A k + truncatedSVD_rect_tail A k := by
  unfold truncatedSVD_rect_tail
  simp only [add_sub_cancel]

/-- The tail can be expressed as U * Σ_tail * V*.
    This is the key structural lemma for the spectral error proof. -/
theorem truncatedSVD_rect_tail_eq_USV (A : Matrix m' n' ℂ) (k : ℕ) :
    truncatedSVD_rect_tail A k =
    (SVD.Rectangular.constructedU_rectangular A : Matrix m' m' ℂ) *
    truncatedSingularDiagonal_rect_tail A k *
    star (SVD.Rectangular.rightUnitary A : Matrix n' n' ℂ) := by
  unfold truncatedSVD_rect_tail truncatedSVD_rect
  -- A - U * Σₖ * V* = U * (Σ - Σₖ) * V* = U * Σ_tail * V*
  set U := (SVD.Rectangular.constructedU_rectangular A : Matrix m' m' ℂ) with hU_def
  set V := (SVD.Rectangular.rightUnitary A : Matrix n' n' ℂ) with hV_def
  set S := SVD.Rectangular.singularDiagonal A with hS_def
  set Sk := truncatedSingularDiagonal_rect A k with hSk_def
  set Stail := truncatedSingularDiagonal_rect_tail A k with hStail_def
  -- First, get A = U * Σ * V*
  have h_AV := SVD.Rectangular.AV_eq_US_rectangular A
  have h_V_unitary := mem_unitaryGroup_iff.mp (SVD.Rectangular.rightUnitary A).2
  have h_A_eq : A = U * S * star V := by
    calc A = A * (1 : Matrix n' n' ℂ) := by rw [Matrix.mul_one]
      _ = A * (V * star V) := by rw [h_V_unitary]
      _ = (A * V) * star V := by rw [Matrix.mul_assoc]
      _ = (U * S) * star V := by rw [h_AV]
      _ = U * S * star V := by rw [Matrix.mul_assoc]
  -- Σ = Σk + Σtail
  have h_sigma_split : S = Sk + Stail := singularDiagonal_eq_truncated_add_tail A k
  -- Now compute A - truncatedSVD_rect A k
  have h_sub : S - Sk = Stail := by rw [h_sigma_split]; simp only [add_sub_cancel_left]
  -- Expand the let definitions in the goal
  show A - U * Sk * star V = U * Stail * star V
  calc A - U * Sk * star V
      = U * S * star V - U * Sk * star V := by rw [h_A_eq]
    _ = U * (S * star V) - U * (Sk * star V) := by
        rw [Matrix.mul_assoc U S (star V), Matrix.mul_assoc U Sk (star V)]
    _ = U * (S * star V - Sk * star V) := by rw [← Matrix.mul_sub]
    _ = U * ((S - Sk) * star V) := by rw [Matrix.sub_mul]
    _ = U * (Stail * star V) := by rw [h_sub]
    _ = U * Stail * star V := by rw [Matrix.mul_assoc]

/-! ### Unitary Invariance for Rectangular Spectral Norm -/

/-- Left multiplication by unitary preserves spectral norm (square target).
    Uses the CStarRing structure on square matrices. -/
lemma l2_opNorm_unitary_mul_rect (U : unitaryGroup m' ℂ) (B : Matrix m' n' ℂ) :
    ‖(U : Matrix m' m' ℂ) * B‖ = ‖B‖ := by
  -- Strategy: ‖UB‖² = ‖(UB)ᴴ(UB)‖ = ‖BᴴU*UB‖ = ‖BᴴB‖ = ‖B‖²
  have h_UstarU : star (U : Matrix m' m' ℂ) * (U : Matrix m' m' ℂ) = 1 :=
    (mem_unitaryGroup_iff'.mp U.2)
  have h1 : ‖(U : Matrix m' m' ℂ) * B‖ ^ 2 = ‖B‖ ^ 2 := by
    calc ‖(U : Matrix m' m' ℂ) * B‖ ^ 2
        = ‖(U : Matrix m' m' ℂ) * B‖ * ‖(U : Matrix m' m' ℂ) * B‖ := sq _
      _ = ‖((U : Matrix m' m' ℂ) * B)ᴴ * ((U : Matrix m' m' ℂ) * B)‖ := by
          rw [l2_opNorm_conjTranspose_mul_self]
      _ = ‖Bᴴ * ((U : Matrix m' m' ℂ)ᴴ * ((U : Matrix m' m' ℂ) * B))‖ := by
          rw [conjTranspose_mul, Matrix.mul_assoc]
      _ = ‖Bᴴ * (star (U : Matrix m' m' ℂ) * ((U : Matrix m' m' ℂ) * B))‖ := by
          simp only [star_eq_conjTranspose]
      _ = ‖Bᴴ * ((star (U : Matrix m' m' ℂ) * (U : Matrix m' m' ℂ)) * B)‖ := by
          rw [Matrix.mul_assoc (star (U : Matrix m' m' ℂ))]
      _ = ‖Bᴴ * ((1 : Matrix m' m' ℂ) * B)‖ := by rw [h_UstarU]
      _ = ‖Bᴴ * B‖ := by rw [Matrix.one_mul]
      _ = ‖B‖ * ‖B‖ := by rw [l2_opNorm_conjTranspose_mul_self]
      _ = ‖B‖ ^ 2 := (sq _).symm
  have h_norm_nonneg : 0 ≤ ‖(U : Matrix m' m' ℂ) * B‖ := norm_nonneg _
  have h_B_nonneg : 0 ≤ ‖B‖ := norm_nonneg _
  exact (sq_eq_sq₀ h_norm_nonneg h_B_nonneg).mp h1

omit [DecidableEq m'] in
/-- Right multiplication by unitary star preserves spectral norm.
    Uses the CStarRing structure on square matrices. -/
lemma l2_opNorm_mul_unitary_star_rect (B : Matrix m' n' ℂ) (V : unitaryGroup n' ℂ) :
    ‖B * star (V : Matrix n' n' ℂ)‖ = ‖B‖ := by
  -- Strategy: ‖BV*‖² = ‖(BV*)ᴴ(BV*)‖ = ‖VBᴴBV*‖ = ‖BᴴB‖ = ‖B‖²
  have h_VstarV : (V : Matrix n' n' ℂ) * star (V : Matrix n' n' ℂ) = 1 :=
    mem_unitaryGroup_iff.mp V.2
  have h1 : ‖B * star (V : Matrix n' n' ℂ)‖ ^ 2 = ‖B‖ ^ 2 := by
    calc ‖B * star (V : Matrix n' n' ℂ)‖ ^ 2
        = ‖B * star (V : Matrix n' n' ℂ)‖ * ‖B * star (V : Matrix n' n' ℂ)‖ := sq _
      _ = ‖(B * star (V : Matrix n' n' ℂ))ᴴ * (B * star (V : Matrix n' n' ℂ))‖ := by
          rw [l2_opNorm_conjTranspose_mul_self]
      _ = ‖((star (V : Matrix n' n' ℂ))ᴴ * Bᴴ) * (B * star (V : Matrix n' n' ℂ))‖ := by
          rw [conjTranspose_mul]
      _ = ‖((V : Matrix n' n' ℂ) * Bᴴ) * (B * star (V : Matrix n' n' ℂ))‖ := by
          simp only [star_eq_conjTranspose, conjTranspose_conjTranspose]
      _ = ‖(V : Matrix n' n' ℂ) * (Bᴴ * B) * star (V : Matrix n' n' ℂ)‖ := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
      _ = ‖(V : Matrix n' n' ℂ) * ((Bᴴ * B) * star (V : Matrix n' n' ℂ))‖ := by
          rw [Matrix.mul_assoc]
      _ = ‖(Bᴴ * B) * star (V : Matrix n' n' ℂ)‖ := by
          -- V is unitary on n'×n' square matrices, use CStarRing
          have hV_unitary : (V : Matrix n' n' ℂ) ∈ unitary (Matrix n' n' ℂ) := V.2
          exact CStarRing.norm_mem_unitary_mul _ hV_unitary
      _ = ‖Bᴴ * B‖ := by
          have hVstar_unitary : star (V : Matrix n' n' ℂ) ∈ unitary (Matrix n' n' ℂ) :=
            Unitary.star_mem V.2
          exact CStarRing.norm_mul_mem_unitary (Bᴴ * B) hVstar_unitary
      _ = ‖B‖ * ‖B‖ := by rw [l2_opNorm_conjTranspose_mul_self]
      _ = ‖B‖ ^ 2 := (sq _).symm
  have h_norm_nonneg : 0 ≤ ‖B * star (V : Matrix n' n' ℂ)‖ := norm_nonneg _
  have h_B_nonneg : 0 ≤ ‖B‖ := norm_nonneg _
  exact (sq_eq_sq₀ h_norm_nonneg h_B_nonneg).mp h1

/-- Spectral norm is invariant under conjugation by unitary matrices (rectangular middle).
    ‖U * B * V*‖ = ‖B‖ for U, V unitary and B rectangular. -/
theorem l2_opNorm_unitary_conj_rect (U : unitaryGroup m' ℂ) (V : unitaryGroup n' ℂ)
    (B : Matrix m' n' ℂ) :
    ‖(U : Matrix m' m' ℂ) * B * star (V : Matrix n' n' ℂ)‖ = ‖B‖ := by
  calc ‖(U : Matrix m' m' ℂ) * B * star (V : Matrix n' n' ℂ)‖
      = ‖(U : Matrix m' m' ℂ) * (B * star (V : Matrix n' n' ℂ))‖ := by rw [Matrix.mul_assoc]
    _ = ‖B * star (V : Matrix n' n' ℂ)‖ := l2_opNorm_unitary_mul_rect U _
    _ = ‖B‖ := l2_opNorm_mul_unitary_star_rect B V

/-- The spectral norm of the tail equals the spectral norm of the tail diagonal. -/
theorem l2_opNorm_truncatedSVD_rect_tail (A : Matrix m' n' ℂ) (k : ℕ) :
    ‖truncatedSVD_rect_tail A k‖ = ‖truncatedSingularDiagonal_rect_tail A k‖ := by
  rw [truncatedSVD_rect_tail_eq_USV]
  exact l2_opNorm_unitary_conj_rect
    (SVD.Rectangular.constructedU_rectangular A)
    (SVD.Rectangular.rightUnitary A)
    (truncatedSingularDiagonal_rect_tail A k)

/-! ### DᴴD Entry Calculation for Rectangular Diagonal Tail -/

omit [DecidableEq m'] in
/-- Explicit computation of (DᴴD)(j, j') for D = truncatedSingularDiagonal_rect_tail A k.

    Key insight: D is a "rectangular diagonal" with nonzero entries only when:
    - eigenvaluesBijection m' i = eigenvaluesBijection n' j  (same diagonal index)
    - k ≤ (eigenvaluesBijection n' j).val < min #m' #n'  (in the tail range)

    Therefore DᴴD(j,j') = Σᵢ D̄(j,i) * D(i,j') where the sum collapses to:
    - σₗ² · δⱼⱼ' if (eigenvaluesBijection n' j).val = ℓ and k ≤ ℓ < min
    - 0 otherwise -/
lemma conjTranspose_mul_truncatedSingularDiagonal_rect_tail_apply
    (A : Matrix m' n' ℂ) (k : ℕ) (j j' : n') :
    let D := truncatedSingularDiagonal_rect_tail A k
    (Dᴴ * D) j j' =
      if h : (SVD.Rectangular.eigenvaluesBijection n' j).val = (SVD.Rectangular.eigenvaluesBijection n' j').val ∧
             k ≤ (SVD.Rectangular.eigenvaluesBijection n' j).val ∧
             (SVD.Rectangular.eigenvaluesBijection n' j).val < min (Fintype.card m') (Fintype.card n') then
        Complex.ofReal ((SVD.Rectangular.singularValues A ⟨(SVD.Rectangular.eigenvaluesBijection n' j).val, h.2.2⟩) ^ 2)
      else 0 := by
  intro D
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply]
  change ∑ x, star (truncatedSingularDiagonal_rect_tail A k x j) *
         truncatedSingularDiagonal_rect_tail A k x j' = _
  simp only [truncatedSingularDiagonal_rect_tail]
  set fj := SVD.Rectangular.eigenvaluesBijection n' j with hfj_def
  set fj' := SVD.Rectangular.eigenvaluesBijection n' j' with hfj'_def
  by_cases h_cond : fj.val = fj'.val ∧ k ≤ fj.val ∧ fj.val < min (Fintype.card m') (Fintype.card n')
  · -- Conditions met: sum should be σ²
    rw [dif_pos h_cond]
    have h_eq : fj.val = fj'.val := h_cond.1
    have h_k : k ≤ fj.val := h_cond.2.1
    have h_min : fj.val < min (Fintype.card m') (Fintype.card n') := h_cond.2.2
    have h_fj_lt_m : fj.val < Fintype.card m' := Nat.lt_of_lt_of_le h_min (Nat.min_le_left _ _)
    let i₀ := (SVD.Rectangular.eigenvaluesBijection m').symm ⟨fj.val, h_fj_lt_m⟩
    have h_fi₀ : SVD.Rectangular.eigenvaluesBijection m' i₀ = ⟨fj.val, h_fj_lt_m⟩ :=
      Equiv.apply_symm_apply (SVD.Rectangular.eigenvaluesBijection m') _
    rw [Fintype.sum_eq_single i₀]
    · -- Show the term at i₀ equals σ²
      have h_cond_i₀_j : (SVD.Rectangular.eigenvaluesBijection m' i₀).val =
                           (SVD.Rectangular.eigenvaluesBijection n' j).val ∧
                         (SVD.Rectangular.eigenvaluesBijection m' i₀).val <
                           min (Fintype.card m') (Fintype.card n') ∧
                         k ≤ (SVD.Rectangular.eigenvaluesBijection m' i₀).val := by
        constructor
        · simp only [h_fi₀, ← hfj_def]
        · constructor
          · simp only [h_fi₀]; exact h_min
          · simp only [h_fi₀]; exact h_k
      have h_cond_i₀_j' : (SVD.Rectangular.eigenvaluesBijection m' i₀).val =
                            (SVD.Rectangular.eigenvaluesBijection n' j').val ∧
                          (SVD.Rectangular.eigenvaluesBijection m' i₀).val <
                            min (Fintype.card m') (Fintype.card n') ∧
                          k ≤ (SVD.Rectangular.eigenvaluesBijection m' i₀).val := by
        constructor
        · simp only [h_fi₀, ← hfj'_def, h_eq]
        · constructor
          · simp only [h_fi₀]; exact h_min
          · simp only [h_fi₀]; exact h_k
      simp only [dif_pos h_cond_i₀_j, dif_pos h_cond_i₀_j']
      -- star (↑σ) * ↑σ = ↑(σ²) since σ is real
      simp only [RCLike.star_def, Complex.conj_ofReal]
      rw [← Complex.ofReal_mul, ← sq]
      congr 1
      simp only [h_fi₀, hfj_def]
    · -- Show all other terms are 0
      intro i hi
      by_cases h_fi_fj : (SVD.Rectangular.eigenvaluesBijection m' i).val = fj.val
      · have h_fi_eq : SVD.Rectangular.eigenvaluesBijection m' i = ⟨fj.val, h_fj_lt_m⟩ := by
          ext; exact h_fi_fj
        have h_i_eq : i = i₀ :=
          (SVD.Rectangular.eigenvaluesBijection m').injective (by rw [h_fi_eq, h_fi₀])
        exact absurd h_i_eq hi
      · have h_neg : ¬((SVD.Rectangular.eigenvaluesBijection m' i).val = fj.val ∧
                       (SVD.Rectangular.eigenvaluesBijection m' i).val <
                         min (Fintype.card m') (Fintype.card n') ∧
                       k ≤ (SVD.Rectangular.eigenvaluesBijection m' i).val) := by
          intro ⟨h1, _, _⟩; exact h_fi_fj h1
        rw [dif_neg h_neg, star_zero, zero_mul]
  · -- Conditions not met: sum should be 0
    rw [dif_neg h_cond]
    push_neg at h_cond
    apply Finset.sum_eq_zero
    intro i _
    by_cases h_fj_eq : fj.val = fj'.val
    · by_cases h_k_le : k ≤ fj.val
      · have h_ge_min := h_cond h_fj_eq h_k_le
        by_cases h_match_j : (SVD.Rectangular.eigenvaluesBijection m' i).val = fj.val
        · have h_neg_j : ¬((SVD.Rectangular.eigenvaluesBijection m' i).val = fj.val ∧
                          (SVD.Rectangular.eigenvaluesBijection m' i).val <
                            min (Fintype.card m') (Fintype.card n') ∧
                          k ≤ (SVD.Rectangular.eigenvaluesBijection m' i).val) := by
            intro ⟨_, h_lt_min, _⟩
            rw [h_match_j] at h_lt_min
            exact Nat.not_lt.mpr h_ge_min h_lt_min
          rw [dif_neg h_neg_j, star_zero, zero_mul]
        · have h_neg_j : ¬((SVD.Rectangular.eigenvaluesBijection m' i).val = fj.val ∧
                          (SVD.Rectangular.eigenvaluesBijection m' i).val <
                            min (Fintype.card m') (Fintype.card n') ∧
                          k ≤ (SVD.Rectangular.eigenvaluesBijection m' i).val) := by
            intro ⟨h1, _, _⟩; exact h_match_j h1
          rw [dif_neg h_neg_j, star_zero, zero_mul]
      · by_cases h_match_j : (SVD.Rectangular.eigenvaluesBijection m' i).val = fj.val
        · have h_neg_j : ¬((SVD.Rectangular.eigenvaluesBijection m' i).val = fj.val ∧
                          (SVD.Rectangular.eigenvaluesBijection m' i).val <
                            min (Fintype.card m') (Fintype.card n') ∧
                          k ≤ (SVD.Rectangular.eigenvaluesBijection m' i).val) := by
            intro ⟨_, _, h_k_le'⟩
            rw [h_match_j] at h_k_le'
            exact Nat.not_lt.mpr h_k_le' (Nat.not_le.mp h_k_le)
          rw [dif_neg h_neg_j, star_zero, zero_mul]
        · have h_neg_j : ¬((SVD.Rectangular.eigenvaluesBijection m' i).val = fj.val ∧
                          (SVD.Rectangular.eigenvaluesBijection m' i).val <
                            min (Fintype.card m') (Fintype.card n') ∧
                          k ≤ (SVD.Rectangular.eigenvaluesBijection m' i).val) := by
            intro ⟨h1, _, _⟩; exact h_match_j h1
          rw [dif_neg h_neg_j, star_zero, zero_mul]
    · by_cases h_match_j : (SVD.Rectangular.eigenvaluesBijection m' i).val = fj.val
      · have h_not_match_j' : (SVD.Rectangular.eigenvaluesBijection m' i).val ≠ fj'.val := by
          rw [h_match_j]; exact h_fj_eq
        have h_neg_j' : ¬((SVD.Rectangular.eigenvaluesBijection m' i).val = fj'.val ∧
                         (SVD.Rectangular.eigenvaluesBijection m' i).val <
                           min (Fintype.card m') (Fintype.card n') ∧
                         k ≤ (SVD.Rectangular.eigenvaluesBijection m' i).val) := by
          intro ⟨h1, _, _⟩; exact h_not_match_j' h1
        rw [dif_neg h_neg_j', mul_zero]
      · have h_neg_j : ¬((SVD.Rectangular.eigenvaluesBijection m' i).val = fj.val ∧
                         (SVD.Rectangular.eigenvaluesBijection m' i).val <
                           min (Fintype.card m') (Fintype.card n') ∧
                         k ≤ (SVD.Rectangular.eigenvaluesBijection m' i).val) := by
          intro ⟨h1, _, _⟩; exact h_match_j h1
        rw [dif_neg h_neg_j, star_zero, zero_mul]

/-! ### Spectral Norm of Rectangular Diagonal Matrix -/

omit [DecidableEq m'] in
/-- DᴴD diagonal entry at j equals σ²_{bijection(j)} when k ≤ bijection(j) < min, else 0.
    This is a specialized version of `conjTranspose_mul_truncatedSingularDiagonal_rect_tail_apply`
    for the diagonal case j = j'. -/
lemma DtD_diagonal_entry (A : Matrix m' n' ℂ) (k : ℕ) (j : n') :
    let D := truncatedSingularDiagonal_rect_tail A k
    (Dᴴ * D) j j =
      if h : k ≤ (SVD.Rectangular.eigenvaluesBijection n' j).val ∧
             (SVD.Rectangular.eigenvaluesBijection n' j).val < min (Fintype.card m') (Fintype.card n') then
        Complex.ofReal ((SVD.Rectangular.singularValues A
          ⟨(SVD.Rectangular.eigenvaluesBijection n' j).val, h.2⟩) ^ 2)
      else 0 := by
  intro D
  rw [conjTranspose_mul_truncatedSingularDiagonal_rect_tail_apply]
  simp only [true_and]

/-- For a diagonal Hermitian matrix H, the inner product ⟨Hx, x⟩ equals Σⱼ H_jj |xⱼ|².
    The real part is Σⱼ Re(H_jj) |xⱼ|². -/
lemma inner_diagonal_matrix_eq_sum
    (H : Matrix n' n' ℂ) (hH : H.IsHermitian) (h_diag : ∀ i j, i ≠ j → H i j = 0)
    (x : EuclideanSpace ℂ n') :
    @inner ℂ (EuclideanSpace ℂ n') _ (Matrix.toEuclideanLin H x) x =
      ∑ k, H k k * (starRingEnd ℂ (x.ofLp k) * x.ofLp k) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, Matrix.toEuclideanLin_apply]
  simp only [dotProduct, Matrix.mulVec, dotProduct, Pi.star_apply]
  -- The inner sum over j simplifies to H i i * x i for diagonal matrices
  have h_diagonal_sum : ∀ i, ∑ j, H i j * x.ofLp j = H i i * x.ofLp i := by
    intro i
    apply Finset.sum_eq_single i
    · intro j _ hji
      rw [h_diag i j (Ne.symm hji), zero_mul]
    · intro h; exact (h (Finset.mem_univ i)).elim
  simp_rw [h_diagonal_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [star_mul']
  -- For Hermitian H, star (H i i) = H i i
  have h_star_diag := hH.apply i i
  simp only at h_star_diag
  rw [h_star_diag]
  -- star = starRingEnd ℂ for Complex
  simp only [starRingEnd_apply]
  ring

omit [Fintype n'] [DecidableEq n'] in
/-- For a Hermitian matrix, diagonal entries are real. -/
lemma hermitian_diagonal_real (H : Matrix n' n' ℂ) (hH : H.IsHermitian) (i : n') :
    H i i = (H i i).re := by
  -- IsHermitian.apply gives star (A j i) = A i j, so for i=j: star (H i i) = H i i
  have h_star : star (H i i) = H i i := hH.apply i i
  -- star = conj for Complex, so Im (H i i) = 0
  have h_im_zero : (H i i).im = 0 := by
    rw [← Complex.conj_eq_iff_im]
    exact h_star
  -- If Im = 0, then z = z.re
  apply Complex.ext
  · rfl
  · simp only [Complex.ofReal_im, h_im_zero]

/-- For a unit vector and diagonal Hermitian matrix with diagonal entries ≤ bound,
    the Rayleigh quotient is ≤ bound. -/
lemma rayleigh_diagonal_le_bound
    (H : Matrix n' n' ℂ) (hH_herm : H.IsHermitian)
    (h_diag : ∀ i j, i ≠ j → H i j = 0)
    (bound : ℝ) (h_diag_le : ∀ i, (H i i).re ≤ bound)
    (x : EuclideanSpace ℂ n') (hx : ‖x‖ = 1) :
    (@inner ℂ (EuclideanSpace ℂ n') _ (Matrix.toEuclideanLin H x) x).re ≤ bound := by
  rw [inner_diagonal_matrix_eq_sum H hH_herm h_diag x, Complex.re_sum]
  calc ∑ k, (H k k * (starRingEnd ℂ (x.ofLp k) * x.ofLp k)).re
      = ∑ k, (H k k).re * Complex.normSq (x.ofLp k) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [hermitian_diagonal_real H hH_herm k]
        -- (↑r : ℂ) * z has Re = r * Re(z) when Im(↑r) = 0
        simp only [starRingEnd_apply]
        simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re]
        -- star on ℂ equals starRingEnd ℂ = conj
        rw [show star (x.ofLp k) = (starRingEnd ℂ) (x.ofLp k) from rfl]
        simp only [Complex.conj_re, Complex.conj_im, neg_mul, sub_neg_eq_add]
        -- re² + im² = normSq
        simp only [Complex.normSq_apply, zero_mul, sub_zero]
    _ ≤ ∑ k, bound * Complex.normSq (x.ofLp k) := by
        apply Finset.sum_le_sum
        intro k _
        apply mul_le_mul_of_nonneg_right (h_diag_le k) (Complex.normSq_nonneg _)
    _ = bound * ∑ k, Complex.normSq (x.ofLp k) := by rw [Finset.mul_sum]
    _ = bound * ‖x‖ ^ 2 := by
        congr 1
        rw [EuclideanSpace.norm_eq]
        -- Need: (√(∑ ‖xₖ‖²))² = ∑ Complex.normSq xₖ
        rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ _)]
        apply Finset.sum_congr rfl
        intro k _
        rw [← Complex.sq_norm]
    _ = bound := by rw [hx, one_pow, mul_one]

/-- For a diagonal-like matrix, diagonal entries are in the spectrum.
    Standard basis vector e_j is an eigenvector with eigenvalue H_jj. -/
lemma diagonal_entry_in_spectrum
    (H : Matrix n' n' ℂ) (h_diag : ∀ i j, i ≠ j → H i j = 0) (j : n') :
    H j j ∈ spectrum ℂ H := by
  rw [← Matrix.spectrum_toLin']
  rw [Module.End.hasEigenvalue_iff_mem_spectrum.symm]
  -- Show e_j is an eigenvector with eigenvalue H_jj
  apply Module.End.hasEigenvalue_of_hasEigenvector (x := Pi.single j 1)
  constructor
  · -- e_j is in eigenspace for H_jj
    rw [Module.End.mem_eigenspace_iff]
    ext i
    simp only [Matrix.toLin'_apply, Pi.smul_apply]
    rw [Matrix.mulVec, dotProduct]
    by_cases h_eq : i = j
    · -- i = j case
      subst h_eq
      simp only [Pi.single_eq_same, smul_eq_mul, mul_one]
      have h_sum_eq : ∑ k, H i k * ((Pi.single i 1 : n' → ℂ) k) = H i i := by
        rw [Fintype.sum_eq_single i]
        · simp only [Pi.single_eq_same, mul_one]
        · intro k hk
          simp [Ne.symm hk, mul_zero]
      simp only [h_sum_eq]
    · -- i ≠ j case
      simp only [Pi.single_eq_of_ne h_eq, smul_zero]
      have h_sum_eq : ∑ k, H i k * ((Pi.single j 1 : n' → ℂ) k) = H i j := by
        rw [Fintype.sum_eq_single j]
        · simp only [Pi.single_eq_same, mul_one]
        · intro k hk
          simp [Ne.symm hk, mul_zero]
      rw [h_sum_eq, h_diag i j h_eq]
  · -- e_j ≠ 0
    intro h_zero
    have h_one : (Pi.single j 1 : n' → ℂ) j = 1 := Pi.single_eq_same j 1
    rw [h_zero] at h_one
    simp only [Pi.zero_apply, zero_ne_one] at h_one

/-- For a Hermitian matrix H with zero off-diagonal entries, every eigenvalue is at most any
    upper bound on the real parts of the diagonal entries.
    This is the upper bound helper for `l2_opNorm_truncatedSingularDiagonal_rect_tail`. -/
lemma eigenvalues_le_max_diagonal_entry_of_diagonal_psd
    (H : Matrix n' n' ℂ) (hH_herm : H.IsHermitian)
    (h_diag_zeros : ∀ j j', j ≠ j' → H j j' = 0)
    (bound : ℝ) (h_diag_le : ∀ j, Complex.re (H j j) ≤ bound) :
    ∀ j : n', hH_herm.eigenvalues j ≤ bound := by
  intro j
  by_cases h_nonempty : Nonempty n'
  · -- Case: n' is nonempty
    have h_eq := Matrix.IsHermitian.eigenvalues.eq_1 hH_herm j
    rw [h_eq]
    have h_antitone := hH_herm.eigenvalues₀_antitone
    have h_le_max : hH_herm.eigenvalues₀ ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm j) ≤
        hH_herm.eigenvalues₀ ⟨0, Fintype.card_pos⟩ :=
      h_antitone (Fin.zero_le _)
    apply le_trans h_le_max
    -- Now show max eigenvalue ≤ bound
    -- Strategy: eigenvalue = Rayleigh quotient on eigenvector ≤ bound
    -- The max eigenvalue eigenvalues₀ 0 corresponds to some eigenvalues i₀
    -- where i₀ = (Fintype.equivOfCardEq _) ⟨0, _⟩
    let i₀ := (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n'))).symm.symm
               ⟨0, Fintype.card_pos⟩
    have h_eigenvalue_eq : hH_herm.eigenvalues₀ ⟨0, Fintype.card_pos⟩ = hH_herm.eigenvalues i₀ := by
      simp only [Matrix.IsHermitian.eigenvalues.eq_1, Equiv.symm_symm, Equiv.symm_apply_apply, i₀]
    rw [h_eigenvalue_eq]
    -- Use rayleigh_eq_eigenvalue_on_eigenvector
    have h_rayleigh := CourantFischer.rayleigh_eq_eigenvalue_on_eigenvector H hH_herm i₀
    rw [← h_rayleigh]
    -- Apply the Rayleigh bound lemma for diagonal matrices
    have h_unit : ‖hH_herm.eigenvectorBasis i₀‖ = 1 := hH_herm.eigenvectorBasis.orthonormal.1 i₀
    exact rayleigh_diagonal_le_bound H hH_herm h_diag_zeros bound h_diag_le
            (hH_herm.eigenvectorBasis i₀) h_unit
  · -- Case: n' is empty - vacuously true
    exact (h_nonempty (Nonempty.intro j)).elim


omit [DecidableEq m'] in
/-- The k-th singular value squared is achieved as a diagonal entry.
    This is the lower bound helper for `l2_opNorm_truncatedSingularDiagonal_rect_tail`. -/
lemma sigma_sq_is_DtD_entry (A : Matrix m' n' ℂ) (k : ℕ)
    (hk : k < min (Fintype.card m') (Fintype.card n')) :
    let D := truncatedSingularDiagonal_rect_tail A k
    let j := SVD.Rectangular.embedMinToN (m := m') ⟨k, hk⟩
    (Dᴴ * D) j j = Complex.ofReal ((singularValues₀_rect A ⟨k, hk⟩) ^ 2) := by
  intro D j
  rw [DtD_diagonal_entry]
  -- Show the condition is satisfied
  have h_bijection : (SVD.Rectangular.eigenvaluesBijection n' j).val = k := by
    unfold j
    rw [Matrix.SVD.Rectangular.eigenvaluesBijection_embedMinToN]
    simp only [Fin.coe_castLE]
  simp only [h_bijection, le_refl, hk, and_self, ↓reduceDIte]
  -- Now need: singularValues A ⟨k, hk⟩ = singularValues₀_rect A ⟨k, hk⟩
  rfl

/-- The spectral norm of a rectangular diagonal matrix equals the maximum entry.
    For the tail diagonal, this is σₖ (the k-th singular value).

    **Proof approach:**
    1. Use `l2_opNorm_conjTranspose_mul_self`: ‖D‖² = ‖DᴴD‖
    2. DᴴD is an n'×n' Hermitian matrix with entries σᵢ² on diagonal positions
       where index ≥ k, and 0 elsewhere
    3. For positive semidefinite H, ‖H‖ = max eigenvalue = max diagonal entry
    4. max{σₖ², σₖ₊₁², ...} = σₖ² since singular values are antitone
    5. Therefore ‖D‖ = √(σₖ²) = σₖ

    Alternative direct approach via operator norm definition:
    - ‖D‖ = sup_{‖x‖=1} ‖Dx‖
    - For rectangular diagonal, Dx = (D₀₀x₀, D₁₁x₁, ...) with 0s elsewhere
    - Maximum achieved at standard basis vector eₖ: ‖Deₖ‖ = σₖ -/
lemma l2_opNorm_truncatedSingularDiagonal_rect_tail (A : Matrix m' n' ℂ) (k : ℕ)
    (hk : k < min (Fintype.card m') (Fintype.card n')) :
    ‖truncatedSingularDiagonal_rect_tail A k‖ = singularValues₀_rect A ⟨k, hk⟩ := by
  set D := truncatedSingularDiagonal_rect_tail A k
  have h_norm_nonneg : 0 ≤ ‖D‖ := norm_nonneg D
  have h_sv_nonneg : 0 ≤ singularValues₀_rect A ⟨k, hk⟩ := singularValues₀_rect_nonneg A ⟨k, hk⟩
  -- Strategy: Show ‖D‖² = σₖ(A)², then conclude ‖D‖ = σₖ(A) by nonnegativity
  suffices h_sq : ‖D‖ ^ 2 = singularValues₀_rect A ⟨k, hk⟩ ^ 2 by
    have := sq_eq_sq₀ h_norm_nonneg h_sv_nonneg
    rwa [this] at h_sq
  -- Use CStarRing identity: ‖D‖² = ‖DᴴD‖
  have h_DtD_sq : ‖Dᴴ * D‖ = ‖D‖ * ‖D‖ := l2_opNorm_conjTranspose_mul_self D
  rw [sq, ← h_DtD_sq]
  -- Now goal is: ‖Dᴴ * D‖ = σₖ(A)²
  -- DᴴD is PSD and Hermitian

  have h_psd : (Dᴴ * D).PosSemidef := posSemidef_conjTranspose_mul_self D
  have h_herm := h_psd.isHermitian
  -- Nonemptiness for Finset.sup'
  have h_nonempty : Nonempty n' := by
    have h_min_pos : 0 < min (Fintype.card m') (Fintype.card n') := Nat.lt_of_le_of_lt (Nat.zero_le k) hk
    have h_card : 0 < Fintype.card n' := Nat.lt_of_lt_of_le h_min_pos (Nat.min_le_right _ _)
    exact Fintype.card_pos_iff.mp h_card
  -- For PSD, ‖DᴴD‖ = max eigenvalue
  rw [Matrix.KroneckerRearrangement.l2_opNorm_posSemidef_eq_sup_eigenvalues (Dᴴ * D) h_psd]
  -- We prove this by showing both ≤ and ≥
  apply le_antisymm
  -- Upper bound: sup' eigenvalues(DᴴD) ≤ σₖ(A)²
  -- All eigenvalues of DᴴD are ≤ σₖ(A)² since they're from {σ_i² : i ≥ k} ∪ {0}
  -- and σ is antitone.
  · apply Finset.sup'_le
    intro j _
    -- Use that all eigenvalues ≤ σₖ² because DᴴD is diagonal with entries ≤ σₖ²
    -- DᴴD is diagonal-like (off-diagonal = 0) by conjTranspose_mul_truncatedSingularDiagonal_rect_tail_apply
    have h_diag_zeros : ∀ i j', i ≠ j' → (Dᴴ * D) i j' = 0 := by
      intro i j' h_ne
      rw [conjTranspose_mul_truncatedSingularDiagonal_rect_tail_apply]
      have h_bijection_ne : (SVD.Rectangular.eigenvaluesBijection n' i).val ≠
                            (SVD.Rectangular.eigenvaluesBijection n' j').val := by
        intro h_eq
        have h_inj := (SVD.Rectangular.eigenvaluesBijection n').injective
        have h_vals_eq : (SVD.Rectangular.eigenvaluesBijection n' i) =
                         (SVD.Rectangular.eigenvaluesBijection n' j') := Fin.ext h_eq
        exact h_ne (h_inj h_vals_eq)
      simp only [h_bijection_ne, false_and, ↓reduceDIte]
    -- Each diagonal entry is either 0 or σᵢ² for i ≥ k, all ≤ σₖ²
    have h_diag_le : ∀ i, Complex.re ((Dᴴ * D) i i) ≤ (singularValues₀_rect A ⟨k, hk⟩) ^ 2 := by
      intro i
      rw [DtD_diagonal_entry]
      split_ifs with h_cond
      · -- Entry is σᵢ²
        simp only [Complex.ofReal_re]
        have h_le_k : k ≤ (SVD.Rectangular.eigenvaluesBijection n' i).val := h_cond.1
        -- Use antitone property of singular values
        have h_antitone := SVD.Rectangular.singularValues_antitone A
        have h_sv_le : SVD.Rectangular.singularValues A
            ⟨(SVD.Rectangular.eigenvaluesBijection n' i).val, h_cond.2⟩ ≤
            SVD.Rectangular.singularValues A ⟨k, hk⟩ := by
          apply h_antitone
          simp only [Fin.mk_le_mk]
          exact h_le_k
        -- singularValues = singularValues₀_rect
        simp only [SVD.Rectangular.singularValues] at h_sv_le ⊢
        -- Square both sides: since both are nonneg, sv_i ≤ sv_k → sv_i² ≤ sv_k²
        have h_nonneg_i := singularValues₀_rect_nonneg A
            ⟨(SVD.Rectangular.eigenvaluesBijection n' i).val, h_cond.2⟩
        have h_nonneg_k := singularValues₀_rect_nonneg A ⟨k, hk⟩
        exact (sq_le_sq₀ h_nonneg_i h_nonneg_k).mpr h_sv_le
      · -- Entry is 0
        simp only [Complex.zero_re]
        apply sq_nonneg
    exact eigenvalues_le_max_diagonal_entry_of_diagonal_psd
      (Dᴴ * D) h_herm h_diag_zeros ((singularValues₀_rect A ⟨k, hk⟩) ^ 2) h_diag_le j

  -- Lower bound: σₖ(A)² ≤ sup' eigenvalues(DᴴD)
  -- Strategy: σₖ² is a diagonal entry of DᴴD, and for diagonal Hermitian matrices,
  -- the eigenvalues are exactly the diagonal entries. So max eigenvalue ≥ σₖ².
  · -- The key index where σₖ² appears on the diagonal
    let j₀ := SVD.Rectangular.embedMinToN (m := m') ⟨k, hk⟩
    -- DᴴD is diagonal with (DᴴD)_j₀j₀ = σₖ²
    have h_entry : (Dᴴ * D) j₀ j₀ = Complex.ofReal ((singularValues₀_rect A ⟨k, hk⟩) ^ 2) :=
      sigma_sq_is_DtD_entry A k hk
    -- DᴴD is diagonal-like (off-diagonal entries are 0)
    have h_diag_zeros : ∀ i j', i ≠ j' → (Dᴴ * D) i j' = 0 := by
      intro i j' h_ne
      rw [conjTranspose_mul_truncatedSingularDiagonal_rect_tail_apply]
      have h_bijection_ne : (SVD.Rectangular.eigenvaluesBijection n' i).val ≠
                            (SVD.Rectangular.eigenvaluesBijection n' j').val := by
        intro h_eq
        have h_inj := (SVD.Rectangular.eigenvaluesBijection n').injective
        have h_vals_eq : (SVD.Rectangular.eigenvaluesBijection n' i) =
                         (SVD.Rectangular.eigenvaluesBijection n' j') := Fin.ext h_eq
        exact h_ne (h_inj h_vals_eq)
      simp only [h_bijection_ne, false_and, ↓reduceDIte]

    -- Use the helper lemma: diagonal entries are in the spectrum
    have h_in_spectrum : Complex.ofReal ((singularValues₀_rect A ⟨k, hk⟩) ^ 2) ∈ spectrum ℂ (Dᴴ * D) := by
      rw [← h_entry]
      exact diagonal_entry_in_spectrum (Dᴴ * D) h_diag_zeros j₀

    -- Extract the eigenvalue from spectrum membership
    rw [Matrix.IsHermitian.spectrum_eq_image_range h_herm] at h_in_spectrum
    simp only [Set.mem_image, Set.mem_range] at h_in_spectrum
    obtain ⟨σ_val, ⟨i, h_i⟩, h_eq⟩ := h_in_spectrum
    -- Now h_i : h_herm.eigenvalues i = σ_val
    -- and h_eq : ↑σ_val = ↑(σₖ²)
    have h_eigenval_eq : h_herm.eigenvalues i = (singularValues₀_rect A ⟨k, hk⟩) ^ 2 := by
      have h_inj := Complex.ofReal_injective h_eq
      rw [h_i]
      exact h_inj
    rw [← h_eigenval_eq]
    exact Finset.le_sup' h_herm.eigenvalues (Finset.mem_univ i)



/-! ### Main Theorem -/

/-- **Spectral error of rectangular truncated SVD equals the (k+1)-th singular value.**
    ‖A - Aₖ‖₂ = σₖ₊₁(A) for rectangular matrices.

    This generalizes spectral_error_truncatedSVD from square to rectangular matrices. -/
theorem spectral_error_truncatedSVD_rect
    (A : Matrix m' n' ℂ) (k : ℕ) (hk : k < min (Fintype.card m') (Fintype.card n')) :
    ‖A - truncatedSVD_rect A k‖ = singularValues₀_rect A ⟨k, hk⟩ := by
  -- Step 1: A - Aₖ = tail
  have h_diff : A - truncatedSVD_rect A k = truncatedSVD_rect_tail A k := rfl
  rw [h_diff]
  -- Step 2: ‖tail‖ = ‖Σ_tail‖ by unitary invariance
  rw [l2_opNorm_truncatedSVD_rect_tail]
  -- Step 3: ‖Σ_tail‖ = σₖ
  exact l2_opNorm_truncatedSingularDiagonal_rect_tail A k hk

end SpectralErrorRect

/-! ## Part 3b: Frobenius Error Formula for Rectangular Matrices

‖A - truncatedSVD_rect A k‖_F² = Σ_{i ≥ k} σᵢ², the sum of the squared discarded singular
values. Here ‖·‖ is the Frobenius norm.
-/

section FrobeniusErrorRect

variable {m' n' : Type*} [Fintype m'] [Fintype n'] [DecidableEq m'] [DecidableEq n']

attribute [local instance] Matrix.frobeniusSeminormedAddCommGroup

/-- **The Frobenius norm is unitarily invariant** (rectangular): ‖U B V*‖_F = ‖B‖_F. -/
theorem frobenius_norm_unitary_conj_rect (U : unitaryGroup m' ℂ) (V : unitaryGroup n' ℂ)
    (B : Matrix m' n' ℂ) :
    ‖(U : Matrix m' m' ℂ) * B * star (V : Matrix n' n' ℂ)‖ = ‖B‖ := by
  have h_star_mem : star (V : Matrix n' n' ℂ) ∈ unitaryGroup n' ℂ := by
    rw [mem_unitaryGroup_iff']
    simp only [star_star]
    exact mem_unitaryGroup_iff.mp V.2
  let Vstar : unitaryGroup n' ℂ := ⟨star (V : Matrix n' n' ℂ), h_star_mem⟩
  calc ‖(U : Matrix m' m' ℂ) * B * star (V : Matrix n' n' ℂ)‖
      = ‖(U : Matrix m' m' ℂ) * B * (Vstar : Matrix n' n' ℂ)‖ := rfl
    _ = ‖(U : Matrix m' m' ℂ) * B‖ := FrobeniusNorm.frobenius_norm_mul_unitary _ Vstar
    _ = ‖B‖ := FrobeniusNorm.frobenius_norm_unitary_mul U B

/-- **Frobenius error of the rectangular truncated SVD:**
    ‖A - truncatedSVD_rect A k‖_F² = Σᵢ (truncatedSingularValues_rect_tail A k i)², the sum of
    σᵢ² over the discarded indices i ≥ k. -/
theorem frobenius_error_truncatedSVD_rect (A : Matrix m' n' ℂ) (k : ℕ) :
    ‖A - truncatedSVD_rect A k‖ ^ 2 = ∑ i, (truncatedSingularValues_rect_tail A k i) ^ 2 := by
  set D := truncatedSingularDiagonal_rect_tail A k with hD
  -- Step 1: A - Aₖ = U D V*, so ‖A - Aₖ‖_F = ‖D‖_F
  have h_norm : ‖A - truncatedSVD_rect A k‖ = ‖D‖ := by
    have h_tail : A - truncatedSVD_rect A k =
        (SVD.Rectangular.constructedU_rectangular A : Matrix m' m' ℂ) * D *
          star (SVD.Rectangular.rightUnitary A : Matrix n' n' ℂ) :=
      truncatedSVD_rect_tail_eq_USV A k
    rw [h_tail]
    exact frobenius_norm_unitary_conj_rect _ _ D
  -- Step 2: ‖D‖_F² = Re tr(DᴴD) = Σⱼ Re (DᴴD)ⱼⱼ
  rw [h_norm, FrobeniusNorm.frobenius_norm_sq_eq_trace, Matrix.trace, Complex.re_sum]
  -- Step 3: the diagonal entries of DᴴD are σ² on the tail and 0 elsewhere
  let g : Fin (Fintype.card n') → ℝ := fun b =>
    if h : k ≤ b.val ∧ b.val < min (Fintype.card m') (Fintype.card n') then
      (SVD.Rectangular.singularValues A ⟨b.val, h.2⟩) ^ 2
    else 0
  have h_diag : ∀ j : n',
      ((Dᴴ * D).diag j).re = g (SVD.Rectangular.eigenvaluesBijection n' j) := by
    intro j
    have h_entry : (Dᴴ * D) j j =
        if h : k ≤ (SVD.Rectangular.eigenvaluesBijection n' j).val ∧
            (SVD.Rectangular.eigenvaluesBijection n' j).val <
              min (Fintype.card m') (Fintype.card n') then
          Complex.ofReal ((SVD.Rectangular.singularValues A
            ⟨(SVD.Rectangular.eigenvaluesBijection n' j).val, h.2⟩) ^ 2)
        else 0 :=
      DtD_diagonal_entry A k j
    rw [Matrix.diag_apply, h_entry]
    simp only [g]
    split_ifs <;> simp
  simp only [h_diag]
  -- Step 4: reindex n' → Fin #n', then drop the indices ≥ min #m' #n'
  rw [Equiv.sum_comp (SVD.Rectangular.eigenvaluesBijection n') g]
  symm
  apply Fintype.sum_of_injective (Fin.castLE (Nat.min_le_right _ _)) (Fin.castLE_injective _)
  · -- Indices ≥ min #m' #n' contribute 0
    intro b hb
    have hcond : ¬(k ≤ b.val ∧ b.val < min (Fintype.card m') (Fintype.card n')) := by
      rintro ⟨_, hb_lt⟩
      exact hb ⟨⟨b.val, hb_lt⟩, rfl⟩
    show (if h : k ≤ b.val ∧ b.val < min (Fintype.card m') (Fintype.card n') then
      (SVD.Rectangular.singularValues A ⟨b.val, h.2⟩) ^ 2 else 0) = 0
    rw [dif_neg hcond]
  · -- On Fin (min #m' #n') the summands agree
    intro c
    show (truncatedSingularValues_rect_tail A k c) ^ 2 =
      (if h : k ≤ c.val ∧ c.val < min (Fintype.card m') (Fintype.card n') then
        (SVD.Rectangular.singularValues A ⟨c.val, h.2⟩) ^ 2 else 0)
    by_cases hc : k ≤ c.val
    · have hcond : k ≤ c.val ∧ c.val < min (Fintype.card m') (Fintype.card n') := ⟨hc, c.isLt⟩
      rw [truncatedSingularValues_rect_tail_eq_of_ge A k c hc]
      exact (dif_pos hcond).symm
    · have hcond : ¬(k ≤ c.val ∧ c.val < min (Fintype.card m') (Fintype.card n')) :=
        fun h => hc h.1
      rw [truncatedSingularValues_rect_tail_eq_zero_of_lt A k c (not_le.mp hc), dif_neg hcond,
        zero_pow two_ne_zero]

end FrobeniusErrorRect

/-! ## Part 3c: Eckart–Young for Rectangular Matrices

Both optimality theorems follow from rectangular Thompson interlacing
(`Matrix.WeylInequality.interlacing_low_rank_subtraction_rect`): if rank(B) ≤ k, then
σⱼ(A) ≤ σⱼ₋ₖ(A - B) for j ≥ k.
-/

section EckartYoungRect

variable {m' n' : Type*} [Fintype m'] [Fintype n'] [DecidableEq m'] [DecidableEq n']

/-- **Tail sum bound behind Eckart–Young:** if rank(B) ≤ k, then the squared discarded
    singular values of A sum to at most the squared singular values of A - B:
    Σᵢ (truncatedSingularValues_rect_tail A k i)² ≤ Σᵢ σᵢ(A - B)². -/
theorem sum_sq_tail_le_sum_sq_singularValues_sub (A B : Matrix m' n' ℂ) (k : ℕ)
    (hB : B.rank ≤ k) :
    ∑ i, (truncatedSingularValues_rect_tail A k i) ^ 2 ≤
      ∑ i, (SVD.Rectangular.singularValues (A - B) i) ^ 2 := by
  -- Shift j ↦ j - k on the tail indices {j ≥ k}
  let shift : Fin (min (Fintype.card m') (Fintype.card n')) →
      Fin (min (Fintype.card m') (Fintype.card n')) := fun j => ⟨j.val - k, by omega⟩
  let g : Fin (min (Fintype.card m') (Fintype.card n')) → ℝ := fun j =>
    (SVD.Rectangular.singularValues (A - B) j) ^ 2
  -- Step 1: the tail sum is a sum over {j ≥ k}
  have h_lhs : ∑ i, (truncatedSingularValues_rect_tail A k i) ^ 2 =
      ∑ j ∈ Finset.univ.filter (fun j : Fin (min (Fintype.card m') (Fintype.card n')) =>
        k ≤ j.val), (SVD.Rectangular.singularValues A j) ^ 2 := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : k ≤ j.val
    · rw [if_pos hj, truncatedSingularValues_rect_tail_eq_of_ge A k j hj]
    · rw [if_neg hj, truncatedSingularValues_rect_tail_eq_zero_of_lt A k j (not_le.mp hj),
        zero_pow two_ne_zero]
  -- Step 2: termwise interlacing σⱼ(A) ≤ σⱼ₋ₖ(A - B)
  have h_term : ∀ j ∈ Finset.univ.filter
      (fun j : Fin (min (Fintype.card m') (Fintype.card n')) => k ≤ j.val),
      (SVD.Rectangular.singularValues A j) ^ 2 ≤ g (shift j) := by
    intro j hj
    have hjk : k ≤ j.val := (Finset.mem_filter.mp hj).2
    have h := Matrix.WeylInequality.interlacing_low_rank_subtraction_rect A B k hB j hjk
    exact (sq_le_sq₀ (SVD.Rectangular.singularValues_nonneg A j)
      (SVD.Rectangular.singularValues_nonneg (A - B) (shift j))).mpr h
  -- Step 3: the shift is injective on {j ≥ k}, so the shifted sum is at most the full sum
  have h_inj : Set.InjOn shift
      (↑(Finset.univ.filter
        (fun j : Fin (min (Fintype.card m') (Fintype.card n')) => k ≤ j.val)) :
        Set (Fin (min (Fintype.card m') (Fintype.card n')))) := by
    intro j₁ hj₁ j₂ hj₂ heq
    have h1 : k ≤ j₁.val := (Finset.mem_filter.mp (Finset.mem_coe.mp hj₁)).2
    have h2 : k ≤ j₂.val := (Finset.mem_filter.mp (Finset.mem_coe.mp hj₂)).2
    have h_val : j₁.val - k = j₂.val - k := congrArg Fin.val heq
    exact Fin.ext (by omega)
  calc ∑ i, (truncatedSingularValues_rect_tail A k i) ^ 2
      = ∑ j ∈ Finset.univ.filter (fun j : Fin (min (Fintype.card m') (Fintype.card n')) =>
          k ≤ j.val), (SVD.Rectangular.singularValues A j) ^ 2 := h_lhs
    _ ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin (min (Fintype.card m') (Fintype.card n')) =>
          k ≤ j.val), g (shift j) := Finset.sum_le_sum h_term
    _ = ∑ j ∈ (Finset.univ.filter (fun j : Fin (min (Fintype.card m') (Fintype.card n')) =>
          k ≤ j.val)).image shift, g j := (Finset.sum_image h_inj).symm
    _ ≤ ∑ j, g j :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun j _ _ => sq_nonneg (SVD.Rectangular.singularValues (A - B) j))

section Frobenius

attribute [local instance] Matrix.frobeniusSeminormedAddCommGroup

/-- **Eckart–Young theorem (Frobenius norm, rectangular).** The truncated SVD is a best
    rank-k approximation in Frobenius norm: for any B with rank(B) ≤ k,
    ‖A - truncatedSVD_rect A k‖_F ≤ ‖A - B‖_F. -/
theorem eckart_young_frobenius_rect (A B : Matrix m' n' ℂ) (k : ℕ) (hB : B.rank ≤ k) :
    ‖A - truncatedSVD_rect A k‖ ≤ ‖A - B‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [frobenius_error_truncatedSVD_rect,
    SVD.Rectangular.frobeniusNorm_sq_eq_sum_singularValues_sq_rect (A - B)]
  exact sum_sq_tail_le_sum_sq_singularValues_sub A B k hB

end Frobenius

section Spectral

attribute [local instance] Matrix.instL2OpNormedAddCommGroup
attribute [local instance] Matrix.instL2OpNormedSpace
attribute [local instance] Matrix.instL2OpNormedRing
attribute [local instance] Matrix.instL2OpNormedAlgebra
attribute [local instance] Matrix.instL2OpMetricSpace
attribute [local instance] Matrix.instCStarRing

/-- **Eckart–Young theorem (spectral norm, rectangular).** The truncated SVD is a best
    rank-k approximation in spectral norm: for any B with rank(B) ≤ k,
    ‖A - truncatedSVD_rect A k‖₂ ≤ ‖A - B‖₂. -/
theorem eckart_young_spectral_rect (A B : Matrix m' n' ℂ) (k : ℕ) (hB : B.rank ≤ k) :
    ‖A - truncatedSVD_rect A k‖ ≤ ‖A - B‖ := by
  by_cases hk : k < min (Fintype.card m') (Fintype.card n')
  · -- The error is σₖ(A) ≤ σ₀(A - B) ≤ ‖A - B‖₂
    rw [spectral_error_truncatedSVD_rect A k hk]
    have h0 : 0 < min (Fintype.card m') (Fintype.card n') := by omega
    have h_norm : ‖A - B‖ = SVD.Rectangular.maxSingularValue h0 (A - B) :=
      SVD.Rectangular.spectral_norm_eq_max_singularValue_rect h0 (A - B)
    have h_top : ∀ j, SVD.Rectangular.singularValues (A - B) j ≤ ‖A - B‖ := by
      intro j
      rw [h_norm]
      exact Finset.le_sup' _ (Finset.mem_univ j)
    have h_interlace :=
      Matrix.WeylInequality.interlacing_low_rank_subtraction_rect A B k hB ⟨k, hk⟩ le_rfl
    exact le_trans h_interlace (h_top _)
  · -- k ≥ min #m' #n': the truncation is A itself
    rw [truncatedSVD_rect_full A k (not_lt.mp hk), sub_self, norm_zero]
    exact norm_nonneg _

end Spectral

end EckartYoungRect

/-! ## Part 4: Tight Bound for Kronecker Approximation

The main theorems for best rank-1 Kronecker approximation error bounds.

**Critical note on norms:**
- The rearrangement R is a Frobenius isometry: ‖R(M)‖_F = ‖M‖_F
- The rearrangement R does NOT preserve spectral norm: ‖R(M)‖₂ ≠ ‖M‖₂ in general
- Counterexample: Anti-diagonal permutation matrix has ‖M‖₂ = 1 but ‖R(M)‖₂ = 2

Therefore:
- Frobenius bounds are EXACT (equality)
- Spectral bounds are only UPPER bounds (inequality)
-/

section TightKroneckerBound

-- Enable Frobenius norm instance for this section
attribute [local instance] Matrix.frobeniusSeminormedAddCommGroup

/-- Cauchy-Schwarz for complex sums: |∑ⱼ aⱼ bⱼ| ≤ √(∑ⱼ |aⱼ|²) · √(∑ⱼ |bⱼ|²) -/
private lemma complex_sum_cauchy_schwarz_inline {ι : Type*} [Fintype ι] (a b : ι → ℂ) :
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
private lemma mulVec_eucl_norm_sq_le_inline {m' n' : Type*} [Fintype m'] [Fintype n']
    (A : Matrix m' n' ℂ) (x : EuclideanSpace ℂ n') :
    ‖(EuclideanSpace.equiv m' ℂ).symm (A *ᵥ x.ofLp)‖^2 ≤
      (∑ i, ∑ j, ‖A i j‖^2) * ‖x‖^2 := by
  rw [EuclideanSpace.norm_sq_eq]
  have cs := fun i => complex_sum_cauchy_schwarz_inline (A i) x.ofLp
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
private lemma mulVec_eucl_norm_le_inline {m' n' : Type*} [Fintype m'] [Fintype n']
    (A : Matrix m' n' ℂ) (x : EuclideanSpace ℂ n') :
    ‖(EuclideanSpace.equiv m' ℂ).symm (A *ᵥ x.ofLp)‖ ≤
      Real.sqrt (∑ i, ∑ j, ‖A i j‖^2) * ‖x‖ := by
  have h_sq := mulVec_eucl_norm_sq_le_inline A x
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
private lemma frobenius_norm_eq_sqrt_inline {m' n' : Type*} [Fintype m'] [Fintype n']
    (A : Matrix m' n' ℂ) :
    @Norm.norm _ Matrix.frobeniusSeminormedAddCommGroup.toNorm A =
      Real.sqrt (∑ i, ∑ j, ‖A i j‖ ^ 2) := by
  rw [Matrix.frobenius_norm_def, Real.sqrt_eq_rpow]
  norm_cast

/-- **L2 operator norm is bounded by Frobenius norm** (rectangular matrices).
    This is the fundamental inequality: ‖A‖₂ ≤ ‖A‖_F
    Proof: Using mulVec norm bound via Cauchy-Schwarz. -/
private theorem l2_opNorm_le_frobenius_inline {m' n' : Type*}
    [Fintype m'] [Fintype n'] [DecidableEq n']
    (A : Matrix m' n' ℂ) :
    @Norm.norm _ Matrix.instL2OpNormedAddCommGroup.toNorm A ≤
      @Norm.norm _ Matrix.frobeniusSeminormedAddCommGroup.toNorm A := by
  rw [Matrix.l2_opNorm_def, frobenius_norm_eq_sqrt_inline]
  apply ContinuousLinearMap.opNorm_le_bound
  · exact Real.sqrt_nonneg _
  · intro x
    exact mulVec_eucl_norm_le_inline A x

/-- **Frobenius error of Kronecker approximation via R isometry**

    For any matrix C, we can compute the Frobenius error of the best rank-1 Kronecker
    approximation by transferring to R-space where R is a Frobenius isometry.

    **Mathematical statement:**
    ‖C - R⁻¹(truncatedSVD(R(C), 1))‖_F = ‖R(C) - truncatedSVD(R(C), 1)‖_F

    This equals √(σ₂² + σ₃² + ... + σₙ²) where σᵢ are singular values of R(C).
    NOT σ₂ alone! (The spectral error equals σ₂, but Frobenius ≠ spectral.)
    Only the isometry identity above is proved. The √(σ₂² + ⋯) formula and the optimality
    of the truncated SVD are not formalized for rectangular matrices.

    **Key property:**
    - R is a Frobenius isometry: ‖R(M)‖_F = ‖M‖_F
    - R_inv is also a Frobenius isometry (since R∘R_inv = id)
    - Therefore ‖C - R⁻¹(X)‖_F = ‖R(C - R⁻¹(X))‖_F = ‖R(C) - X‖_F -/
theorem frobenius_error_via_R_isometry
    (C : Matrix (m × n) (p × q) ℂ) (X : Matrix (m × p) (n × q) ℂ) :
    ‖C - KroneckerRearrangement.R_inv X‖ =
    ‖KroneckerRearrangement.R C - X‖ := by
  -- Step 1: ‖C - R_inv(X)‖ = ‖R(C - R_inv(X))‖ by R isometry
  have h1 : ‖C - KroneckerRearrangement.R_inv X‖ =
            ‖KroneckerRearrangement.R (C - KroneckerRearrangement.R_inv X)‖ := by
    rw [KroneckerRearrangement.R_frobenius_norm_eq]
  -- Step 2: R(C - R_inv(X)) = R(C) - R(R_inv(X)) = R(C) - X
  have h2 : KroneckerRearrangement.R (C - KroneckerRearrangement.R_inv X) =
            KroneckerRearrangement.R C - X := by
    rw [Kronecker.SpectralGap.R_sub, KroneckerRearrangement.R_R_inv]
  rw [h1, h2]

-- Enable L2 operator norm instances for spectral norm theorems
attribute [local instance] Matrix.instL2OpNormedAddCommGroup
attribute [local instance] Matrix.instL2OpNormedSpace
attribute [local instance] Matrix.instL2OpNormedRing
attribute [local instance] Matrix.instL2OpNormedAlgebra
attribute [local instance] Matrix.instL2OpMetricSpace
attribute [local instance] Matrix.instCStarRing

/-- **Spectral error bounded by Frobenius error**

    The spectral error is bounded above by the Frobenius error.
    This bound is universal (‖·‖₂ ≤ ‖·‖_F for any matrix).

    **Mathematical statement:**
    ‖C - R⁻¹(truncatedSVD(R(C), 1))‖₂ ≤ ‖C - R⁻¹(truncatedSVD(R(C), 1))‖_F
                                        = ‖R(C) - truncatedSVD(R(C), 1)‖_F
                                        = √(σ₂² + σ₃² + ...)

    The theorem states only the first inequality. The first equality is
    `frobenius_error_via_R_isometry`; the last is not formalized. -/
theorem spectral_error_le_frobenius_error
    (C : Matrix (m × n) (p × q) ℂ) :
    @Norm.norm _ Matrix.instL2OpNormedAddCommGroup.toNorm
      (C - KroneckerRearrangement.R_inv (truncatedSVD_rect (KroneckerRearrangement.R C) 1)) ≤
    @Norm.norm _ Matrix.frobeniusSeminormedAddCommGroup.toNorm
      (C - KroneckerRearrangement.R_inv (truncatedSVD_rect (KroneckerRearrangement.R C) 1)) :=
  l2_opNorm_le_frobenius_inline _

end TightKroneckerBound

/-! ## Part 5: Coherence and Spectral-Frobenius Coincidence

A previous draft stated that high coherence of the rearranged error
`E' = R(C) - truncatedSVD_rect (R C) 1` (`μ(E') ≥ 0.9`) forces
`‖E‖₂ ≥ 0.9 · ‖E‖_F` for the original-space error `E = R⁻¹(E')`. That statement
is false and has been removed:

* High coherence bounds the spectral norm from *above* relative to Frobenius
  (`‖E'‖_F / ‖E'‖₂ = √rank · μ(E')`, see `frobenius_spectral_ratio_eq_sqrt_rank_mul_coherence_rect`).
* `R` preserves the Frobenius norm but not the spectral norm.

Counterexample with `m = n = p = q = Fin 2`: let `R(C) = vec(I₂) vec(I₂)ᵀ + 3 e e ᵀ`
with `e` the basis vector at index `(0, 1)`. The singular values are `3 > 2`, so the
rank-1 truncation is `3 e eᵀ` and `E' = vec(I₂) vec(I₂)ᵀ` has rank 1 and `μ(E') = 1`.
But `E = R⁻¹(E') = I₄`, with `‖E‖₂ = 1 < 0.9 · 2 = 0.9 · ‖E‖_F`.
-/

end Matrix.TightBounds
