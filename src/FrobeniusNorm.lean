/-
Copyright (c) 2025 FLYWHEEL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aleksandar Markovski
-/
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Complex.Order
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Norm
import SVD
import WeylInequality

/-!
# Frobenius Norm and Eckart-Young

‖A‖_F² = tr(Aᴴ A) = Σᵢ σᵢ². Unitary invariance from trace cyclicity.

## References

[1] Eckart, C. & Young, G. (1936). The approximation of one matrix by
    another of lower rank. Psychometrika 1(3), 211–218.
[2] Mirsky, L. (1960). Symmetric gauge functions and unitarily invariant norms.
    Quart. J. Math. 11, 50–59.
[3] Horn & Johnson (2012), §5.6 (Unitarily Invariant Norms).

Test matrix dims for validation: 3×75, 72×74, 111×81, 3×76, 121×54, 115×1.
Implementation via `Matrix.frobeniusSeminormedAddCommGroup` instance.

## Known Issues
- The Eckart-Young theorem is not fully implmented yet (see below)
- Some simp lemmas might be missing @[simp] tags

## Questions
- Should we use `NNReal` for the norm squared? Would simplify some proofs
- Is there a better way to handle the sqrt vs rpow (1/2) situation?
-/

open Matrix
open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder

namespace Matrix.FrobeniusNorm

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

attribute [local instance] Matrix.frobeniusSeminormedAddCommGroup

-- FIXME: this lemma probably already exists somewhere in Mathlib?
-- I looked but couldn't find it. If someone finds it, replace this.
lemma Complex.norm_sq_eq_star_mul_self (z : ℂ) : ‖z‖^2 = (star z * z).re := by
  have key : star z * z = z.normSq := by
    simp only [Complex.star_def]
    rw [Complex.normSq_eq_conj_mul_self]
  rw [key]
  simp only [Complex.ofReal_re]
  rw [sq, Complex.norm_mul_self_eq_normSq]
  -- #check Complex.sq_abs -- this exists but uses abs not norm, annoying

lemma Complex.norm_rpow_two_eq_star_mul_self (z : ℂ) : ‖z‖ ^ (2:ℝ) = (star z * z).re := by
  rw [Real.rpow_two]
  exact Complex.norm_sq_eq_star_mul_self z

omit [DecidableEq n] in
/-- ‖A‖_F² = Re tr(Aᴴ A). Standard identity. -/
theorem frobenius_norm_sq_eq_trace (A : Matrix n n ℂ) :
    ‖A‖^2 = (trace (Aᴴ * A)).re := by
  -- Show the sum part directly using ℝ powers
  have key : ∑ i : n, ∑ j : n, ‖A i j‖ ^ (2:ℝ) = (trace (Aᴴ * A)).re := by
    simp only [trace, diag_apply, mul_apply, conjTranspose_apply]
    rw [Finset.sum_comm]
    conv_rhs => rw [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro j _
    conv_rhs => rw [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact Complex.norm_rpow_two_eq_star_mul_self (A i j)
  -- Now the goal is to show ‖A‖^2 = ...
  rw [frobenius_norm_def]
  have h_nonneg : 0 ≤ ∑ i : n, ∑ j : n, ‖A i j‖ ^ (2:ℝ) :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => Real.rpow_nonneg (norm_nonneg _) _))
  rw [sq]
  -- x^(1/2) * x^(1/2) = x for x ≥ 0
  have rpow_half_mul_self : (∑ i : n, ∑ j : n, ‖A i j‖ ^ (2:ℝ)) ^ (1/2 : ℝ) *
                            (∑ i : n, ∑ j : n, ‖A i j‖ ^ (2:ℝ)) ^ (1/2 : ℝ) =
                            ∑ i : n, ∑ j : n, ‖A i j‖ ^ (2:ℝ) := by
    have h2ne : (2 : ℝ)⁻¹ + (2 : ℝ)⁻¹ ≠ 0 := by norm_num
    have half_eq : (1 : ℝ) / 2 = (2 : ℝ)⁻¹ := one_div 2
    rw [half_eq]
    rw [← Real.rpow_add' h_nonneg h2ne]
    norm_num
  exact rpow_half_mul_self.trans key

/-! ### Unitary Invariance of Trace -/

/-- Left multiplication by a unitary matrix preserves trace(Aᴴ * A).
Uses: (U*A)ᴴ*(U*A) = Aᴴ*Uᴴ*U*A = Aᴴ*A since Uᴴ*U = 1. -/
lemma trace_conjTranspose_unitary_mul (U : unitaryGroup n ℂ) (A : Matrix n n ℂ) :
    trace (((U : Matrix n n ℂ) * A)ᴴ * ((U : Matrix n n ℂ) * A)) = trace (Aᴴ * A) := by
  have h_unitary : (U : Matrix n n ℂ)ᴴ * (U : Matrix n n ℂ) = 1 := by
    have h := mem_unitaryGroup_iff'.mp U.2
    simp only [star_eq_conjTranspose] at h
    exact h
  simp only [conjTranspose_mul]
  -- Goal: (Aᴴ * Uᴴ * (U * A)).trace = (Aᴴ * A).trace
  have h1 : Aᴴ * (U : Matrix n n ℂ)ᴴ * ((U : Matrix n n ℂ) * A) =
            Aᴴ * ((U : Matrix n n ℂ)ᴴ * (U : Matrix n n ℂ)) * A := by
    rw [mul_assoc, mul_assoc, mul_assoc]
  rw [h1, h_unitary, mul_one]

/-- Right multiplication by a unitary matrix preserves trace(Aᴴ * A).
Uses trace cyclicity: trace(VᴴAᴴAV) = trace(VVᴴAᴴA) = trace(AᴴA) since VVᴴ = 1. -/
lemma trace_conjTranspose_mul_unitary (A : Matrix n n ℂ) (V : unitaryGroup n ℂ) :
    trace ((A * (V : Matrix n n ℂ))ᴴ * (A * (V : Matrix n n ℂ))) = trace (Aᴴ * A) := by
  have h_unitary : (V : Matrix n n ℂ) * (V : Matrix n n ℂ)ᴴ = 1 := by
    have h := mem_unitaryGroup_iff.mp V.2
    simp only [star_eq_conjTranspose] at h
    exact h
  simp only [conjTranspose_mul]
  -- Goal: ((↑V)ᴴ * Aᴴ * (A * ↑V)).trace = (Aᴴ * A).trace
  have step1 : (V : Matrix n n ℂ)ᴴ * Aᴴ * (A * (V : Matrix n n ℂ)) =
               (V : Matrix n n ℂ)ᴴ * (Aᴴ * A) * (V : Matrix n n ℂ) := by
    rw [mul_assoc, mul_assoc, mul_assoc]
  rw [step1]
  rw [trace_mul_cycle ((V : Matrix n n ℂ)ᴴ) (Aᴴ * A) ((V : Matrix n n ℂ))]
  -- (↑V * (↑V)ᴴ * (Aᴴ * A)).trace = (Aᴴ * A).trace
  rw [← mul_assoc, h_unitary, one_mul]

/-! ### Unitary Invariance of Frobenius Norm -/

/-- Left multiplication by unitary preserves Frobenius norm. -/
theorem frobenius_norm_unitary_mul (U : unitaryGroup n ℂ) (A : Matrix n n ℂ) :
    ‖(U : Matrix n n ℂ) * A‖ = ‖A‖ := by
  have h_sq : ‖(U : Matrix n n ℂ) * A‖^2 = ‖A‖^2 := by
    rw [frobenius_norm_sq_eq_trace, frobenius_norm_sq_eq_trace]
    rw [trace_conjTranspose_unitary_mul]
  have h1 : 0 ≤ ‖(U : Matrix n n ℂ) * A‖ := norm_nonneg _
  have h2 : 0 ≤ ‖A‖ := norm_nonneg _
  rw [← Real.sqrt_sq h1, ← Real.sqrt_sq h2, h_sq]

/-- Right multiplication by unitary preserves Frobenius norm. -/
theorem frobenius_norm_mul_unitary (A : Matrix n n ℂ) (V : unitaryGroup n ℂ) :
    ‖A * (V : Matrix n n ℂ)‖ = ‖A‖ := by
  have h_sq : ‖A * (V : Matrix n n ℂ)‖^2 = ‖A‖^2 := by
    rw [frobenius_norm_sq_eq_trace, frobenius_norm_sq_eq_trace]
    rw [trace_conjTranspose_mul_unitary]
  have h1 : 0 ≤ ‖A * (V : Matrix n n ℂ)‖ := norm_nonneg _
  have h2 : 0 ≤ ‖A‖ := norm_nonneg _
  rw [← Real.sqrt_sq h1, ← Real.sqrt_sq h2, h_sq]

/-! ### Diagonal Matrix Norm -/

/-- The Frobenius norm squared of a diagonal matrix equals the sum of squared entries. -/
theorem frobenius_norm_sq_diagonal (d : n → ℂ) :
    ‖diagonal d‖^2 = ∑ i : n, ‖d i‖^2 := by
  rw [frobenius_norm_sq_eq_trace]
  simp only [trace, diag_apply, mul_apply, conjTranspose_apply, diagonal_apply]
  -- Simplify inner sums: only j = i contributes
  have inner_sum_eq : ∀ i : n, ∑ j : n, star (if j = i then d j else 0) * (if j = i then d j else 0) =
                                star (d i) * d i := by
    intro i
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [hji]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  -- Apply to convert double sum to single sum
  have sum_eq : ∑ i : n, ∑ j : n, star (if j = i then d j else 0) * (if j = i then d j else 0) =
                ∑ i : n, star (d i) * d i := by
    apply Finset.sum_congr rfl
    intro i _
    exact inner_sum_eq i
  rw [sum_eq]
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  -- (star (d i) * d i).re = ‖d i‖^2
  have h1 : star (d i) * d i = (d i).normSq := by
    simp only [Complex.star_def, Complex.normSq_eq_conj_mul_self]
  rw [h1]
  simp only [Complex.ofReal_re]
  rw [Complex.normSq_eq_norm_sq]

/-! ### Main Theorem: Frobenius Error Formula -/

/-- Tail singular values are non-negative. -/
theorem truncatedSingularValues_tail_nonneg (A : Matrix n n ℂ) (k : ℕ) (i : n) :
    0 ≤ Matrix.SVD.truncatedSingularValues_tail A k i := by
  unfold Matrix.SVD.truncatedSingularValues_tail
  simp only
  split_ifs with h
  · exact Matrix.SVD.singularValues₀_nonneg A _
  · rfl

/-- Helper: star of a unitary matrix is also unitary. -/
private lemma star_unitary_mem (V : unitaryGroup n ℂ) :
    (star (V : Matrix n n ℂ)) ∈ unitaryGroup n ℂ := by
  rw [mem_unitaryGroup_iff']
  simp only [star_star]
  exact mem_unitaryGroup_iff.mp V.2

/-- Helper for converting |r|² to r² when r ≥ 0. -/
private lemma sq_abs_eq_sq_of_nonneg {r : ℝ} (h : 0 ≤ r) : |r|^2 = r^2 := by
  rw [abs_of_nonneg h]

set_option maxHeartbeats 800000 in
/-- The Frobenius norm squared of A - Aₖ equals the sum of squared tail singular values.
    This is the key formula for the Eckart-Young theorem.

    Proof strategy:
    1. Use `truncatedSVD_add_tail`: A - Aₖ = truncatedSVD_tail A k = U * Σ_tail * Vᴴ
    2. Apply unitary invariance: ‖U * Σ_tail * Vᴴ‖_F = ‖Σ_tail‖_F
    3. Apply diagonal norm formula: ‖Σ_tail‖_F² = Σᵢ |σ_tail(i)|² -/
theorem frobenius_error_truncatedSVD (A : Matrix n n ℂ) (k : ℕ) :
    ‖A - Matrix.SVD.truncatedSVD A k‖^2 =
      ∑ i : n, (Matrix.SVD.truncatedSingularValues_tail A k i)^2 := by
  -- Abbreviations for readability
  set U := Matrix.SVD.constructedU A with hU_def
  set V := Matrix.SVD.rightUnitary A with hV_def
  set d := Matrix.SVD.truncatedSingularValues_tail A k with hd_def
  set D := diagonal (Complex.ofReal ∘ d) with hD_def
  set Vstar : unitaryGroup n ℂ := ⟨star (V : Matrix n n ℂ), star_unitary_mem V⟩ with hVstar_def

  -- Step 1: A - Aₖ = truncatedSVD_tail by truncatedSVD_add_tail
  have h_sub : A - Matrix.SVD.truncatedSVD A k = Matrix.SVD.truncatedSVD_tail A k :=
    sub_eq_of_eq_add' (Matrix.SVD.truncatedSVD_add_tail A k)

  -- Step 2: truncatedSVD_tail = U * D * Vᴴ
  have h_tail_eq : Matrix.SVD.truncatedSVD_tail A k = (U : Matrix n n ℂ) * D * star (V : Matrix n n ℂ) := by
    simp only [hU_def, hV_def, hD_def, hd_def]
    rfl

  -- Step 3: Compute the norm via unitary invariance
  have h_norm_tail : ‖Matrix.SVD.truncatedSVD_tail A k‖ = ‖D‖ := by
    rw [h_tail_eq]
    -- ‖U * D * Vᴴ‖ = ‖U * D‖ (right unitary)
    have h1 : ‖(U : Matrix n n ℂ) * D * star (V : Matrix n n ℂ)‖ = ‖(U : Matrix n n ℂ) * D‖ := by
      have assoc_eq : (U : Matrix n n ℂ) * D * star (V : Matrix n n ℂ) = (U : Matrix n n ℂ) * (D * (Vstar : Matrix n n ℂ)) := by
        rw [mul_assoc]
      rw [assoc_eq]
      have h := frobenius_norm_mul_unitary ((U : Matrix n n ℂ) * D) Vstar
      rw [mul_assoc] at h
      exact h
    -- ‖U * D‖ = ‖D‖ (left unitary)
    have h2 : ‖(U : Matrix n n ℂ) * D‖ = ‖D‖ := frobenius_norm_unitary_mul U D
    rw [h1, h2]

  -- Step 4: Compute ‖D‖² using diagonal formula
  have h_D_sq : ‖D‖^2 = ∑ i : n, ‖(Complex.ofReal ∘ d) i‖^2 := frobenius_norm_sq_diagonal (Complex.ofReal ∘ d)

  -- Step 5: Simplify ‖Complex.ofReal r‖^2 = r^2 for r ≥ 0
  have h_sum_eq : ∑ i : n, ‖(Complex.ofReal ∘ d) i‖^2 = ∑ i : n, d i ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [Function.comp_apply, Complex.norm_real, Real.norm_eq_abs]
    exact sq_abs_eq_sq_of_nonneg (by simp only [hd_def]; exact truncatedSingularValues_tail_nonneg A k i)

  -- Combine all steps
  calc ‖A - Matrix.SVD.truncatedSVD A k‖^2
      = ‖Matrix.SVD.truncatedSVD_tail A k‖^2 := by rw [h_sub]
    _ = ‖D‖^2 := by rw [h_norm_tail]
    _ = ∑ i : n, ‖(Complex.ofReal ∘ d) i‖^2 := h_D_sq
    _ = ∑ i : n, d i ^ 2 := h_sum_eq

/-! ### Eckart-Young Theorem (Frobenius Norm) -/

section EckartYoung

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Unitary transformation from the left preserves matrix rank. -/
lemma rank_unitary_mul (U : unitaryGroup n ℂ) (A : Matrix n n ℂ) :
    ((U : Matrix n n ℂ) * A).rank = A.rank := by
  have hU : IsUnit (U : Matrix n n ℂ).det := Matrix.UnitaryGroup.det_isUnit U
  exact Matrix.rank_mul_eq_right_of_isUnit_det (U : Matrix n n ℂ) A hU

/-- Unitary transformation from the right preserves matrix rank. -/
lemma rank_mul_unitary (A : Matrix n n ℂ) (V : unitaryGroup n ℂ) :
    (A * (V : Matrix n n ℂ)).rank = A.rank := by
  have hV : IsUnit (V : Matrix n n ℂ).det := Matrix.UnitaryGroup.det_isUnit V
  exact Matrix.rank_mul_eq_left_of_isUnit_det (V : Matrix n n ℂ) A hV

/-- Star of unitary matrix preserves matrix rank under left multiplication. -/
lemma rank_star_unitary_mul (U : unitaryGroup n ℂ) (A : Matrix n n ℂ) :
    (star (U : Matrix n n ℂ) * A).rank = A.rank := by
  have h_mem : star (U : Matrix n n ℂ) ∈ unitaryGroup n ℂ := by
    rw [mem_unitaryGroup_iff']
    simp only [star_star]
    exact mem_unitaryGroup_iff.mp U.2
  let Ustar : unitaryGroup n ℂ := ⟨star (U : Matrix n n ℂ), h_mem⟩
  exact rank_unitary_mul Ustar A

/-- Star of unitary matrix preserves matrix rank under right multiplication. -/
lemma rank_mul_star_unitary (A : Matrix n n ℂ) (V : unitaryGroup n ℂ) :
    (A * star (V : Matrix n n ℂ)).rank = A.rank := by
  have h_mem : star (V : Matrix n n ℂ) ∈ unitaryGroup n ℂ := by
    rw [mem_unitaryGroup_iff']
    simp only [star_star]
    exact mem_unitaryGroup_iff.mp V.2
  let Vstar : unitaryGroup n ℂ := ⟨star (V : Matrix n n ℂ), h_mem⟩
  exact rank_mul_unitary A Vstar

/-- Sandwich between unitary matrices preserves rank: rank(U* * A * V) = rank(A). -/
lemma rank_star_unitary_mul_unitary (U : unitaryGroup n ℂ) (A : Matrix n n ℂ) (V : unitaryGroup n ℂ) :
    (star (U : Matrix n n ℂ) * A * (V : Matrix n n ℂ)).rank = A.rank := by
  calc (star (U : Matrix n n ℂ) * A * (V : Matrix n n ℂ)).rank
      = (star (U : Matrix n n ℂ) * (A * (V : Matrix n n ℂ))).rank := by rw [mul_assoc]
    _ = (A * (V : Matrix n n ℂ)).rank := rank_star_unitary_mul U (A * (V : Matrix n n ℂ))
    _ = A.rank := rank_mul_unitary A V

/-- The error ‖A - B‖_F equals ‖Sig - U* B V‖_F in the SVD basis.
    This transforms the optimization problem to diagonal form. -/
lemma frobenius_error_in_svd_basis (A B : Matrix n n ℂ) :
    ‖A - B‖ = ‖diagonal (Complex.ofReal ∘ Matrix.SVD.singularValues A) -
               star (Matrix.SVD.constructedU A : Matrix n n ℂ) * B * (Matrix.SVD.rightUnitary A : Matrix n n ℂ)‖ := by
  let U := Matrix.SVD.constructedU A
  let V := Matrix.SVD.rightUnitary A
  let Sig := diagonal (Complex.ofReal ∘ Matrix.SVD.singularValues A)

  -- The SVD: A = U * Sig * V*
  have h_svd : A = (U : Matrix n n ℂ) * Sig * star (V : Matrix n n ℂ) := by
    have h_AV := Matrix.SVD.AV_eq_constructedU_mul_sigma A
    have h_V_unitary : (V : Matrix n n ℂ) * star (V : Matrix n n ℂ) = 1 :=
      mem_unitaryGroup_iff.mp V.2
    calc A = A * ((V : Matrix n n ℂ) * star (V : Matrix n n ℂ)) := by rw [h_V_unitary, mul_one]
      _ = (A * (V : Matrix n n ℂ)) * star (V : Matrix n n ℂ) := by rw [mul_assoc]
      _ = ((U : Matrix n n ℂ) * Sig) * star (V : Matrix n n ℂ) := by rw [h_AV]
      _ = (U : Matrix n n ℂ) * Sig * star (V : Matrix n n ℂ) := by rw [mul_assoc]

  -- U* * (A - B) * V = U* * U * Sig * V* * V - U* * B * V = Sig - U* * B * V
  have h_transform : star (U : Matrix n n ℂ) * (A - B) * (V : Matrix n n ℂ) =
                     Sig - star (U : Matrix n n ℂ) * B * (V : Matrix n n ℂ) := by
    have h_U_unitary : star (U : Matrix n n ℂ) * (U : Matrix n n ℂ) = 1 :=
      mem_unitaryGroup_iff'.mp U.2
    have h_V_unitary : star (V : Matrix n n ℂ) * (V : Matrix n n ℂ) = 1 :=
      mem_unitaryGroup_iff'.mp V.2
    -- Direct calculation
    have step1 : star (U : Matrix n n ℂ) * (A - B) * (V : Matrix n n ℂ) =
                 star (U : Matrix n n ℂ) * A * (V : Matrix n n ℂ) -
                 star (U : Matrix n n ℂ) * B * (V : Matrix n n ℂ) := by
      simp only [sub_mul, mul_sub]
    have step2 : star (U : Matrix n n ℂ) * A * (V : Matrix n n ℂ) = Sig := by
      rw [h_svd]
      -- star U * (U * Sig * star V) * V = (star U * U) * Sig * (star V * V) = 1 * Sig * 1 = Sig
      calc star (U : Matrix n n ℂ) * ((U : Matrix n n ℂ) * Sig * star (V : Matrix n n ℂ)) * (V : Matrix n n ℂ)
          = star (U : Matrix n n ℂ) * (U : Matrix n n ℂ) * Sig * star (V : Matrix n n ℂ) * (V : Matrix n n ℂ) := by
            simp only [mul_assoc]
        _ = 1 * Sig * star (V : Matrix n n ℂ) * (V : Matrix n n ℂ) := by rw [h_U_unitary]
        _ = Sig * star (V : Matrix n n ℂ) * (V : Matrix n n ℂ) := by rw [one_mul]
        _ = Sig * (star (V : Matrix n n ℂ) * (V : Matrix n n ℂ)) := by rw [mul_assoc]
        _ = Sig * 1 := by rw [h_V_unitary]
        _ = Sig := by rw [mul_one]
    rw [step1, step2]

  -- Use unitary invariance of Frobenius norm
  have h_mem_U : star (U : Matrix n n ℂ) ∈ unitaryGroup n ℂ := by
    rw [mem_unitaryGroup_iff']
    simp only [star_star]
    exact mem_unitaryGroup_iff.mp U.2
  let Ustar : unitaryGroup n ℂ := ⟨star (U : Matrix n n ℂ), h_mem_U⟩

  calc ‖A - B‖
      = ‖(Ustar : Matrix n n ℂ) * (A - B)‖ := (frobenius_norm_unitary_mul Ustar (A - B)).symm
    _ = ‖(Ustar : Matrix n n ℂ) * (A - B) * (V : Matrix n n ℂ)‖ := (frobenius_norm_mul_unitary _ V).symm
    _ = ‖star (U : Matrix n n ℂ) * (A - B) * (V : Matrix n n ℂ)‖ := rfl
    _ = ‖Sig - star (U : Matrix n n ℂ) * B * (V : Matrix n n ℂ)‖ := by rw [h_transform]

/-- The Frobenius norm squared of the difference between a diagonal and an arbitrary matrix
    can be decomposed into diagonal and off-diagonal contributions. -/
lemma frobenius_sq_diagonal_minus_matrix (d : n → ℂ) (C : Matrix n n ℂ) :
    ‖diagonal d - C‖^2 = ∑ i, ‖d i - C i i‖^2 + ∑ i, ∑ j, (if i ≠ j then ‖C i j‖^2 else 0) := by
  rw [frobenius_norm_sq_eq_trace]
  -- Expand trace(Aᴴ * A) = Σᵢⱼ |Aᵢⱼ|²
  -- trace((Aᴴ * A)) = Σᵢ (Aᴴ * A)ᵢᵢ = Σᵢ Σⱼ (Aᴴ)ᵢⱼ * Aⱼᵢ = Σᵢ Σⱼ |Aⱼᵢ|²
  -- By commutativity of sum = Σⱼ Σᵢ |Aⱼᵢ|² = Σᵢ Σⱼ |Aᵢⱼ|² (relabeling)
  have h_expand : (trace ((diagonal d - C)ᴴ * (diagonal d - C))).re =
                  ∑ i, ∑ j, ‖(diagonal d - C) i j‖^2 := by
    simp only [trace, diag_apply, mul_apply, conjTranspose_apply]
    rw [Complex.re_sum]
    -- Swap the sum order: Σᵢ Σⱼ |Mⱼᵢ|² = Σⱼ Σᵢ |Mⱼᵢ|² = Σᵢ Σⱼ |Mᵢⱼ|²
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [Complex.norm_sq_eq_star_mul_self]
  rw [h_expand]
  -- Split each inner sum into the diagonal term and off-diagonal terms
  have h_rewrite : ∀ i : n, ∑ j, ‖(diagonal d - C) i j‖^2 =
      ‖d i - C i i‖^2 + ∑ j, (if i ≠ j then ‖C i j‖^2 else 0) := by
    intro i
    -- Σⱼ ‖(diagonal d - C)ᵢⱼ‖² = ‖dᵢ - Cᵢᵢ‖² + Σⱼ≠ᵢ ‖-Cᵢⱼ‖²
    --                          = ‖dᵢ - Cᵢᵢ‖² + Σⱼ≠ᵢ ‖Cᵢⱼ‖²
    calc ∑ j, ‖(diagonal d - C) i j‖^2
        = ‖(diagonal d - C) i i‖^2 + ∑ j ∈ Finset.univ.filter (· ≠ i), ‖(diagonal d - C) i j‖^2 := by
          rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· = i)]
          simp only [Finset.filter_eq', Finset.mem_univ, ↓reduceIte, Finset.sum_singleton]
      _ = ‖d i - C i i‖^2 + ∑ j ∈ Finset.univ.filter (· ≠ i), ‖(diagonal d - C) i j‖^2 := by
          congr 1
          simp only [sub_apply, diagonal_apply_eq]
      _ = ‖d i - C i i‖^2 + ∑ j ∈ Finset.univ.filter (· ≠ i), ‖C i j‖^2 := by
          congr 1
          apply Finset.sum_congr rfl
          intro j hj
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, ne_eq] at hj
          -- hj : ¬j = i, we need to show (if i = j then d i else 0) = 0
          have hij : ¬i = j := fun h => hj h.symm
          simp only [sub_apply, diagonal_apply, if_neg hij, zero_sub, norm_neg]
      _ = ‖d i - C i i‖^2 + ∑ j, (if i ≠ j then ‖C i j‖^2 else 0) := by
          congr 1
          -- Need to show Σ_{j ≠ i} ‖C i j‖² = Σⱼ (if i ≠ j then ‖C i j‖² else 0)
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro j _
          -- When j ≠ i, need i ≠ j; when ¬(j ≠ i), both sides are 0
          by_cases h : j = i
          · simp only [h, ne_eq, not_true_eq_false, ↓reduceIte]
          · have h' : i ≠ j := fun h' => h h'.symm
            simp only [ne_eq, h, not_false_eq_true, h', ↓reduceIte]
  simp_rw [h_rewrite]
  rw [Finset.sum_add_distrib]

/-- Key insight: For the truncated singular value diagonal matrix,
    the Frobenius squared error is the sum of squared tail singular values. -/
lemma frobenius_sq_truncated_diagonal (A : Matrix n n ℂ) (k : ℕ) :
    ‖diagonal (Complex.ofReal ∘ Matrix.SVD.singularValues A) -
     diagonal (Complex.ofReal ∘ Matrix.SVD.truncatedSingularValues A k)‖^2 =
    ∑ i : n, (Matrix.SVD.truncatedSingularValues_tail A k i)^2 := by
  -- The difference of diagonals is diagonal(singularValues - truncated) = diagonal(tail)
  have h_diff : diagonal (Complex.ofReal ∘ Matrix.SVD.singularValues A) -
                diagonal (Complex.ofReal ∘ Matrix.SVD.truncatedSingularValues A k) =
                diagonal (Complex.ofReal ∘ Matrix.SVD.truncatedSingularValues_tail A k) := by
    ext i j
    simp only [sub_apply, diagonal_apply, Function.comp_apply]
    split_ifs with h
    · subst h
      rw [← Complex.ofReal_sub]
      congr 1
      have := Matrix.SVD.truncatedSingularValues_add_tail A k i
      linarith
    · ring
  rw [h_diff, frobenius_norm_sq_diagonal]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Function.comp_apply, Complex.norm_real, Real.norm_eq_abs]
  rw [sq_abs_eq_sq_of_nonneg (truncatedSingularValues_tail_nonneg A k i)]

/-! ### Eckart-Young Core Lemma

The following lemma is the essential mathematical content of the Eckart-Young theorem.
It states that for sorted singular values σ₁ ≥ σ₂ ≥ ... ≥ σₙ ≥ 0 and any matrix C
with rank(C) ≤ k, the tail sum of squared singular values is bounded:

  σₖ₊₁² + σₖ₊₂² + ... + σₙ² ≤ Σᵢ |σᵢ - Cᵢᵢ|²

**Proof Strategy:**

The Eckart-Young theorem states that the truncated SVD minimizes the Frobenius norm
error among all rank-k approximations. The proof works in the SVD basis where:
- A becomes the diagonal matrix Σ = diag(σ₁, ..., σₙ)
- The truncated SVD becomes Σₖ = diag(σ₁, ..., σₖ, 0, ..., 0)
- Any rank-k approximation B becomes C = U*BV with rank(C) ≤ k

The full Frobenius error decomposes as:
  ‖Σ - C‖² = Σᵢ |σᵢ - Cᵢᵢ|² + Σᵢ≠ⱼ |Cᵢⱼ|²

The key insight is that:
1. Off-diagonal terms are always ≥ 0
2. For the truncated diagonal Σₖ, off-diagonal terms are 0
3. The diagonal terms of Σₖ give error Σᵢ≥ₖ σᵢ²

**NOTE:** The previously stated "diagonal-only" lemma (eckartYoungCoreLemma) was FALSE.
A rank-k matrix can have ALL diagonal entries matching σᵢ perfectly (unlike diagonal
rank-k matrices which can have at most k nonzero entries).

Counterexample: n=2, k=1, σ=(2,1), C=[[2,1],[2,1]] has rank 1 but diag(C)=(2,1)=σ.

The correct proof uses the FULL Frobenius norm. We prove optimality via an alternative
approach that doesn't require the false diagonal bound.

See: Horn & Johnson, "Matrix Analysis" (2012), Theorem 7.4.9 (Eckart-Young-Mirsky).
-/

/-! ### Eckart-Young Theorem -/

/-- The Eckart-Young theorem (Frobenius norm): The truncated SVD is the
    optimal rank-k approximation in Frobenius norm.

    For any matrix B with rank(B) ≤ k:
    ‖A - truncatedSVD A k‖_F ≤ ‖A - B‖_F

    Proof strategy (Horn & Johnson):
    1. Transform to SVD basis using unitary invariance
    2. In SVD basis, A becomes diagonal Σ
    3. Any rank-k approximation C = U* B V also has rank ≤ k
    4. The truncated diagonal achieves minimum error among all matrices

**IMPORTANT NOTE ON PROOF CORRECTNESS:**

The previously used `eckartYoungCoreLemma` claimed that diagonal deviations alone
bound the tail singular values. This is FALSE - see EckartYoung-BugReport.md.

Counterexample: For A = diag(2,1), the rank-1 matrix C = [[2,1],[2,1]] has
diagonal entries (2,1) = σ, giving RHS = 0, but LHS = 1.

The correct proof uses the FULL Frobenius norm. The key insight is that while
diagonal deviations alone may be insufficient, the off-diagonal terms of any
non-diagonal rank-k approximation add enough error to compensate.

For a rigorous proof, we use an alternative approach via projection optimality. -/
theorem eckart_young_frobenius (A : Matrix n n ℂ) (k : ℕ)
    (B : Matrix n n ℂ) (hB : B.rank ≤ k) :
    ‖A - Matrix.SVD.truncatedSVD A k‖ ≤ ‖A - B‖ := by
  -- Abbreviations for SVD components
  let U := Matrix.SVD.constructedU A
  let V := Matrix.SVD.rightUnitary A
  let Sig := diagonal (Complex.ofReal ∘ Matrix.SVD.singularValues A)
  let Sigk := diagonal (Complex.ofReal ∘ Matrix.SVD.truncatedSingularValues A k)
  let C := star (U : Matrix n n ℂ) * B * (V : Matrix n n ℂ)

  -- Step 1: rank(C) = rank(B) ≤ k
  have _hC : C.rank ≤ k := by
    calc C.rank = B.rank := rank_star_unitary_mul_unitary U B V
      _ ≤ k := hB

  -- Step 2: Transform both errors to SVD basis using unitary invariance
  have h_error_svd_basis : ‖A - B‖ = ‖Sig - C‖ := frobenius_error_in_svd_basis A B

  -- Step 3: The truncated SVD error in SVD basis equals diagonal truncation error
  have h_truncated_in_basis : ‖A - Matrix.SVD.truncatedSVD A k‖ = ‖Sig - Sigk‖ := by
    have h1 := frobenius_error_truncatedSVD A k
    have h2 := frobenius_sq_truncated_diagonal A k
    have h_sq_eq : ‖A - Matrix.SVD.truncatedSVD A k‖^2 = ‖Sig - Sigk‖^2 := by rw [h1, h2]
    have h_nonneg1 : 0 ≤ ‖A - Matrix.SVD.truncatedSVD A k‖ := norm_nonneg _
    have h_nonneg2 : 0 ≤ ‖Sig - Sigk‖ := norm_nonneg _
    exact (sq_eq_sq₀ h_nonneg1 h_nonneg2).mp h_sq_eq

  -- Step 4: Main inequality ‖Sig - Sigk‖ ≤ ‖Sig - C‖
  -- We prove ‖Sig - Sigk‖² ≤ ‖Sig - C‖² for any rank-k matrix C.

  suffices h_key : ‖Sig - Sigk‖^2 ≤ ‖Sig - C‖^2 by
    rw [h_truncated_in_basis, h_error_svd_basis]
    have h_nonneg1 : 0 ≤ ‖Sig - Sigk‖ := norm_nonneg _
    have h_nonneg2 : 0 ≤ ‖Sig - C‖ := norm_nonneg _
    have h_le := Real.sqrt_le_sqrt h_key
    rw [Real.sqrt_sq h_nonneg1, Real.sqrt_sq h_nonneg2] at h_le
    exact h_le

  -- Use the Frobenius decomposition: ‖Σ - C‖² = diagonal part + off-diagonal part
  -- The off-diagonal part is ≥ 0, so it suffices to show:
  -- ‖Σ - Σₖ‖² ≤ ∑ᵢ |σᵢ - Cᵢᵢ|² + (off-diagonal ≥ 0)

  let σ := Matrix.SVD.singularValues A
  let σₖ := Matrix.SVD.truncatedSingularValues A k

  -- LHS: ‖Σ - Σₖ‖² = ∑ᵢ (tail σᵢ)²
  have h_lhs : ‖Sig - Sigk‖^2 = ∑ i : n, (Matrix.SVD.truncatedSingularValues_tail A k i)^2 :=
    frobenius_sq_truncated_diagonal A k

  -- RHS decomposition using frobenius_sq_diagonal_minus_matrix
  have h_rhs : ‖Sig - C‖^2 = ∑ i, ‖(Complex.ofReal ∘ σ) i - C i i‖^2 +
      ∑ i, ∑ j, (if i ≠ j then ‖C i j‖^2 else 0) :=
    frobenius_sq_diagonal_minus_matrix (Complex.ofReal ∘ σ) C

  -- The off-diagonal sum is nonnegative
  have h_offdiag_nonneg : 0 ≤ ∑ i, ∑ j, (if i ≠ j then ‖C i j‖^2 else 0) := by
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    split_ifs <;> positivity

  rw [h_lhs, h_rhs]

  -- It suffices to show: ∑ᵢ (tail σᵢ)² ≤ ∑ᵢ |σᵢ - Cᵢᵢ|² + off-diagonal
  -- This is NOT true for diagonal terms alone (the bug we found).
  -- However, the full inequality including off-diagonal terms IS true.

  -- MATHEMATICAL PROOF OUTLINE (Eckart-Young-Mirsky via singular value interlacing):
  --
  -- Let s₁ ≥ s₂ ≥ ... ≥ sₙ be the singular values of (Σ - C).
  -- Then: ‖Σ - C‖² = ∑ⱼ sⱼ² (Frobenius norm = sum of squared singular values)
  --
  -- Key fact (Weyl's inequality): For any matrices A, B:
  --   σⱼ(A + B) ≤ σ₁(A) + σⱼ(B) for all j
  --   σⱼ(A) ≤ σⱼ₊ₖ(A + B) + σₖ₊₁(B) for appropriate indices
  --
  -- Applied to A = Σ - C and B = C (so A + B = Σ):
  -- Since rank(C) ≤ k, C has at most k nonzero singular values.
  -- Therefore σⱼ(C) = 0 for j > k.
  --
  -- By Weyl: σⱼ(Σ) ≤ σⱼ(Σ - C) + σ₁(C) for all j
  --          σⱼ(Σ - C) ≥ σⱼ(Σ) - σ₁(C)
  --
  -- For j > k: σⱼ(Σ) ≤ σⱼ(Σ - C) + σⱼ(C) = σⱼ(Σ - C) + 0 = σⱼ(Σ - C)
  --            (using the interlacing variant)
  --
  -- Therefore: ∑_{j>k} σⱼ(Σ)² ≤ ∑_{j>k} σⱼ(Σ - C)² ≤ ∑ⱼ σⱼ(Σ - C)² = ‖Σ - C‖²
  --
  -- The statement is mathematically correct per Horn & Johnson Theorem 7.4.9.
  -- Now proved using Thompson interlacing from WeylInequality.lean

  -- Handle the empty case first
  by_cases hn : Nonempty n
  case neg =>
    -- If n is empty, all sums are trivially 0
    have h_empty : IsEmpty n := not_nonempty_iff.mp hn
    simp only [@Finset.univ_eq_empty n _ h_empty, Finset.sum_empty, le_refl, add_zero]

  case pos =>
    -- Main proof using Thompson interlacing
    -- Key insight: For j ≥ k, singularValues₀ Sig j ≤ singularValues₀ (Sig - C) (j-k)
    -- Since Sig = diagonal(singularValues A), we have singularValues₀ Sig = singularValues₀ A
    -- (diagonal matrix with non-negative entries has those entries as singular values)

    -- The RHS = ‖Sig - C‖² = ∑ (singularValues (Sig - C))² by Frobenius norm identity
    have h_frob_sv : ‖Sig - C‖^2 = ∑ i, (Matrix.SVD.singularValues (Sig - C) i)^2 := by
      rw [frobenius_norm_sq_eq_trace]
      exact (Matrix.SVD.sum_sq_singularValues_eq_trace (Sig - C)).symm

    -- Use h_rhs to get the RHS = ‖Sig - C‖²
    have h_rhs' : ∑ i, ‖(Complex.ofReal ∘ σ) i - C i i‖^2 +
        ∑ i, ∑ j, (if i ≠ j then ‖C i j‖^2 else 0) = ‖Sig - C‖^2 := h_rhs.symm

    -- Convert singularValues to singularValues₀ on RHS using reindexing
    have h_sv_sum : ∑ i : n, (Matrix.SVD.singularValues (Sig - C) i)^2 =
        ∑ j : Fin (Fintype.card n), (Matrix.SVD.singularValues₀ (Sig - C) j)^2 := by
      -- singularValues_eq_singularValues₀: sv i = sv₀ (equivOfCardEq.symm i)
      -- So we need to sum using equivOfCardEq: Fin (card n) ≃ n
      have h : ∀ i : n, (Matrix.SVD.singularValues (Sig - C) i)^2 =
          (Matrix.SVD.singularValues₀ (Sig - C)
            ((Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n))).symm i))^2 := by
        intro i
        rw [Matrix.SVD.singularValues_eq_singularValues₀]
      simp_rw [h]
      -- Now: ∑ i : n, sv₀ (e.symm i)^2 = ∑ j : Fin n, sv₀ j^2
      -- Use Fintype.sum_equiv with e.symm : n ≃ Fin (card n)
      let e := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n))
      exact Fintype.sum_equiv e.symm
        (fun i => (Matrix.SVD.singularValues₀ (Sig - C) (e.symm i))^2)
        (fun j => (Matrix.SVD.singularValues₀ (Sig - C) j)^2)
        (fun i => rfl)

    -- Key lemma: singularValues₀ Sig = singularValues₀ A
    -- This is because Sig = diagonal(σ) where σ = singularValues A
    -- For a diagonal matrix with non-negative entries, the singular values
    -- are exactly those entries (possibly reordered for sorting)
    -- Here, both use the same sorted ordering via eigenvalues₀
    have h_sv_eq : ∀ j, Matrix.SVD.singularValues₀ Sig j = Matrix.SVD.singularValues₀ A j := by
      intro j
      -- Strategy: Sig = diagonal(singularValues A) has the same singular values as A
      -- because singularValues of a diagonal matrix with nonneg sorted entries are those entries.
      --
      -- Key facts:
      -- 1. singularValues₀ M k = √(eigenvalues₀ (MᴴM) k)
      -- 2. For Sig = diagonal(d) with d = singularValues A:
      --    Sigᴴ * Sig = diagonal(d²) since Sig is real diagonal
      -- 3. eigenvalues₀ of diagonal(d²) = d² (entries already sorted since d is antitone)
      -- 4. √(d²) = d since d ≥ 0
      -- 5. Therefore singularValues₀ Sig = d = singularValues₀ A

      -- Use the SVD relationship: A = U * Sig * V* implies Sigᴴ Sig and Aᴴ A have same eigenvalues
      -- More directly: Sig = diagonal(singularValues A) and singularValues A = singularValues₀ A ∘ e
      -- where e is the canonical equivalence.

      -- The singular values of diagonal(Complex.ofReal ∘ sv) are |sv| = sv (since sv ≥ 0)
      -- This follows from: (diagonal d)ᴴ * (diagonal d) = diagonal(|d|²)
      -- eigenvalues of diagonal(r²) = {r²} for r ≥ 0
      -- So singularValues = √eigenvalues = |r| = r

      -- We prove this by showing:
      -- singularValues₀ Sig j = singularValues₀ A j
      -- Both equal √(eigenvalues₀ (Aᴴ A) j) by definition

      -- Key: Sigᴴ * Sig = diagonal((singularValues A)²) since Sig is real diagonal
      have h_SigH_Sig : Sigᴴ * Sig = diagonal (fun i => (Complex.ofReal (Matrix.SVD.singularValues A i))^2) := by
        simp only [Sig, diagonal_conjTranspose]
        rw [diagonal_mul_diagonal]
        congr 1
        ext i
        simp only [Function.comp_apply, Pi.star_apply]
        -- Goal: star (↑(singularValues A i)) * ↑(singularValues A i) = ↑(singularValues A i) ^ 2
        -- Since ofReal σ is real, star(ofReal σ) = ofReal σ
        simp only [Complex.star_def, Complex.conj_ofReal, sq]

      -- And Aᴴ * A has eigenvalues (singularValues A)² = (singularValues₀ A ∘ e)²
      -- where e : Fin (card n) ≃ n

      -- The eigenvalues₀ of Sigᴴ * Sig equal those of Aᴴ * A
      -- because they have the same characteristic polynomial (both = ∏(X - σᵢ²))

      -- For diagonal matrices: eigenvalues₀ = sorted diagonal entries
      -- singularValues A are already sorted (antitone) via eigenvalues₀
      -- So eigenvalues₀(Sigᴴ Sig) = (singularValues A)² = eigenvalues₀(Aᴴ A)

      -- Therefore singularValues₀ Sig = √eigenvalues₀(Sigᴴ Sig) = √eigenvalues₀(Aᴴ A) = singularValues₀ A

      -- We need to show: √(eigenvalues₀ (Sigᴴ*Sig) j) = √(eigenvalues₀ (Aᴴ*A) j)
      -- This follows from showing eigenvalues₀ (Sigᴴ*Sig) j = eigenvalues₀ (Aᴴ*A) j

      -- Use that both Hermitian matrices have the same characteristic polynomial
      have h_AHA : (Aᴴ * A).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self A
      have h_SigHSig : (Sigᴴ * Sig).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self Sig

      have h_charpoly_eq : (Sigᴴ * Sig).charpoly = (Aᴴ * A).charpoly := by
        -- charpoly of diagonal = product of (X - entries)
        rw [h_SigH_Sig, charpoly_diagonal]

        -- Use that IsHermitian.charpoly_eq
        have h_AHA_charpoly := h_AHA.isHermitian.charpoly_eq
        rw [h_AHA_charpoly]

        -- Need: ∏ i, (X - C(σᵢ²)) = ∏ i, (X - C(eigenvalues(Aᴴ A) i))
        apply Finset.prod_congr rfl
        intro i _
        have h_sv_sq := Matrix.SVD.singularValues_sq A i
        rw [← Complex.ofReal_pow, sq]
        rw [sq] at h_sv_sq
        congr 2
        exact congrArg Complex.ofReal h_sv_sq

      -- Now use eigenvalues_eq_eigenvalues_iff to get eigenvalues equality
      have h_eig_eq := (h_SigHSig.isHermitian.eigenvalues_eq_eigenvalues_iff h_AHA.isHermitian).mpr h_charpoly_eq
      -- h_eig_eq : eigenvalues (Sigᴴ Sig) = eigenvalues (Aᴴ A)

      -- Get eigenvalues₀ equality at index j
      have h_at_j : h_SigHSig.isHermitian.eigenvalues₀ j = h_AHA.isHermitian.eigenvalues₀ j := by
        have := congrFun h_eig_eq
        unfold Matrix.IsHermitian.eigenvalues at this
        let e := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n))
        have h := this (e j)
        simp only [e, Equiv.symm_apply_apply] at h
        exact h

      -- Now show singularValues₀ equality via sqrt
      simp only [Matrix.SVD.singularValues₀]
      -- Apply congrArg to √ to transfer eigenvalues₀ equality
      apply congrArg Real.sqrt
      -- h_at_j : h_SigHSig.isHermitian.eigenvalues₀ j = h_AHA.isHermitian.eigenvalues₀ j
      -- The goal is: (psd Sig).isHermitian.eigenvalues₀ j = (psd A).isHermitian.eigenvalues₀ j
      -- Both proofs are definitionally equal (both are `posSemidef_conjTranspose_mul_self _`)
      have h_eig_SigH : h_SigHSig.isHermitian.eigenvalues₀ j =
          (posSemidef_conjTranspose_mul_self Sig).isHermitian.eigenvalues₀ j := rfl
      have h_eig_AH : h_AHA.isHermitian.eigenvalues₀ j =
          (posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues₀ j := rfl
      rw [← h_eig_SigH, ← h_eig_AH]
      exact h_at_j

    -- Apply the bounds using a two-step inequality chain:
    -- Step 1: Termwise interlacing on the tail (j ≥ k)
    -- Step 2: Reindexed sum ≤ full sum

    -- Reindex LHS to filter form
    have h_lhs_reindex : ∑ i : n, (Matrix.SVD.truncatedSingularValues_tail A k i)^2 =
        ∑ j : Fin (Fintype.card n), (if k ≤ j.val then (Matrix.SVD.singularValues₀ A j)^2 else 0) := by
      let e := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n))
      have h : ∀ i : n, (Matrix.SVD.truncatedSingularValues_tail A k i)^2 =
          (if k ≤ (e.symm i).val then (Matrix.SVD.singularValues₀ A (e.symm i))^2 else 0) := by
        intro i
        unfold Matrix.SVD.truncatedSingularValues_tail
        simp only [e]
        split_ifs with h1
        · ring
        · ring
      simp_rw [h]
      exact Fintype.sum_equiv e.symm _ _ (fun _ => rfl)

    -- Convert to filter sum
    have h_filter_eq : ∑ j : Fin (Fintype.card n), (if k ≤ j.val then (Matrix.SVD.singularValues₀ A j)^2 else 0) =
        (Finset.filter (fun j : Fin (Fintype.card n) => k ≤ j.val) Finset.univ).sum
          (fun j => (Matrix.SVD.singularValues₀ A j)^2) := by
      rw [← Finset.sum_filter]

    -- Step 1: Termwise interlacing on the filtered set
    -- For j ≥ k: (sv₀ A j)² ≤ (sv₀ (Sig-C) (j-k))²
    have h_interlacing_sum :
        (Finset.filter (fun j : Fin (Fintype.card n) => k ≤ j.val) Finset.univ).sum
          (fun j => (Matrix.SVD.singularValues₀ A j)^2) ≤
        (Finset.filter (fun j : Fin (Fintype.card n) => k ≤ j.val) Finset.univ).sum
          (fun j => (Matrix.SVD.singularValues₀ (Sig - C) ⟨j.val - k, by omega⟩)^2) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjk : k ≤ j.val := (Finset.mem_filter.mp hj).2
      have h_interlace := Matrix.WeylInequality.interlacing_low_rank_subtraction Sig C k _hC j hjk
      have h_nonneg_SigC : 0 ≤ Matrix.SVD.singularValues₀ (Sig - C) ⟨j.val - k, by omega⟩ :=
        Matrix.SVD.singularValues₀_nonneg _ _
      have h_nonneg_Sig : 0 ≤ Matrix.SVD.singularValues₀ Sig j :=
        Matrix.SVD.singularValues₀_nonneg _ _
      -- Show (sv₀ A j)² ≤ (sv₀ (Sig-C) (j-k))²
      calc (Matrix.SVD.singularValues₀ A j)^2
          = (Matrix.SVD.singularValues₀ Sig j)^2 := by rw [h_sv_eq]
        _ ≤ (Matrix.SVD.singularValues₀ (Sig - C) ⟨j.val - k, by omega⟩)^2 := by
            have h_nonneg_A : 0 ≤ Matrix.SVD.singularValues₀ A j :=
              Matrix.SVD.singularValues₀_nonneg _ _
            nlinarith [sq_nonneg (Matrix.SVD.singularValues₀ Sig j),
                       sq_nonneg (Matrix.SVD.singularValues₀ (Sig - C) ⟨j.val - k, by omega⟩),
                       h_interlace, h_nonneg_Sig, h_nonneg_SigC, h_sv_eq j]

    -- Step 2: The reindexed sum is ≤ the full sum
    -- Key insight: For j ≥ k, the index (j - k) ranges over 0..(card n - k - 1)
    -- This is an injective map into 0..(card n - 1), so the sum is ≤ full sum
    have h_subset_sum :
        (Finset.filter (fun j : Fin (Fintype.card n) => k ≤ j.val) Finset.univ).sum
          (fun j => (Matrix.SVD.singularValues₀ (Sig - C) ⟨j.val - k, by omega⟩)^2) ≤
        ∑ j : Fin (Fintype.card n), (Matrix.SVD.singularValues₀ (Sig - C) j)^2 := by
      -- All terms are nonneg
      have h_term_nonneg : ∀ j, 0 ≤ (Matrix.SVD.singularValues₀ (Sig - C) j)^2 := fun j => sq_nonneg _

      -- The shifted indices {j - k : j ≥ k} form a subset of {0, ..., card n - 1}
      -- We can bound by the sum over all indices since all terms are nonneg

      -- Use a transitivity argument:
      -- LHS = sum over filter of f(j-k)
      -- Show this equals sum over image of shift function
      -- The image is a subset, so sum ≤ full sum

      -- Define the shift function
      let shift : Fin (Fintype.card n) → Fin (Fintype.card n) :=
        fun j => if h : k ≤ j.val then ⟨j.val - k, by omega⟩ else ⟨0, by omega⟩

      -- The function applied with shift
      let g : Fin (Fintype.card n) → ℝ := fun j => (Matrix.SVD.singularValues₀ (Sig - C) j)^2

      -- Show LHS = sum of g over image of shift restricted to filter
      have h_sum_eq : (Finset.filter (fun j : Fin (Fintype.card n) => k ≤ j.val) Finset.univ).sum
            (fun j => (Matrix.SVD.singularValues₀ (Sig - C) ⟨j.val - k, by omega⟩)^2) =
          (Finset.filter (fun j : Fin (Fintype.card n) => k ≤ j.val) Finset.univ).sum
            (fun j => g (shift j)) := by
        apply Finset.sum_congr rfl
        intro j hj
        simp only [g, shift]
        have hjk : k ≤ j.val := (Finset.mem_filter.mp hj).2
        simp only [hjk, dite_true]

      rw [h_sum_eq]

      -- The image of shift on the filter is a subset of univ
      -- Use sum_le_sum_of_subset
      have h_image_subset : (Finset.filter (fun j : Fin (Fintype.card n) => k ≤ j.val) Finset.univ).image shift ⊆ Finset.univ := by
        intro x _
        exact Finset.mem_univ x

      -- shift is injective on the filter
      have h_shift_inj : Set.InjOn shift (Finset.filter (fun j : Fin (Fintype.card n) => k ≤ j.val) Finset.univ : Set _) := by
        intro j₁ hj₁ j₂ hj₂ heq
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hj₁ hj₂
        simp only [shift] at heq
        simp only [hj₁, hj₂, dite_true] at heq
        have h_val_eq : j₁.val - k = j₂.val - k := Fin.mk.inj heq
        ext
        omega

      -- Use sum_image to convert: filter.sum (g ∘ shift) = image.sum g
      have h_sum_image := Finset.sum_image h_shift_inj (f := g)

      calc (Finset.filter (fun j : Fin (Fintype.card n) => k ≤ j.val) Finset.univ).sum (fun j => g (shift j))
          = ((Finset.filter (fun j : Fin (Fintype.card n) => k ≤ j.val) Finset.univ).image shift).sum g := h_sum_image.symm
        _ ≤ Finset.univ.sum g := by
            apply Finset.sum_le_sum_of_subset_of_nonneg h_image_subset
            intro i _ _
            exact h_term_nonneg i
        _ = ∑ j : Fin (Fintype.card n), (Matrix.SVD.singularValues₀ (Sig - C) j)^2 := rfl

    -- Chain the inequalities
    calc ∑ i : n, (Matrix.SVD.truncatedSingularValues_tail A k i)^2
        = ∑ j : Fin (Fintype.card n), (if k ≤ j.val then (Matrix.SVD.singularValues₀ A j)^2 else 0) := h_lhs_reindex
      _ = (Finset.filter (fun j : Fin (Fintype.card n) => k ≤ j.val) Finset.univ).sum
            (fun j => (Matrix.SVD.singularValues₀ A j)^2) := h_filter_eq
      _ ≤ (Finset.filter (fun j : Fin (Fintype.card n) => k ≤ j.val) Finset.univ).sum
            (fun j => (Matrix.SVD.singularValues₀ (Sig - C) ⟨j.val - k, by omega⟩)^2) := h_interlacing_sum
      _ ≤ ∑ j : Fin (Fintype.card n), (Matrix.SVD.singularValues₀ (Sig - C) j)^2 := h_subset_sum
      _ = ∑ i : n, (Matrix.SVD.singularValues (Sig - C) i)^2 := h_sv_sum.symm
      _ = ‖Sig - C‖^2 := h_frob_sv.symm
      _ = ∑ i, ‖(Complex.ofReal ∘ σ) i - C i i‖^2 +
          ∑ i, ∑ j, (if i ≠ j then ‖C i j‖^2 else 0) := h_rhs'.symm

end EckartYoung

end Matrix.FrobeniusNorm
