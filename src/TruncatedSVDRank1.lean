/-
Copyright (c) 2025 FLYWHEEL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aleksandar Markovski
-/
module

public import SVD
public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Truncated SVD of Low-Rank Matrices

For rank(A) ≤ k: truncatedSVD(A, k) = A (`truncatedSVD_eq_self_of_rank_le`), since σⱼ = 0 for
j ≥ k (`singularValues₀_eq_zero_of_rank_le`). The rank-1 case is
`truncatedSVD_rank1_identity`.

Created: 2025-01-02
Last modified: 2025-01-05 (fixed off-by-one in index bounds)
-/

public section

open Matrix Matrix.SVD
open scoped ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

-- Q: should this be in SVD.lean instead? It's kinda SVD-specific.

/-- If rank(A) ≤ k, then the sorted singular values at indices ≥ k are zero. -/
theorem singularValues₀_eq_zero_of_rank_le (A : Matrix n n ℂ) {k : ℕ} (h : A.rank ≤ k)
    (j : Fin (Fintype.card n)) (hj : k ≤ j.val) :
    singularValues₀ A j = 0 := by
  unfold singularValues₀
  rw [Matrix.SVD.Rectangular.eigenvalues₀_zero_beyond_rank A j (le_trans h hj), Real.sqrt_zero]

/-- If rank(A) ≤ k, then the rank-k truncated SVD recovers A. -/
theorem truncatedSVD_eq_self_of_rank_le (A : Matrix n n ℂ) (k : ℕ) (h : A.rank ≤ k) :
    truncatedSVD A k = A := by
  -- Use the SVD decomposition: A = U * Σ * Vᴴ
  have h_svd := AV_eq_constructedU_mul_sigma A
  have h_V_unitary : (rightUnitary A : Matrix n n ℂ) * star (rightUnitary A : Matrix n n ℂ) = 1 :=
    mem_unitaryGroup_iff.mp (rightUnitary A).2

  -- Show truncatedSVD A 1 = U * Σ_truncated * Vᴴ = U * Σ * Vᴴ = A
  -- by showing truncated singular values = singular values when rank ≤ k
  unfold truncatedSVD

  -- Show the diagonal matrices are equal
  have h_diag_eq : diagonal (Complex.ofReal ∘ truncatedSingularValues A k) =
                   diagonal (Complex.ofReal ∘ singularValues A) := by
    ext i j
    simp only [diagonal_apply, Function.comp_apply]
    split_ifs with h_eq
    · subst h_eq
      simp only [truncatedSingularValues, singularValues_eq_singularValues₀]
      split_ifs with h_lt
      · -- idx < k: the truncation keeps σ_idx
        rfl
      · -- idx ≥ k: σ_idx = 0 since rank ≤ k
        simp only [Complex.ofReal_inj]
        symm
        exact singularValues₀_eq_zero_of_rank_le A h _ (not_lt.mp h_lt)
    · rfl

  rw [h_diag_eq]

  -- Now show U * Σ * Vᴴ = A
  calc (constructedU A : Matrix n n ℂ) * diagonal (Complex.ofReal ∘ singularValues A) * star (rightUnitary A : Matrix n n ℂ)
      = ((constructedU A : Matrix n n ℂ) * diagonal (Complex.ofReal ∘ singularValues A)) * star (rightUnitary A : Matrix n n ℂ) := by rw [mul_assoc]
    _ = (A * (rightUnitary A : Matrix n n ℂ)) * star (rightUnitary A : Matrix n n ℂ) := by rw [← h_svd]
    _ = A * ((rightUnitary A : Matrix n n ℂ) * star (rightUnitary A : Matrix n n ℂ)) := by rw [mul_assoc]
    _ = A * 1 := by rw [h_V_unitary]
    _ = A := by rw [mul_one]

/-- If rank(A) ≤ 1, then the truncated SVD with k = 1 recovers A. -/
theorem truncatedSVD_rank1_identity (A : Matrix n n ℂ) (h : A.rank ≤ 1) :
    truncatedSVD A 1 = A :=
  truncatedSVD_eq_self_of_rank_le A 1 h
