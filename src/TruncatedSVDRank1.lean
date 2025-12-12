/-
Copyright (c) 2025 FLYWHEEL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aleksandar Markovski
-/
import SVD
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Truncated SVD for Rank-1 Matrices

For rank(A) ≤ 1: truncatedSVD(A,1) = A. Follows from σₖ = 0 for k ≥ 1.

## Status

This is the simplest case of truncated SVD. The general k-rank case is harder
and would require more machinery from Eckart-Young.

Created: 2025-01-02
Last modified: 2025-01-05 (fixed off-by-one in index bounds)
-/

open Matrix Matrix.SVD
open scoped ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

-- Q: should this be in SVD.lean instead? It's kinda SVD-specific.

/-- If rank(A) ≤ 1, then singular values at indices ≥ 1 are zero. -/
theorem singularValues₀_eq_zero_of_rank_le_one (A : Matrix n n ℂ) (h : A.rank ≤ 1)
    (k : Fin (Fintype.card n)) (hk : 1 ≤ k.val) :
    singularValues₀ A k = 0 := by
  -- rank A = rank (Aᴴ * A)
  have h_rank_eq : (Aᴴ * A).rank = A.rank := rank_conjTranspose_mul_self A

  let hpsd := posSemidef_conjTranspose_mul_self A
  let hermAHA := hpsd.isHermitian
  have h_rank_card : (Aᴴ * A).rank = Fintype.card { i : n // hermAHA.eigenvalues i ≠ 0 } :=
    hermAHA.rank_eq_card_non_zero_eigs

  -- The number of non-zero eigenvalues is the same for sorted eigenvalues
  have h_card_eq : Fintype.card { i : n // hermAHA.eigenvalues i ≠ 0 } =
                   Fintype.card { k : Fin (Fintype.card n) // hermAHA.eigenvalues₀ k ≠ 0 } := by
    let e := (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n)) : Fin (Fintype.card n) ≃ n)
    apply Fintype.card_congr
    exact {
      toFun := fun ⟨i, hi⟩ => ⟨e.symm i, by
        simp only [ne_eq, IsHermitian.eigenvalues, IsHermitian.eigenvalues₀] at hi ⊢
        convert hi using 2⟩
      invFun := fun ⟨j, hj⟩ => ⟨e j, by
        simp only [ne_eq, IsHermitian.eigenvalues, IsHermitian.eigenvalues₀] at hj ⊢
        convert hj using 2
        simp only [e, Equiv.symm_apply_apply]⟩
      left_inv := fun ⟨i, hi⟩ => Subtype.ext (e.apply_symm_apply i)
      right_inv := fun ⟨j, hj⟩ => Subtype.ext (e.symm_apply_apply j)
    }

  -- Transform h to use eigenvalues₀
  have h' : Fintype.card { k : Fin (Fintype.card n) // hermAHA.eigenvalues₀ k ≠ 0 } ≤ 1 := by
    calc Fintype.card { k : Fin (Fintype.card n) // hermAHA.eigenvalues₀ k ≠ 0 }
        = Fintype.card { i : n // hermAHA.eigenvalues i ≠ 0 } := h_card_eq.symm
      _ = (Aᴴ * A).rank := h_rank_card.symm
      _ = A.rank := h_rank_eq
      _ ≤ 1 := h

  -- eigenvalues₀ is antitone and non-negative
  have h_antitone : Antitone hermAHA.eigenvalues₀ := hermAHA.eigenvalues₀_antitone
  have h_nonneg : ∀ j, 0 ≤ hermAHA.eigenvalues₀ j := PosSemidef_eigenvalues₀_nonneg hpsd

  -- Use the helper lemma for eigenvalues
  have h_eig_zero : hermAHA.eigenvalues₀ k = 0 :=
    antitone_nonneg_zeros_after_rank hermAHA.eigenvalues₀ h_antitone h_nonneg h' k hk

  -- singular value is sqrt of eigenvalue
  unfold singularValues₀
  rw [h_eig_zero, Real.sqrt_zero]

/-- If rank(A) ≤ 1, then the truncated SVD with k=1 recovers the original matrix. -/
theorem truncatedSVD_rank1_identity (A : Matrix n n ℂ) (h : A.rank ≤ 1) :
    truncatedSVD A 1 = A := by
  -- Use the SVD decomposition: A = U * Σ * Vᴴ
  have h_svd := AV_eq_constructedU_mul_sigma A
  have h_V_unitary : (rightUnitary A : Matrix n n ℂ) * star (rightUnitary A : Matrix n n ℂ) = 1 :=
    mem_unitaryGroup_iff.mp (rightUnitary A).2

  -- Show truncatedSVD A 1 = U * Σ_truncated * Vᴴ = U * Σ * Vᴴ = A
  -- by showing truncated singular values = singular values when rank ≤ 1
  unfold truncatedSVD

  -- Show the diagonal matrices are equal
  have h_diag_eq : diagonal (Complex.ofReal ∘ truncatedSingularValues A 1) =
                   diagonal (Complex.ofReal ∘ singularValues A) := by
    ext i j
    simp only [diagonal_apply, Function.comp_apply]
    split_ifs with h_eq
    · subst h_eq
      simp only [truncatedSingularValues, singularValues_eq_singularValues₀]
      split_ifs with h_lt
      · -- idx < 1, so idx = 0, trivially equal
        rfl
      · -- idx ≥ 1, so singular value is 0 anyway due to rank ≤ 1
        simp only [Complex.ofReal_inj]
        symm
        apply singularValues₀_eq_zero_of_rank_le_one A h
        exact not_lt.mp h_lt
    · rfl

  rw [h_diag_eq]

  -- Now show U * Σ * Vᴴ = A
  calc (constructedU A : Matrix n n ℂ) * diagonal (Complex.ofReal ∘ singularValues A) * star (rightUnitary A : Matrix n n ℂ)
      = ((constructedU A : Matrix n n ℂ) * diagonal (Complex.ofReal ∘ singularValues A)) * star (rightUnitary A : Matrix n n ℂ) := by rw [mul_assoc]
    _ = (A * (rightUnitary A : Matrix n n ℂ)) * star (rightUnitary A : Matrix n n ℂ) := by rw [← h_svd]
    _ = A * ((rightUnitary A : Matrix n n ℂ) * star (rightUnitary A : Matrix n n ℂ)) := by rw [mul_assoc]
    _ = A * 1 := by rw [h_V_unitary]
    _ = A := by rw [mul_one]
