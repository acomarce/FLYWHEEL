/-
Copyright (c) 2025 FLYWHEEL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aleksandar Markovski
-/
import MatrixNormRelations
import SpectralNormGap

/-!
# Coherence Characterization for Kronecker Approximation

Defines μ(E) = ‖E‖_F / (√rank · ‖E‖₂) ∈ [1/√r, 1].
μ ≈ 1 implies incoherent (flat spectrum), μ ≈ 1/√r implies coherent.

Here "coherence" is this norm ratio only. It is not the singular-vector coherence of the
matrix-completion references below, which are background reading, not sources of proofs.

## References

[1] Candès & Recht (2009). Found. Comput. Math. 9(6), 717–772.
[2] Tropp, J. (2012). Found. Comput. Math. 12(4), 389–434.

## Notes

This file has gotten quite long (almost 2000 lines). Should probably split it up
into separate files for:
- Basic coherence definitions
- Rank-related lemmas
- The main characterization theorems

But that's a refactor for another day...
-/

open scoped ComplexOrder Matrix
open Matrix SpectralNorm

namespace Matrix.Coherence

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

section RankSingularValues

variable {n : Type*} [Fintype n] [DecidableEq n]

-- I spent way too long on this section. The key insight is that singular values
-- are just square roots of eigenvalues of A^H A, so nonzero sv <-> nonzero eig.
-- Seems obvious in retrospect but the type theory made it tricky.

/-- Nonzero singular values correspond to nonzero eigenvalues of Aᴴ * A.
    Since σᵢ = √(λᵢ) where λᵢ ≥ 0, we have σᵢ ≠ 0 ↔ λᵢ ≠ 0. -/
theorem singularValues_ne_zero_iff_eigenvalues_ne_zero (A : Matrix n n ℂ) (i : n) :
    SVD.singularValues A i ≠ 0 ↔
    (posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues i ≠ 0 := by
  have h_psd := posSemidef_conjTranspose_mul_self A
  have h_eig_nonneg := h_psd.eigenvalues_nonneg i
  constructor
  · -- If σᵢ ≠ 0, then σᵢ² ≠ 0, so λᵢ ≠ 0
    intro h_sv_ne h_eig_eq
    rw [SVD.singularValues] at h_sv_ne
    simp only [h_eig_eq, Real.sqrt_zero, ne_eq, not_true] at h_sv_ne
  · intro h_eig_ne
    -- If λᵢ ≠ 0 and λᵢ ≥ 0, then λᵢ > 0, so √λᵢ > 0 ≠ 0
    rw [SVD.singularValues]
    have h_pos : 0 < h_psd.isHermitian.eigenvalues i := lt_of_le_of_ne h_eig_nonneg (ne_comm.mpr h_eig_ne)
    exact ne_of_gt (Real.sqrt_pos.mpr h_pos)

/-- The rank of a matrix equals the number of nonzero singular values.
    This follows from rank(A) = rank(Aᴴ * A) and the Hermitian eigenvalue characterization. -/
theorem rank_eq_card_nonzero_singularValues (A : Matrix n n ℂ) :
    A.rank = Fintype.card {i : n // SVD.singularValues A i ≠ 0} := by
  have h_psd := posSemidef_conjTranspose_mul_self A
  have herm := h_psd.isHermitian

  -- Step 1: rank(A) = rank(Aᴴ * A)
  have h_rank_eq : A.rank = (Aᴴ * A).rank := (rank_conjTranspose_mul_self A).symm

  -- Step 2: rank(Aᴴ * A) = |{i : eigenvalues i ≠ 0}| by Hermitian characterization
  have h_herm_rank : (Aᴴ * A).rank = Fintype.card {i : n // herm.eigenvalues i ≠ 0} :=
    herm.rank_eq_card_non_zero_eigs

  -- Step 3: Build bijection between {σᵢ ≠ 0} and {λᵢ ≠ 0}
  have h_card_eq : Fintype.card {i : n // SVD.singularValues A i ≠ 0} =
                   Fintype.card {i : n // herm.eigenvalues i ≠ 0} := by
    apply Fintype.card_eq.mpr
    refine ⟨{
      toFun := fun ⟨i, hi⟩ => ⟨i, (singularValues_ne_zero_iff_eigenvalues_ne_zero A i).mp hi⟩
      invFun := fun ⟨i, hi⟩ => ⟨i, (singularValues_ne_zero_iff_eigenvalues_ne_zero A i).mpr hi⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
    }⟩

  rw [h_rank_eq, h_herm_rank, h_card_eq]

end RankSingularValues

/-- The sum of squared singular values is bounded by rank(A) times the max squared.
    Key insight: only rank(A) singular values are nonzero, and each is ≤ max. -/
theorem sum_singularValues_sq_le_rank_mul_max_sq (A : Matrix n n ℂ) :
    ∑ i, SVD.singularValues A i ^ 2 ≤
    A.rank * (Finset.sup' Finset.univ Finset.univ_nonempty (SVD.singularValues A)) ^ 2 := by
  let M := Finset.sup' Finset.univ Finset.univ_nonempty (SVD.singularValues A)
  have hM_nonneg : 0 ≤ M := Finset.le_sup'_of_le _ (Finset.mem_univ (Classical.arbitrary n))
                             (SVD.singularValues_nonneg A _)
  have h_le_M : ∀ i, SVD.singularValues A i ≤ M := fun i =>
    Finset.le_sup' (SVD.singularValues A) (Finset.mem_univ i)

  have h_rank := rank_eq_card_nonzero_singularValues A

  -- Bound each term by M²
  have h_each_le : ∀ i, SVD.singularValues A i ^ 2 ≤ M ^ 2 := fun i => by
    apply sq_le_sq'
    · calc -M ≤ 0 := neg_nonpos.mpr hM_nonneg
        _ ≤ SVD.singularValues A i := SVD.singularValues_nonneg A i
    · exact h_le_M i

  -- Split into nonzero and zero contributions
  let S := {i : n | SVD.singularValues A i ≠ 0}.toFinset
  have hS_card : S.card = A.rank := by
    rw [h_rank]
    simp only [S, Set.toFinset_card]
    rfl

  -- Sum over nonzero equals original sum (zero terms contribute 0)
  have h_sum_eq : ∑ i, SVD.singularValues A i ^ 2 = ∑ i ∈ S, SVD.singularValues A i ^ 2 := by
    rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ) (p := fun i => i ∈ S)]
    simp only [S, Set.mem_toFinset, Set.mem_setOf_eq]
    have h_zero_sum : ∑ i ∈ Finset.univ.filter (fun i => SVD.singularValues A i = 0),
        SVD.singularValues A i ^ 2 = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      simp [hi]
    simp only [not_not]
    rw [h_zero_sum, add_zero]
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, ne_eq, Set.mem_toFinset,
      Set.mem_setOf_eq]

  calc ∑ i, SVD.singularValues A i ^ 2
      = ∑ i ∈ S, SVD.singularValues A i ^ 2 := h_sum_eq
    _ ≤ ∑ _i ∈ S, M ^ 2 := Finset.sum_le_sum fun i _ => h_each_le i
    _ = S.card * M ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
    _ = A.rank * M ^ 2 := by rw [hS_card]

section RankPos

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A non-zero matrix has positive rank (the square case of `rank_pos_of_ne_zero_rect`). -/
theorem rank_pos_of_ne_zero (A : Matrix n n ℂ) (hA : A ≠ 0) : 0 < A.rank :=
  rank_pos_of_ne_zero_rect A hA

end RankPos

/-- The sum of squared singular values is bounded by n times the max squared singular value.
    Each σᵢ is at most maxⱼ σⱼ. -/
theorem sum_singularValues_sq_le_card_mul_max_sq (A : Matrix n n ℂ) :
    ∑ i, SVD.singularValues A i ^ 2 ≤
    Fintype.card n * (Finset.sup' Finset.univ Finset.univ_nonempty (SVD.singularValues A)) ^ 2 := by
  have h_le : ∀ i, SVD.singularValues A i ≤
      Finset.sup' Finset.univ Finset.univ_nonempty (SVD.singularValues A) := fun i =>
    Finset.le_sup' (SVD.singularValues A) (Finset.mem_univ i)
  have h_nonneg : 0 ≤ Finset.sup' Finset.univ Finset.univ_nonempty (SVD.singularValues A) := by
    apply Finset.le_sup'_of_le (SVD.singularValues A) (Finset.mem_univ (Classical.arbitrary n))
    exact SVD.singularValues_nonneg A _
  calc ∑ i, SVD.singularValues A i ^ 2
      ≤ ∑ _i : n, (Finset.sup' Finset.univ Finset.univ_nonempty (SVD.singularValues A)) ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        have h_i_nonneg : 0 ≤ SVD.singularValues A i := SVD.singularValues_nonneg A i
        apply sq_le_sq'
        · linarith [h_nonneg]
        · exact h_le i
    _ = Fintype.card n * (Finset.sup' Finset.univ Finset.univ_nonempty (SVD.singularValues A)) ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ]
        ring

/-- The Frobenius-to-spectral ratio is bounded by √(dim).
    frobeniusNorm' A / ‖A‖ ≤ √n -/
theorem frobenius_spectral_ratio_le_sqrt_dim (A : Matrix n n ℂ) (hA : A ≠ 0) :
    frobeniusNorm' A / ‖A‖ ≤ Real.sqrt (Fintype.card n) := by
  have h_spectral_pos : 0 < ‖A‖ := norm_pos_iff.mpr hA
  have h_frob_nonneg : 0 ≤ frobeniusNorm' A := frobeniusNorm'_nonneg A
  rw [div_le_iff₀' h_spectral_pos]
  -- Goal: frobeniusNorm' A ≤ √n · ‖A‖
  -- Square both sides: frobeniusNorm' A² ≤ n · ‖A‖²
  have h_sq : frobeniusNorm' A ^ 2 ≤ Fintype.card n * ‖A‖ ^ 2 := by
    -- Use: frobeniusNorm' A² ≤ ∑ σᵢ² ≤ n · max(σᵢ)² = n · ‖A‖²
    have h_spec_sq : ‖A‖ ^ 2 =
        (Finset.sup' Finset.univ Finset.univ_nonempty (SVD.singularValues A)) ^ 2 := by
      rw [spectral_norm_eq_max_singularValue]
      rfl
    calc frobeniusNorm' A ^ 2
        = ∑ i, SVD.singularValues A i ^ 2 := by
          -- frobeniusNorm' A² = trace(Aᴴ A) = ∑ σᵢ² (SVD characterization)
          rw [frobeniusNorm'_sq, SVD.sum_sq_singularValues_eq_trace]
          simp only [trace, diag_apply, mul_apply, conjTranspose_apply]
          rw [Finset.sum_comm]
          simp [Complex.re_sum, Complex.normSq]
      _ ≤ Fintype.card n * (Finset.sup' Finset.univ Finset.univ_nonempty (SVD.singularValues A)) ^ 2 :=
          sum_singularValues_sq_le_card_mul_max_sq A
      _ = Fintype.card n * ‖A‖ ^ 2 := by rw [h_spec_sq]
  -- Now derive the non-squared inequality
  have h_sqrt_card_nonneg : 0 ≤ Real.sqrt (Fintype.card n) := Real.sqrt_nonneg _
  have h_rhs_nonneg : 0 ≤ Real.sqrt (Fintype.card n) * ‖A‖ := mul_nonneg h_sqrt_card_nonneg (le_of_lt h_spectral_pos)
  have h_mul_comm : Real.sqrt (Fintype.card n) * ‖A‖ = ‖A‖ * Real.sqrt (Fintype.card n) := mul_comm _ _
  -- Goal: frobeniusNorm' A ≤ ‖A‖ * √n
  -- Use that frobeniusNorm' A² ≤ n * ‖A‖²
  have h_card_nonneg : (0 : ℝ) ≤ Fintype.card n := Nat.cast_nonneg _
  have h_sq' : frobeniusNorm' A ^ 2 ≤ (‖A‖ * Real.sqrt (Fintype.card n)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt h_card_nonneg, mul_comm]
    exact h_sq
  calc frobeniusNorm' A
      = Real.sqrt (frobeniusNorm' A ^ 2) := (Real.sqrt_sq h_frob_nonneg).symm
    _ ≤ Real.sqrt ((‖A‖ * Real.sqrt (Fintype.card n)) ^ 2) := Real.sqrt_le_sqrt h_sq'
    _ = ‖A‖ * Real.sqrt (Fintype.card n) := Real.sqrt_sq (mul_nonneg (le_of_lt h_spectral_pos) h_sqrt_card_nonneg)

/-! ## Coherence Factor Definition -/

/-- Coherence factor: measures how concentrated the singular values are.
    μ(E) = ‖E‖_F / (√rank(E) · ‖E‖₂) ∈ [1/√r, 1]

    - μ ≈ 1: Incoherent (flat spectrum, singular values roughly equal)
    - μ ≈ 1/√r: Coherent (dominated by top singular value) -/
noncomputable def coherenceFactor (E : Matrix n n ℂ) : ℝ :=
  if E = 0 then 1
  else frobeniusNorm' E / (Real.sqrt E.rank * ‖E‖)

omit [Nonempty n] in
/-- For the zero matrix, coherence factor is defined as 1. -/
theorem coherenceFactor_zero : coherenceFactor (0 : Matrix n n ℂ) = 1 := by
  simp [coherenceFactor]

omit [Nonempty n] in
/-- For square matrices, the rectangular coherence factor `coherenceFactorRect` (SVD.lean)
    agrees with `coherenceFactor`. -/
theorem coherenceFactorRect_eq_coherenceFactor (E : Matrix n n ℂ) :
    coherenceFactorRect E = coherenceFactor E := by
  by_cases hE : E = 0
  · rw [hE, coherenceFactorRect_zero, coherenceFactor_zero]
  · rw [coherenceFactorRect_eq_formula E hE]
    unfold coherenceFactor
    simp only [hE, ↓reduceIte]
    -- Both sides are ‖E‖_F / (√rank(E) · ‖E‖₂), with the same norms unfolded differently
    rfl

/-! ## Bounds on the coherence factor

The square results are the rectangular ones of SVD.lean (`coherenceFactorRect_le_one`, …)
transported by `coherenceFactorRect_eq_coherenceFactor`. -/

omit [Nonempty n] in
/-- The coherence factor is at most 1, since ‖E‖_F² = ∑ σᵢ² ≤ rank(E) · σ₀² = rank(E) · ‖E‖₂².
    The square case of `coherenceFactorRect_le_one`. -/
theorem coherenceFactor_le_one (E : Matrix n n ℂ) : coherenceFactor E ≤ 1 := by
  rw [← coherenceFactorRect_eq_coherenceFactor]
  exact coherenceFactorRect_le_one E

omit [Nonempty n] in
/-- The coherence factor is at least 1/√rank(E), since ‖E‖₂ ≤ ‖E‖_F.
    The square case of `coherenceFactorRect_ge_inv_sqrt_rank`. -/
theorem coherenceFactor_ge_inv_sqrt_rank (E : Matrix n n ℂ) (hE : E ≠ 0) :
    1 / Real.sqrt E.rank ≤ coherenceFactor E := by
  rw [← coherenceFactorRect_eq_coherenceFactor]
  exact coherenceFactorRect_ge_inv_sqrt_rank E hE

omit [Nonempty n] in
/-- The coherence factor is bounded: 1/√rank(E) ≤ μ(E) ≤ 1 -/
theorem coherenceFactor_bounds (E : Matrix n n ℂ) (hE : E ≠ 0) :
    1 / Real.sqrt E.rank ≤ coherenceFactor E ∧ coherenceFactor E ≤ 1 :=
  ⟨coherenceFactor_ge_inv_sqrt_rank E hE, coherenceFactor_le_one E⟩

/-! ## Spectral Bound with Coherence -/

omit [Nonempty n] in
/-- The spectral norm in terms of the coherence factor, for E ≠ 0:
    ‖E‖₂ = frobeniusNorm' E / (√rank(E) · μ(E)).

    This is the definition of μ solved for ‖E‖₂ (the square case of
    `spectral_norm_eq_frobenius_div_coherence_rect`).
    For incoherent matrices (μ ≈ 1), ‖E‖₂ ≈ ‖E‖_F / √rank.
    For coherent matrices (μ ≈ 1/√rank), ‖E‖₂ ≈ ‖E‖_F. -/
theorem spectral_norm_eq_frobenius_div_coherence (E : Matrix n n ℂ) (hE : E ≠ 0) :
    ‖E‖ = frobeniusNorm' E / (Real.sqrt E.rank * coherenceFactor E) := by
  rw [← coherenceFactorRect_eq_coherenceFactor]
  exact spectral_norm_eq_frobenius_div_coherence_rect E hE

/-! ## Coherent (Rank-1) Case - Tight Bounds

For rank-1 matrices (where 1/√rank = μ = 1), the spectral and Frobenius norms are equal:
‖u vᵀ‖₂ = ‖u vᵀ‖_F = ‖u‖·‖v‖.
-/

section CoherentCase

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-! ### Key Result: Outer Product Spectral Norm Equality

For an outer product u vᵀ, we prove ‖u vᵀ‖₂ = ‖u‖·‖v‖ (equality, not just ≤).
The upper bound comes from spectral ≤ Frobenius.
The lower bound is achieved by the witness w = v.
-/

omit [DecidableEq m] in
/-- Lower bound via witness: ‖u vᵀ‖₂ ≥ ‖u‖·‖v‖ when v ≠ 0.
    Apply u vᵀ to the witness w = conj(v): (u vᵀ) w = u · Σⱼ vⱼ conj(vⱼ) = ‖v‖² u, so
    ‖(u vᵀ) w‖ = ‖u‖·‖v‖² with ‖w‖ = ‖v‖. -/
theorem outerProduct_spectral_norm_ge [Nonempty m] [Nonempty n]
    (u : EuclideanSpace ℂ m) (v : EuclideanSpace ℂ n) (hv : v ≠ 0) :
    ‖u‖ * ‖v‖ ≤ @Norm.norm _ Matrix.instL2OpNormedAddCommGroup.toNorm
      (KroneckerRearrangement.outerProduct u v) := by
  by_cases hu : u = 0
  · simp only [hu, norm_zero, zero_mul, norm_nonneg]
  · -- **Witness strategy using star(v)**
    -- Key insight: outerProduct u v = u_i * v_j (no conjugate in definition)
    -- So (A * star(v))_i = ∑_j u_i * v_j * star(v_j) = u_i * (∑_j v_j * star(v_j))
    --                    = u_i * ∑_j |v_j|² = u_i * ‖v‖²
    -- Then ‖A * star(v)‖ = ‖v‖² * ‖u‖ and ‖star(v)‖ = ‖v‖
    -- By operator norm: ‖A‖ ≥ ‖A * star(v)‖ / ‖star(v)‖ = ‖v‖² * ‖u‖ / ‖v‖ = ‖u‖ * ‖v‖

    have h_norm_v_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv

    -- Define the witness: star(v) as a plain function n → ℂ
    let w : n → ℂ := fun j => star (v.ofLp j)

    -- The witness w has the same norm as v
    have h_norm_w : ‖(WithLp.equiv 2 (n → ℂ)).symm w‖ = ‖v‖ := by
      rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      -- ‖((WithLp.equiv 2 (n → ℂ)).symm w).ofLp j‖² = ‖v.ofLp j‖²
      -- The LHS simplifies to ‖star (v.ofLp j)‖² = ‖v.ofLp j‖² by norm_star
      have h1 : ((WithLp.equiv 2 (n → ℂ)).symm w).ofLp j = w j := rfl
      simp only [h1, w, norm_star]

    -- w is nonzero (since v ≠ 0)
    have h_w_ne : w ≠ 0 := by
      intro h_eq
      apply hv
      ext j
      have := congrFun h_eq j
      simp only [w, Pi.zero_apply] at this
      rw [star_eq_zero] at this
      exact this
    have h_norm_w_pos : 0 < ‖(WithLp.equiv 2 (n → ℂ)).symm w‖ := by rw [h_norm_w]; exact h_norm_v_pos

    -- Compute (outerProduct u v) *ᵥ w
    -- = ∑_j (u_i * v_j) * star(v_j) = u_i * (∑_j v_j * star(v_j)) = u_i * ‖v‖²
    have h_mulVec : (KroneckerRearrangement.outerProduct u v) *ᵥ w =
        ((‖v‖^2 : ℝ) : ℂ) • u.ofLp := by
      ext i
      simp only [mulVec, dotProduct, KroneckerRearrangement.outerProduct,
                 Pi.smul_apply, smul_eq_mul, w]
      -- Goal: ∑_j u_i * v_j * star(v_j) = ‖v‖² * u_i
      -- Factor out u_i: = u_i * ∑_j v_j * star(v_j)
      have h_factor : ∑ j, (u i : ℂ) * (v j : ℂ) * star (v j : ℂ) =
          (u i : ℂ) * ∑ j, (v j : ℂ) * star (v j : ℂ) := by
        rw [Finset.mul_sum]
        congr 1; ext j; ring
      rw [h_factor]
      -- Now show ∑_j v_j * star(v_j) = ‖v‖²
      have h_inner : ∑ j, (v j : ℂ) * star (v j : ℂ) = ((‖v‖^2 : ℝ) : ℂ) := by
        -- Each term v_j * star(v_j) = |v_j|² (real, nonneg)
        have h1 : ∀ j, (v j : ℂ) * star (v j : ℂ) = (Complex.normSq (v j) : ℂ) := fun j => by
          rw [Complex.normSq_eq_conj_mul_self]
          simp only [RCLike.star_def]
          ring
        simp_rw [h1]
        -- Sum of |v_j|² = ‖v‖² for EuclideanSpace
        have h2 : ∑ j, Complex.normSq (v j : ℂ) = ‖v‖^2 := by
          rw [EuclideanSpace.norm_sq_eq]
          congr 1; funext j
          rw [Complex.normSq_eq_norm_sq]
        rw [← Complex.ofReal_sum, h2]
      rw [h_inner]; ring

    -- Compute the norm of (outerProduct u v) *ᵥ w
    -- ‖(‖v‖² : ℂ) • u‖ = |‖v‖²| * ‖u‖ = ‖v‖² * ‖u‖
    have h_output_norm : ‖(EuclideanSpace.equiv m ℂ).symm
        ((KroneckerRearrangement.outerProduct u v) *ᵥ w)‖ = ‖v‖^2 * ‖u‖ := by
      simp only [h_mulVec]
      -- Need: ‖(EuclideanSpace.equiv m ℂ).symm (((‖v‖^2 : ℝ) : ℂ) • u.ofLp)‖ = ‖v‖² * ‖u‖
      have h_smul : (EuclideanSpace.equiv m ℂ).symm (((‖v‖^2 : ℝ) : ℂ) • u.ofLp) =
          ((‖v‖^2 : ℝ) : ℂ) • u := by
        ext i; simp [EuclideanSpace.equiv]
      rw [h_smul, norm_smul]
      -- ‖((‖v‖² : ℝ) : ℂ)‖ * ‖u‖ = |‖v‖²| * ‖u‖ = ‖v‖² * ‖u‖ (since ‖v‖² ≥ 0)
      congr 1
      rw [Complex.norm_of_nonneg (sq_nonneg _)]

    -- Use operator norm bound: ‖Ax‖ ≤ ‖A‖ * ‖x‖
    -- We need to convert w to EuclideanSpace to use l2_opNorm_mulVec
    let w' : EuclideanSpace ℂ n := (WithLp.equiv 2 (n → ℂ)).symm w
    have h_w'_ofLp : w'.ofLp = w := rfl
    have h_w'_norm : ‖w'‖ = ‖v‖ := h_norm_w
    have h_bound := Matrix.l2_opNorm_mulVec (KroneckerRearrangement.outerProduct u v) w'
    -- Rearrange: ‖A‖ ≥ ‖Ax‖ / ‖x‖
    -- Here: ‖A‖ ≥ ‖v‖² * ‖u‖ / ‖w'‖ = ‖v‖² * ‖u‖ / ‖v‖ = ‖u‖ * ‖v‖

    -- Use explicit L2 operator norm for Matrix m n ℂ
    let l2norm : Matrix m n ℂ → ℝ := @Norm.norm _ Matrix.instL2OpNormedAddCommGroup.toNorm
    -- Note: KroneckerRearrangement.outerProduct u v = KroneckerRearrangement.outerProduct u.ofLp v.ofLp
    -- definitionally, since EuclideanSpace ℂ m = WithLp 2 (m → ℂ) and .ofLp just unwraps

    calc ‖u‖ * ‖v‖
        = ‖v‖^2 * ‖u‖ / ‖v‖ := by field_simp
      _ = ‖(EuclideanSpace.equiv m ℂ).symm
            ((KroneckerRearrangement.outerProduct u v) *ᵥ w)‖ / ‖w'‖ := by
          rw [h_output_norm, h_w'_norm]
      _ ≤ l2norm (KroneckerRearrangement.outerProduct u v) * ‖w'‖ / ‖w'‖ := by
          gcongr
          rw [← h_w'_ofLp]
          exact h_bound
      _ = l2norm (KroneckerRearrangement.outerProduct u v) := by
          have h_w'_ne : ‖w'‖ ≠ 0 := ne_of_gt h_norm_w_pos
          field_simp [h_w'_ne]

omit [DecidableEq m] in
/-- **Main theorem**: The spectral norm of an outer product equals the product of vector norms.
    ‖u vᵀ‖₂ = ‖u‖ · ‖v‖

    This shows that rank-1 matrices achieve equality in spectral ≤ Frobenius. -/
theorem outerProduct_spectral_norm_eq [Nonempty m] [Nonempty n]
    (u : EuclideanSpace ℂ m) (v : EuclideanSpace ℂ n) :
    @Norm.norm _ Matrix.instL2OpNormedAddCommGroup.toNorm
      (KroneckerRearrangement.outerProduct u v) = ‖u‖ * ‖v‖ := by
  by_cases hv : v = 0
  · -- v = 0 case: outerProduct u 0 = 0, so ‖0‖ = 0 = ‖u‖·0
    subst hv
    have h_zero : KroneckerRearrangement.outerProduct u (0 : EuclideanSpace ℂ n) = 0 := by
      ext i j; simp [KroneckerRearrangement.outerProduct]
    simp only [h_zero, @norm_zero _ Matrix.instL2OpNormedAddCommGroup.toSeminormedAddCommGroup.toSeminormedAddGroup, norm_zero, mul_zero]
  · by_cases hu : u = 0
    · -- u = 0 case: outerProduct 0 v = 0, so ‖0‖ = 0 = 0·‖v‖
      subst hu
      have h_zero : KroneckerRearrangement.outerProduct (0 : EuclideanSpace ℂ m) v = 0 := by
        ext i j; simp [KroneckerRearrangement.outerProduct]
      simp only [h_zero, @norm_zero _ Matrix.instL2OpNormedAddCommGroup.toSeminormedAddCommGroup.toSeminormedAddGroup, norm_zero, zero_mul]
    · -- Both nonzero: combine upper and lower bounds
      apply le_antisymm
      · exact Matrix.Kronecker.SpectralBounds.outerProduct_spectral_norm_le u v  -- Upper: ≤ ‖u‖·‖v‖
      · exact outerProduct_spectral_norm_ge u v hv  -- Lower: ≥ ‖u‖·‖v‖

/-! ### Rank-1 Spectral = Frobenius -/

attribute [local instance] Matrix.frobeniusSeminormedAddCommGroup

omit [DecidableEq m] in
/-- For any vectors, the spectral and Frobenius norms of their outer product are equal.
    This is the general version: ‖u vᵀ‖₂ = ‖u vᵀ‖_F = ‖u‖·‖v‖ -/
theorem rank_one_spectral_eq_frobenius [Nonempty m] [Nonempty n]
    (u : EuclideanSpace ℂ m) (v : EuclideanSpace ℂ n) :
    @Norm.norm _ Matrix.instL2OpNormedAddCommGroup.toNorm
      (KroneckerRearrangement.outerProduct u v) =
    @Norm.norm _ Matrix.frobeniusSeminormedAddCommGroup.toNorm
      (KroneckerRearrangement.outerProduct u v) := by
  rw [outerProduct_spectral_norm_eq, Matrix.Kronecker.SpectralBounds.outerProduct_frobenius_norm']

/-! ### Nearly Coherent Bound

In this file's convention, μ(E) = 1/√rank(E) is the coherent extreme, where ‖E‖₂ = ‖E‖_F. The
hypothesis μ(E) ≤ 1 / ((1 - ε) · √rank(E)) says E is within a factor 1/(1 - ε) of it, and is
equivalent to (1 - ε) · ‖E‖_F ≤ ‖E‖₂ (`nearly_coherent_iff`). -/

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

omit [Nonempty n] in
/-- **Near coherence in norm form:** for E ≠ 0 and ε < 1,
    μ(E) ≤ 1 / ((1 - ε) · √rank(E)) ↔ (1 - ε) · ‖E‖_F ≤ ‖E‖₂. -/
theorem nearly_coherent_iff (E : Matrix n n ℂ) (ε : ℝ) (hE : E ≠ 0) (hε_lt_one : ε < 1) :
    coherenceFactor E ≤ 1 / ((1 - ε) * Real.sqrt E.rank) ↔
      (1 - ε) * frobeniusNorm' E ≤ ‖E‖ := by
  have h_spectral_pos : 0 < ‖E‖ := norm_pos_iff.mpr hE
  have h_rank_pos : 0 < E.rank := rank_pos_of_ne_zero E hE
  have h_sqrt_rank_pos : 0 < Real.sqrt E.rank := Real.sqrt_pos.mpr (Nat.cast_pos.mpr h_rank_pos)
  have h_one_minus_eps_pos : 0 < 1 - ε := by linarith
  -- Unfold μ(E) = ‖E‖_F / (√r · ‖E‖₂) and clear denominators
  unfold coherenceFactor
  simp only [hE, ↓reduceIte]
  rw [div_le_div_iff₀ (mul_pos h_sqrt_rank_pos h_spectral_pos)
    (mul_pos h_one_minus_eps_pos h_sqrt_rank_pos)]
  -- Goal: ‖E‖_F · ((1 - ε) · √r) ≤ 1 · (√r · ‖E‖₂) ↔ (1 - ε) · ‖E‖_F ≤ ‖E‖₂
  have h_lhs : frobeniusNorm' E * ((1 - ε) * Real.sqrt E.rank) =
      ((1 - ε) * frobeniusNorm' E) * Real.sqrt E.rank := by ring
  have h_rhs : 1 * (Real.sqrt E.rank * ‖E‖) = ‖E‖ * Real.sqrt E.rank := by ring
  rw [h_lhs, h_rhs]
  exact mul_le_mul_iff_left₀ h_sqrt_rank_pos

omit [Nonempty n] in
/-- **Nearly coherent bound:** if μ(E) ≤ 1 / ((1 - ε) · √rank(E)) with ε < 1 and E ≠ 0, then
    ‖E‖_F ≤ ‖E‖₂ / (1 - ε).

    Without the coherence hypothesis only ‖E‖_F ≤ √rank(E) · ‖E‖₂ holds
    (`coherenceFactor_le_one`). -/
theorem nearly_coherent_bound (E : Matrix n n ℂ) (ε : ℝ) (hE : E ≠ 0) (hε_lt_one : ε < 1)
    (h_coh : coherenceFactor E ≤ 1 / ((1 - ε) * Real.sqrt E.rank)) :
    frobeniusNorm' E ≤ ‖E‖ / (1 - ε) := by
  have h_one_minus_eps_pos : 0 < 1 - ε := by linarith
  have h := (nearly_coherent_iff E ε hE hε_lt_one).mp h_coh
  rw [le_div_iff₀ h_one_minus_eps_pos]
  linarith

omit [Nonempty n] in
/-- **Nearly coherent spectral lower bound:** if μ(E) ≤ 1 / ((1 - ε) · √rank(E)) with ε < 1
    and E ≠ 0, then (1 - ε) · ‖E‖_F ≤ ‖E‖₂.

    Without the coherence hypothesis only ‖E‖_F / √rank(E) ≤ ‖E‖₂ holds
    (`coherenceFactor_le_one`). -/
theorem nearly_coherent_spectral_lower_bound (E : Matrix n n ℂ) (ε : ℝ) (hE : E ≠ 0)
    (hε_lt_one : ε < 1) (h_coh : coherenceFactor E ≤ 1 / ((1 - ε) * Real.sqrt E.rank)) :
    (1 - ε) * frobeniusNorm' E ≤ ‖E‖ :=
  (nearly_coherent_iff E ε hE hε_lt_one).mp h_coh

end CoherentCase

/-! ## Incoherent Case — Improved Bounds

For incoherent matrices (flat spectrum, μ ≈ 1), the spectral norm is much smaller
than the Frobenius norm. This gives us an improvement factor of √rank over the
trivial bound.

### Key Results
* `incoherent_improved_bound`: ‖E‖ ≤ ‖E‖_F / √rank(E) (for maximally incoherent)
* `flat_spectrum_coherence_eq_one`: A flat spectrum gives μ = 1
* `effectiveRank`: Alternative characterization via entropy
* `effectiveRank_bounds`: 1 ≤ effectiveRank E ≤ rank(E)
-/

section IncoherentCase

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

omit [Nonempty n] in
/-- **Incoherent improved bound**: When coherence factor is at least α,
    we get ‖E‖ ≤ ‖E‖_F / (α · √rank). The square case of `incoherent_improved_bound_rect`.

    For maximally incoherent matrices (μ = 1), this gives ‖E‖ ≤ ‖E‖_F / √rank.
    For more coherent matrices (μ < 1), the bound is weaker.

    Note: The unconditional bound ‖E‖ ≤ ‖E‖_F / √rank is false in general. For
    E = diag(1, 0.1), rank(E) = 2 and ‖E‖ = 1 > ‖E‖_F / √2 = √(1.01 / 2). -/
theorem incoherent_improved_bound (E : Matrix n n ℂ) (hE : E ≠ 0) (α : ℝ)
    (hα_pos : 0 < α) (h_coh : α ≤ coherenceFactor E) :
    ‖E‖ ≤ frobeniusNorm' E / (α * Real.sqrt E.rank) := by
  rw [← coherenceFactorRect_eq_coherenceFactor] at h_coh
  exact incoherent_improved_bound_rect E hE α hα_pos h_coh

omit [Nonempty n] in
/-- The incoherent bound holds when coherence factor equals 1.
    If μ(E) = 1 (maximally incoherent), then ‖E‖ = ‖E‖_F / √rank(E).

    By `coherenceFactor_eq_one_iff`, μ(E) = 1 exactly when every nonzero singular value
    equals ‖E‖₂ (a flat spectrum). -/
theorem incoherent_bound_eq_of_coherence_one (E : Matrix n n ℂ) (hE : E ≠ 0)
    (h_coh : coherenceFactor E = 1) :
    ‖E‖ = frobeniusNorm' E / Real.sqrt E.rank := by
  unfold coherenceFactor at h_coh
  simp only [hE, ↓reduceIte] at h_coh
  have h_rank_pos : 0 < E.rank := rank_pos_of_ne_zero E hE
  have h_sqrt_rank_pos : 0 < Real.sqrt E.rank := Real.sqrt_pos.mpr (Nat.cast_pos.mpr h_rank_pos)
  have h_spectral_pos : 0 < ‖E‖ := norm_pos_iff.mpr hE
  have h_denom_pos : 0 < Real.sqrt E.rank * ‖E‖ := mul_pos h_sqrt_rank_pos h_spectral_pos
  -- h_coh: frobeniusNorm' E / (√r · ‖E‖) = 1
  -- Therefore: frobeniusNorm' E = √r · ‖E‖
  -- Hence: ‖E‖ = frobeniusNorm' E / √r
  have h_eq : frobeniusNorm' E = Real.sqrt E.rank * ‖E‖ := by
    rw [div_eq_one_iff_eq h_denom_pos.ne'] at h_coh
    exact h_coh
  rw [h_eq]
  field_simp

/-! ### Flat Spectrum Characterization

When all nonzero singular values are equal (flat spectrum), the coherence factor is exactly 1;
the converse is `coherenceFactor_eq_one_iff`. No stability version (nearly flat ⇒ μ near 1) is
formalized.
-/

/-- For a flat spectrum (all nonzero singular values equal), coherence = 1.
    If σ₁ = σ₂ = ... = σᵣ = c and σᵢ = 0 for i > r, then μ = 1. -/
theorem flat_spectrum_coherence_eq_one (E : Matrix n n ℂ) (hE : E ≠ 0)
    (h_flat : ∀ i j, SVD.singularValues E i ≠ 0 → SVD.singularValues E j ≠ 0 →
              SVD.singularValues E i = SVD.singularValues E j) :
    coherenceFactor E = 1 := by
  unfold coherenceFactor
  simp only [hE, ↓reduceIte]
  have h_rank_pos : 0 < E.rank := rank_pos_of_ne_zero E hE
  have h_sqrt_rank_pos : 0 < Real.sqrt E.rank := Real.sqrt_pos.mpr (Nat.cast_pos.mpr h_rank_pos)
  have h_spectral_pos : 0 < ‖E‖ := norm_pos_iff.mpr hE
  have h_denom_pos : 0 < Real.sqrt E.rank * ‖E‖ := mul_pos h_sqrt_rank_pos h_spectral_pos

  -- When all nonzero singular values are equal to some c:
  -- ‖E‖ = σ₁ = c (since some σᵢ ≠ 0)
  -- ‖E‖_F² = ∑ σᵢ² = r · c² (r nonzero terms)
  -- ‖E‖_F = c · √r
  -- μ = c · √r / (√r · c) = 1

  -- Let c = ‖E‖ (the common nonzero singular value)
  let c := ‖E‖

  -- Key: all nonzero singular values equal ‖E‖
  have h_sv_eq_norm : ∀ i, SVD.singularValues E i ≠ 0 → SVD.singularValues E i = c := by
    intro i hi
    -- ‖E‖ = max singular value
    have h_max := spectral_norm_eq_max_singularValue E
    -- The max singular value achieves ‖E‖ (by Finset.exists_mem_eq_sup')
    obtain ⟨j, _, hj_eq⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (SVD.singularValues E)
    -- hj_eq : sup' = σⱼ, and ‖E‖ = sup' (from h_max)
    have hj_val : SVD.singularValues E j = c := by
      simp only [c, h_max, maxSingularValue]
      exact hj_eq.symm
    have hj_ne : SVD.singularValues E j ≠ 0 := by rw [hj_val]; exact ne_of_gt h_spectral_pos
    -- By flatness, σᵢ = σⱼ = c
    calc SVD.singularValues E i = SVD.singularValues E j := h_flat i j hi hj_ne
      _ = c := hj_val

  -- Sum of squared singular values
  have h_frob_sq : frobeniusNorm' E ^ 2 = E.rank * c ^ 2 := by
    -- Split the sum into nonzero and zero terms
    have h_sum_eq : ∑ i, SVD.singularValues E i ^ 2 =
        ∑ i ∈ Finset.univ.filter (fun i => SVD.singularValues E i ≠ 0),
          SVD.singularValues E i ^ 2 := by
      rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
          (p := fun i => SVD.singularValues E i ≠ 0)]
      have h_zero_sum : ∑ i ∈ Finset.univ.filter (fun i => ¬SVD.singularValues E i ≠ 0),
          SVD.singularValues E i ^ 2 = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        simp only [ne_eq, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hi
        simp [hi]
      rw [h_zero_sum, add_zero]
    calc frobeniusNorm' E ^ 2
        = ∑ i, SVD.singularValues E i ^ 2 := by
          rw [frobeniusNorm'_sq, SVD.sum_sq_singularValues_eq_trace]
          simp only [trace, diag_apply, mul_apply, conjTranspose_apply]
          rw [Finset.sum_comm]
          simp [Complex.re_sum, Complex.normSq]
      _ = ∑ i ∈ Finset.univ.filter (fun i => SVD.singularValues E i ≠ 0),
            SVD.singularValues E i ^ 2 := h_sum_eq
      _ = ∑ _i ∈ Finset.univ.filter (fun i => SVD.singularValues E i ≠ 0), c ^ 2 := by
          apply Finset.sum_congr rfl
          intro i hi
          simp only [ne_eq, Finset.mem_filter, Finset.mem_univ, true_and] at hi
          rw [h_sv_eq_norm i hi]
      _ = (Finset.univ.filter (fun i => SVD.singularValues E i ≠ 0)).card * c ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = E.rank * c ^ 2 := by
          congr 1
          rw [rank_eq_card_nonzero_singularValues]
          -- The filter and the subtype have the same cardinality
          have h_card : (Finset.univ.filter (fun i => SVD.singularValues E i ≠ 0)).card =
              Fintype.card {i : n // SVD.singularValues E i ≠ 0} := by
            rw [← Finset.card_subtype]
            congr 1
            ext i
            simp
          exact_mod_cast h_card

  -- Therefore ‖E‖_F = √r · c
  have h_frob_eq : frobeniusNorm' E = Real.sqrt E.rank * c := by
    have h_frob_nonneg : 0 ≤ frobeniusNorm' E := frobeniusNorm'_nonneg E
    have h_rhs_nonneg : 0 ≤ Real.sqrt E.rank * c := mul_nonneg (Real.sqrt_nonneg _) (le_of_lt h_spectral_pos)
    rw [← Real.sqrt_sq h_frob_nonneg, ← Real.sqrt_sq h_rhs_nonneg]
    congr 1
    rw [h_frob_sq, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]

  -- Now compute μ = ‖E‖_F / (√r · c) = √r · c / (√r · c) = 1
  -- c is definitionally ‖E‖, so field_simp closes the goal
  rw [h_frob_eq]
  simp only [c]
  field_simp

/-! ### Effective Rank Definition

The effective rank captures the "true" dimensionality of a matrix based on
the entropy of its singular value distribution.
-/

/-! #### Entropy Helper Lemmas -/

/-- KL divergence is nonnegative: For positive probability distributions p on a finite set S,
    ∑_{i∈S} pᵢ log(pᵢ|S|) ≥ 0. This is equivalent to KL(P || Uniform) ≥ 0. -/
theorem kl_divergence_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (hS : S.Nonempty)
    (p : ι → ℝ) (hp_pos : ∀ i ∈ S, 0 < p i) (hp_sum : ∑ i ∈ S, p i = 1) :
    0 ≤ ∑ i ∈ S, p i * Real.log (p i * S.card) := by
  have hS_pos : (0 : ℝ) < S.card := Nat.cast_pos.mpr (Finset.card_pos.mpr hS)
  have hS_ne : (S.card : ℝ) ≠ 0 := ne_of_gt hS_pos
  have h_bound : ∀ i ∈ S, p i * Real.log (1 / (p i * S.card)) ≤ 1 / S.card - p i := by
    intro i hi
    have hp_i_pos := hp_pos i hi
    have h_arg_pos : 0 < 1 / (p i * S.card) := by positivity
    have h_ineq := Real.log_le_sub_one_of_pos h_arg_pos
    calc p i * Real.log (1 / (p i * S.card))
        ≤ p i * (1 / (p i * S.card) - 1) := mul_le_mul_of_nonneg_left h_ineq (le_of_lt hp_i_pos)
      _ = 1 / S.card - p i := by field_simp
  have h_sum_bound : ∑ i ∈ S, p i * Real.log (1 / (p i * S.card)) ≤ 0 := by
    calc ∑ i ∈ S, p i * Real.log (1 / (p i * S.card))
        ≤ ∑ i ∈ S, (1 / S.card - p i) := Finset.sum_le_sum h_bound
      _ = ∑ i ∈ S, (1 / (S.card : ℝ)) - ∑ i ∈ S, p i := by rw [← Finset.sum_sub_distrib]
      _ = S.card * (1 / S.card) - 1 := by rw [Finset.sum_const, hp_sum]; simp [nsmul_eq_mul]
      _ = 0 := by field_simp; ring
  have h_convert : ∑ i ∈ S, p i * Real.log (1 / (p i * S.card)) =
                   -∑ i ∈ S, p i * Real.log (p i * S.card) := by
    rw [← Finset.sum_neg_distrib]; congr 1; ext i; rw [one_div, Real.log_inv]; ring
  rw [h_convert] at h_sum_bound
  linarith

/-- Shannon entropy bound: For a probability distribution p with support S,
    the entropy H = ∑ negMulLog(pᵢ) ≤ log|S|. This is the maximum entropy principle. -/
theorem entropy_le_log_support {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℝ) (hp_nonneg : ∀ i, 0 ≤ p i) (hp_sum : ∑ i, p i = 1)
    (hr : 0 < (Finset.univ.filter (fun i => p i ≠ 0)).card) :
    ∑ i, Real.negMulLog (p i) ≤ Real.log (Finset.univ.filter (fun i => p i ≠ 0)).card := by
  have h_zero : ∀ i, p i = 0 → Real.negMulLog (p i) = 0 := fun i hi => by simp [Real.negMulLog, hi]
  let S := Finset.univ.filter (fun i => p i ≠ 0)
  have hS : S.Nonempty := Finset.card_pos.mp hr
  have h_sum_split : ∑ i, Real.negMulLog (p i) = ∑ i ∈ S, Real.negMulLog (p i) := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => p i ≠ 0)]
    have h_zero_sum : ∑ x ∈ Finset.filter (fun x => ¬p x ≠ 0) Finset.univ, Real.negMulLog (p x) = 0 := by
      apply Finset.sum_eq_zero; intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hi; exact h_zero i hi
    rw [h_zero_sum, add_zero]
  have hp_sum_S : ∑ i ∈ S, p i = 1 := by
    have h_comp : ∑ i ∈ Finset.filter (fun i => ¬p i ≠ 0) Finset.univ, p i = 0 := by
      apply Finset.sum_eq_zero; intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hi; exact hi
    rw [← hp_sum, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => p i ≠ 0)]
    simp only [h_comp, add_zero, S]
  have hp_pos_S : ∀ i ∈ S, 0 < p i := fun i hi => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, ne_eq, S] at hi
    exact lt_of_le_of_ne (hp_nonneg i) (Ne.symm hi)
  rw [h_sum_split]
  have hS_pos : (0 : ℝ) < S.card := Nat.cast_pos.mpr (Finset.card_pos.mpr hS)
  have h_kl := kl_divergence_nonneg S hS p hp_pos_S hp_sum_S
  have h_expand : ∑ i ∈ S, p i * Real.log (p i * S.card) =
                  ∑ i ∈ S, p i * Real.log (p i) + Real.log S.card := by
    have h_split : ∀ i ∈ S, p i * Real.log (p i * S.card) = p i * Real.log (p i) + p i * Real.log S.card := by
      intro i hi
      have hp_i_pos := hp_pos_S i hi
      have hp_i_ne : p i ≠ 0 := ne_of_gt hp_i_pos
      have hS_ne : (S.card : ℝ) ≠ 0 := ne_of_gt hS_pos
      rw [Real.log_mul hp_i_ne hS_ne]
      ring
    rw [Finset.sum_congr rfl h_split, Finset.sum_add_distrib, ← Finset.sum_mul, hp_sum_S, one_mul]
  rw [h_expand] at h_kl
  have h_negMulLog : ∀ i ∈ S, Real.negMulLog (p i) = -(p i * Real.log (p i)) := fun i _ => by
    simp only [Real.negMulLog]; ring
  calc ∑ i ∈ S, Real.negMulLog (p i)
      = ∑ i ∈ S, -(p i * Real.log (p i)) := Finset.sum_congr rfl h_negMulLog
    _ = -∑ i ∈ S, p i * Real.log (p i) := by rw [Finset.sum_neg_distrib]
    _ ≤ Real.log S.card := by linarith

/-- Normalized singular value squared: pᵢ = σᵢ² / ‖E‖_F²
    Forms a probability distribution over indices. -/
noncomputable def normalizedSingularValueSq (E : Matrix n n ℂ) (i : n) : ℝ :=
  if frobeniusNorm' E = 0 then 1 / Fintype.card n
  else (SVD.singularValues E i) ^ 2 / (frobeniusNorm' E) ^ 2

omit [Nonempty n] in
/-- The normalized singular values are nonnegative. -/
theorem normalizedSingularValueSq_nonneg (E : Matrix n n ℂ) (i : n) :
    0 ≤ normalizedSingularValueSq E i := by
  unfold normalizedSingularValueSq
  split_ifs
  · apply div_nonneg zero_le_one (Nat.cast_nonneg _)
  · apply div_nonneg (sq_nonneg _) (sq_nonneg _)

/-- The normalized singular values sum to 1 (form a probability distribution). -/
theorem normalizedSingularValueSq_sum_eq_one (E : Matrix n n ℂ) :
    ∑ i, normalizedSingularValueSq E i = 1 := by
  unfold normalizedSingularValueSq
  split_ifs with h_zero
  · -- E = 0 case: each term is 1/n, sum is n · (1/n) = 1
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  · -- E ≠ 0 case: ∑ σᵢ²/‖E‖_F² = (∑ σᵢ²) / ‖E‖_F² = ‖E‖_F² / ‖E‖_F² = 1
    have h_frob_pos : 0 < frobeniusNorm' E := by
      have h_nonneg := frobeniusNorm'_nonneg E
      rcases h_nonneg.lt_or_eq with h_lt | h_eq
      · exact h_lt
      · exfalso; exact h_zero h_eq.symm
    rw [← Finset.sum_div]
    have h_sum : ∑ i, SVD.singularValues E i ^ 2 = frobeniusNorm' E ^ 2 := by
      rw [frobeniusNorm'_sq, SVD.sum_sq_singularValues_eq_trace]
      simp only [trace, diag_apply, mul_apply, conjTranspose_apply]
      rw [Finset.sum_comm]
      simp [Complex.re_sum, Complex.normSq]
    rw [h_sum]
    field_simp

/-- Effective rank via entropy: erank(E) = exp(-∑ᵢ pᵢ log pᵢ)
    where pᵢ = σᵢ²/‖E‖_F² is the normalized singular value distribution.

    Properties:
    - erank(E) = 1 for rank-1 matrices (maximally coherent)
    - erank(E) = rank(E) for flat spectrum (maximally incoherent)
    - 1 ≤ erank(E) ≤ rank(E) for E ≠ 0 (`effectiveRank_ge_one`, `effectiveRank_le_rank`);
      for E = 0 the distribution is uniform and erank(0) = card n -/
noncomputable def effectiveRank (E : Matrix n n ℂ) : ℝ :=
  Real.exp (- ∑ i, normalizedSingularValueSq E i *
    if normalizedSingularValueSq E i = 0 then 0
    else Real.log (normalizedSingularValueSq E i))

/-- The effective rank is at least 1.
    Proof: Since pᵢ ∈ [0,1] and log pᵢ ≤ 0 for pᵢ ≤ 1, we have pᵢ log pᵢ ≤ 0.
    Therefore ∑ pᵢ log pᵢ ≤ 0, so -∑ pᵢ log pᵢ ≥ 0.
    Hence erank = exp(-∑ pᵢ log pᵢ) ≥ exp(0) = 1. -/
theorem effectiveRank_ge_one (E : Matrix n n ℂ) : 1 ≤ effectiveRank E := by
  unfold effectiveRank
  rw [← Real.exp_zero]
  apply Real.exp_le_exp_of_le
  -- Need: 0 ≤ -∑ pᵢ log pᵢ, i.e., ∑ pᵢ log pᵢ ≤ 0
  apply neg_nonneg.mpr
  apply Finset.sum_nonpos
  intro i _
  split_ifs with hp
  · -- p = 0 case: 0 * 0 = 0 ≤ 0
    simp [hp]
  · -- p > 0 case: p · log p ≤ 0 since p ∈ (0, 1] and log p ≤ 0
    have hp_pos : 0 < normalizedSingularValueSq E i := by
      unfold normalizedSingularValueSq at hp ⊢
      split_ifs with h_zero
      · -- 1/n > 0 always
        apply one_div_pos.mpr
        exact Nat.cast_pos.mpr Fintype.card_pos
      · -- σᵢ²/‖E‖_F² > 0 when σᵢ ≠ 0
        push_neg at hp
        have h_frob_pos : 0 < frobeniusNorm' E := by
          have h_nonneg := frobeniusNorm'_nonneg E
          rcases h_nonneg.lt_or_eq with h_lt | h_eq
          · exact h_lt
          · exfalso; exact h_zero h_eq.symm
        have h_sv_pos : 0 < SVD.singularValues E i := by
          have h_nonneg := SVD.singularValues_nonneg E i
          rcases h_nonneg.lt_or_eq with h_lt | h_eq
          · exact h_lt
          · exfalso
            apply hp
            simp only [if_neg h_zero]
            rw [← h_eq]
            simp
        exact div_pos (sq_pos_of_pos h_sv_pos) (sq_pos_of_pos h_frob_pos)
    have hp_le_one : normalizedSingularValueSq E i ≤ 1 := by
      have h_sum := normalizedSingularValueSq_sum_eq_one E
      calc normalizedSingularValueSq E i
          ≤ ∑ j, normalizedSingularValueSq E j := Finset.single_le_sum
            (fun j _ => by
              unfold normalizedSingularValueSq
              split_ifs
              · apply div_nonneg zero_le_one (Nat.cast_nonneg _)
              · apply div_nonneg (sq_nonneg _) (sq_nonneg _))
            (Finset.mem_univ i)
        _ = 1 := h_sum
    -- p ∈ (0, 1], so log p ≤ 0
    have h_log_nonpos : Real.log (normalizedSingularValueSq E i) ≤ 0 :=
      Real.log_nonpos (le_of_lt hp_pos) hp_le_one
    exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt hp_pos) h_log_nonpos

/-- The effective rank is at most the matrix rank.
    This follows from the maximum entropy principle: entropy is maximized
    when the distribution is uniform over the support, giving H = log(rank).
    Therefore erank = exp(H) ≤ exp(log(rank)) = rank. -/
theorem effectiveRank_le_rank (E : Matrix n n ℂ) (hE : E ≠ 0) :
    effectiveRank E ≤ E.rank := by
  unfold effectiveRank
  -- Step 1: Rewrite the entropy sum using negMulLog
  have h_entropy_eq : - ∑ i, normalizedSingularValueSq E i *
      (if normalizedSingularValueSq E i = 0 then (0 : ℝ)
       else Real.log (normalizedSingularValueSq E i))
      = ∑ i, Real.negMulLog (normalizedSingularValueSq E i) := by
    simp only [Real.negMulLog]
    rw [← Finset.sum_neg_distrib]
    congr 1; ext i
    split_ifs with h
    · simp [h]
    · ring

  rw [h_entropy_eq]

  -- Step 2: The p_i form a probability distribution
  have hp_nonneg : ∀ i, 0 ≤ normalizedSingularValueSq E i := normalizedSingularValueSq_nonneg E
  have hp_sum : ∑ i, normalizedSingularValueSq E i = 1 := normalizedSingularValueSq_sum_eq_one E

  -- Step 3: The support of p equals the set of nonzero singular values
  have h_frob_ne : frobeniusNorm' E ≠ 0 := by
    intro h_eq
    apply hE
    ext i j
    have h_frob_sq : frobeniusNorm' E ^ 2 = 0 := by rw [h_eq]; ring
    rw [frobeniusNorm'_sq] at h_frob_sq
    have h_nonneg : 0 ≤ ∑ i', ∑ j', Complex.normSq (E i' j') :=
      Finset.sum_nonneg (fun i' _ => Finset.sum_nonneg (fun j' _ => Complex.normSq_nonneg _))
    have h_le : ∑ i', ∑ j', Complex.normSq (E i' j') ≤ 0 := le_of_eq h_frob_sq
    have h_zero : ∑ i', ∑ j', Complex.normSq (E i' j') = 0 := le_antisymm h_le h_nonneg
    have h_row_zero : ∀ i', ∑ j', Complex.normSq (E i' j') = 0 := fun i' => by
      have h1 := (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ)
        (fun i'' _ => Finset.sum_nonneg (fun j' _ => Complex.normSq_nonneg _))).mp h_zero i' (Finset.mem_univ _)
      exact h1
    have h_entry_zero := (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ)
        (fun j' _ => Complex.normSq_nonneg _)).mp (h_row_zero i) j (Finset.mem_univ _)
    exact Complex.normSq_eq_zero.mp h_entry_zero

  have h_support_eq : (Finset.univ.filter (fun i => normalizedSingularValueSq E i ≠ 0)) =
                      (Finset.univ.filter (fun i => SVD.singularValues E i ≠ 0)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    unfold normalizedSingularValueSq
    simp only [h_frob_ne, ↓reduceIte]
    have h_frob_sq_pos : 0 < frobeniusNorm' E ^ 2 := by
      have := frobeniusNorm'_nonneg E
      exact sq_pos_of_pos (lt_of_le_of_ne this (ne_comm.mp h_frob_ne))
    constructor
    · intro h_ne
      rw [div_ne_zero_iff] at h_ne
      have ⟨h_num, _⟩ := h_ne
      have h_sq_ne : SVD.singularValues E i ^ 2 ≠ 0 := h_num
      -- σ² ≠ 0 → σ ≠ 0
      intro h_sv_zero
      exact h_sq_ne (by rw [h_sv_zero]; ring)
    · intro h
      rw [div_ne_zero_iff]
      exact ⟨pow_ne_zero 2 h, ne_of_gt h_frob_sq_pos⟩

  -- Step 4: The support size equals rank
  have h_rank_eq : E.rank = (Finset.univ.filter (fun i => SVD.singularValues E i ≠ 0)).card := by
    rw [rank_eq_card_nonzero_singularValues]
    -- Fintype.card {i // P i} = (Finset.univ.filter P).card is Fintype.card_subtype
    exact Fintype.card_subtype _

  -- Step 5: rank > 0 since E ≠ 0
  have h_rank_pos : 0 < E.rank := rank_pos_of_ne_zero E hE

  have h_support_pos : 0 < (Finset.univ.filter (fun i => normalizedSingularValueSq E i ≠ 0)).card := by
    rw [h_support_eq, ← h_rank_eq]
    exact h_rank_pos

  -- Step 6: Apply entropy bound
  have h_entropy_bound := entropy_le_log_support (normalizedSingularValueSq E) hp_nonneg hp_sum h_support_pos

  -- Step 7: exp(H) ≤ exp(log r) = r
  rw [h_support_eq] at h_entropy_bound
  calc Real.exp (∑ i, Real.negMulLog (normalizedSingularValueSq E i))
      ≤ Real.exp (Real.log (Finset.univ.filter (fun i => SVD.singularValues E i ≠ 0)).card) :=
        Real.exp_le_exp_of_le h_entropy_bound
    _ = (Finset.univ.filter (fun i => SVD.singularValues E i ≠ 0)).card := by
        apply Real.exp_log
        exact Nat.cast_pos.mpr (by rw [← h_rank_eq]; exact h_rank_pos)
    _ = E.rank := by rw [← h_rank_eq]

/-- Combined bounds for effective rank. -/
theorem effectiveRank_bounds (E : Matrix n n ℂ) (hE : E ≠ 0) :
    1 ≤ effectiveRank E ∧ effectiveRank E ≤ E.rank :=
  ⟨effectiveRank_ge_one E, effectiveRank_le_rank E hE⟩

/-- Effective rank equals 1 for rank-1 matrices (maximally coherent).
    A rank-1 matrix has one nonzero singular value σ₁, so p₁ = 1 and pᵢ = 0 for i > 1.
    Entropy H = -1·log(1) = 0, so erank = exp(0) = 1. -/
theorem effectiveRank_eq_one_of_rank_one (E : Matrix n n ℂ)
    (h_rank : E.rank = 1) :
    effectiveRank E = 1 := by
  unfold effectiveRank
  -- The goal is: exp(-∑ pᵢ * if pᵢ = 0 then 0 else log pᵢ) = 1
  -- Equivalently: ∑ pᵢ * if pᵢ = 0 then 0 else log pᵢ = 0

  -- Step 1: E ≠ 0 since rank > 0
  have hE_ne : E ≠ 0 := by
    intro h_eq
    rw [h_eq, rank_zero] at h_rank
    exact Nat.zero_ne_one h_rank

  -- Step 2: Get that frobeniusNorm' E ≠ 0
  have h_frob_ne : frobeniusNorm' E ≠ 0 := by
    intro h_eq
    have h_frob_sq := frobeniusNorm'_sq E
    rw [h_eq, sq, mul_zero] at h_frob_sq
    -- h_frob_sq : 0 = ∑ i, ∑ j, Complex.normSq (E i j)
    have h_sum_zero : ∑ i, ∑ j, Complex.normSq (E i j) = 0 := h_frob_sq.symm
    have h_all_zero : ∀ i j, E i j = 0 := by
      intro i j
      have h_inner_nonneg : ∀ k l, 0 ≤ Complex.normSq (E k l) := fun k l => Complex.normSq_nonneg _
      have h_outer_nonneg : ∀ k, 0 ≤ ∑ l, Complex.normSq (E k l) :=
        fun k => Finset.sum_nonneg (fun l _ => h_inner_nonneg k l)
      have h_outer_zero : ∀ k, ∑ l, Complex.normSq (E k l) = 0 := by
        have h_lem := Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ) (fun k _ => h_outer_nonneg k)
        simp only [Finset.mem_univ, true_implies] at h_lem
        exact h_lem.mp h_sum_zero
      have h_inner_eq_zero := Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ) (fun l _ => h_inner_nonneg i l)
      simp only [Finset.mem_univ, true_implies] at h_inner_eq_zero
      have := h_inner_eq_zero.mp (h_outer_zero i) j
      exact Complex.normSq_eq_zero.mp this
    exact hE_ne (Matrix.ext h_all_zero)

  -- Step 3: rank = 1 means exactly one nonzero singular value
  have h_card_one : Fintype.card {i : n // SVD.singularValues E i ≠ 0} = 1 := by
    rw [← rank_eq_card_nonzero_singularValues E, h_rank]

  -- Step 4: Get the unique nonzero index
  haveI : Nonempty {i : n // SVD.singularValues E i ≠ 0} := by
    rw [← Fintype.card_pos_iff, h_card_one]
    exact Nat.one_pos
  haveI h_unique_inst : Unique {i : n // SVD.singularValues E i ≠ 0} :=
    Fintype.card_eq_one_iff_nonempty_unique.mp h_card_one |>.some
  set i₀ := (default : {i : n // SVD.singularValues E i ≠ 0}).val with h_i0_def
  have hi₀ : SVD.singularValues E i₀ ≠ 0 := (default : {i : n // SVD.singularValues E i ≠ 0}).property
  have h_unique : ∀ (a : {i : n // SVD.singularValues E i ≠ 0}), a = default := Unique.eq_default

  -- Step 5: For i ≠ i₀, singularValues E i = 0, hence pᵢ = 0
  have h_sv_zero : ∀ i, i ≠ i₀ → SVD.singularValues E i = 0 := by
    intro i hi
    by_contra h_ne
    have h_mem : (⟨i, h_ne⟩ : {j // SVD.singularValues E j ≠ 0}) = default := h_unique ⟨i, h_ne⟩
    have : i = i₀ := congrArg Subtype.val h_mem
    exact hi this

  -- Step 6: Since ∑ pᵢ = 1 and all pⱼ = 0 for j ≠ i₀, we have p_{i₀} = 1
  have h_p_i0 : normalizedSingularValueSq E i₀ = 1 := by
    have h_sum := normalizedSingularValueSq_sum_eq_one E
    have h_other_zero : ∀ j, j ≠ i₀ → normalizedSingularValueSq E j = 0 := by
      intro j hj
      show normalizedSingularValueSq E j = 0
      simp only [normalizedSingularValueSq, if_neg h_frob_ne]
      rw [h_sv_zero j hj, sq, mul_zero, zero_div]
    have h_split := Fintype.sum_eq_single i₀ h_other_zero
    rw [h_split] at h_sum
    exact h_sum

  -- Step 7: For j ≠ i₀, pⱼ = 0
  have h_p_zero : ∀ j, j ≠ i₀ → normalizedSingularValueSq E j = 0 := by
    intro j hj
    simp only [normalizedSingularValueSq, if_neg h_frob_ne]
    rw [h_sv_zero j hj, sq, mul_zero, zero_div]

  -- Step 8: The entropy sum equals 0
  have h_entropy_zero : ∑ i, normalizedSingularValueSq E i *
      (if normalizedSingularValueSq E i = 0 then 0
       else Real.log (normalizedSingularValueSq E i)) = 0 := by
    rw [Fintype.sum_eq_single i₀]
    · -- The i₀ term: p_{i₀} = 1, so 1 * log 1 = 0
      simp only [h_p_i0, one_ne_zero, ↓reduceIte, Real.log_one, mul_zero]
    · -- All other terms: pⱼ = 0
      intro j hj
      rw [h_p_zero j hj]
      simp only [↓reduceIte, mul_zero]

  -- Step 9: exp(0) = 1
  rw [h_entropy_zero, neg_zero, Real.exp_zero]

omit [Nonempty n] in
/-- Effective rank equals rank for flat spectrum (maximally incoherent).
    When all nonzero singular values are equal, pᵢ = 1/r for i ∈ support.
    Entropy H = -r·(1/r)·log(1/r) = log(r), so erank = exp(log r) = r. -/
theorem effectiveRank_eq_rank_of_flat_spectrum (E : Matrix n n ℂ) (hE : E ≠ 0)
    (h_flat : ∀ i j, SVD.singularValues E i ≠ 0 → SVD.singularValues E j ≠ 0 →
              SVD.singularValues E i = SVD.singularValues E j) :
    effectiveRank E = E.rank := by
  unfold effectiveRank

  -- Step 1: Basic setup
  have h_rank_pos : 0 < E.rank := rank_pos_of_ne_zero E hE

  have h_frob_ne : frobeniusNorm' E ≠ 0 := by
    intro h_eq
    have h_frob_sq := frobeniusNorm'_sq E
    rw [h_eq, sq, mul_zero] at h_frob_sq
    have h_sum_zero : ∑ i, ∑ j, Complex.normSq (E i j) = 0 := h_frob_sq.symm
    have h_all_zero : ∀ i j, E i j = 0 := by
      intro i j
      have h_inner_nonneg : ∀ k l, 0 ≤ Complex.normSq (E k l) := fun k l => Complex.normSq_nonneg _
      have h_outer_nonneg : ∀ k, 0 ≤ ∑ l, Complex.normSq (E k l) :=
        fun k => Finset.sum_nonneg (fun l _ => h_inner_nonneg k l)
      have h_outer_zero : ∀ k, ∑ l, Complex.normSq (E k l) = 0 := by
        have h_lem := Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ) (fun k _ => h_outer_nonneg k)
        simp only [Finset.mem_univ, true_implies] at h_lem
        exact h_lem.mp h_sum_zero
      have h_inner_eq_zero := Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ) (fun l _ => h_inner_nonneg i l)
      simp only [Finset.mem_univ, true_implies] at h_inner_eq_zero
      have := h_inner_eq_zero.mp (h_outer_zero i) j
      exact Complex.normSq_eq_zero.mp this
    exact hE (Matrix.ext h_all_zero)

  -- Step 2: Let S = support = {i : σᵢ ≠ 0}
  let S := Finset.univ.filter (fun i => SVD.singularValues E i ≠ 0)
  have h_S_card_eq_rank : S.card = E.rank := by
    rw [rank_eq_card_nonzero_singularValues]
    exact (Fintype.card_subtype _).symm

  have h_S_card_pos : 0 < S.card := by
    rw [h_S_card_eq_rank]
    exact h_rank_pos

  -- Step 3: For i ∈ S, σᵢ² = c² for some common value c > 0
  -- Since all nonzero singular values are equal, ∑_{i ∈ S} σᵢ² = |S| · c²
  -- So pᵢ = c²/(|S|·c²) = 1/|S| for i ∈ S
  have h_frob_sq_eq : frobeniusNorm' E ^ 2 = ∑ i, SVD.singularValues E i ^ 2 := by
    rw [frobeniusNorm'_sq, SVD.sum_sq_singularValues_eq_trace]
    simp only [trace, diag_apply, mul_apply, conjTranspose_apply]
    rw [Finset.sum_comm]
    simp [Complex.re_sum, Complex.normSq]

  -- Get a nonzero singular value
  have h_exists_nonzero : ∃ i₀, SVD.singularValues E i₀ ≠ 0 := by
    by_contra h_all_zero
    push_neg at h_all_zero
    have h_card_zero : Fintype.card {i : n // SVD.singularValues E i ≠ 0} = 0 := by
      simp only [Fintype.card_eq_zero_iff, isEmpty_subtype, not_not]
      exact h_all_zero
    rw [← rank_eq_card_nonzero_singularValues] at h_card_zero
    omega

  obtain ⟨i₀, hi₀⟩ := h_exists_nonzero
  set σ₀ := SVD.singularValues E i₀ with h_σ₀_def

  -- All nonzero singular values equal σ₀
  have h_sv_eq : ∀ i, SVD.singularValues E i ≠ 0 → SVD.singularValues E i = σ₀ := by
    intro i hi
    exact h_flat i i₀ hi hi₀

  -- Helper: i ∈ S ↔ singularValues E i ≠ 0
  have h_mem_S : ∀ i, i ∈ S ↔ SVD.singularValues E i ≠ 0 := fun i =>
    Finset.mem_filter.trans ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

  -- Step 4: Compute pᵢ for i ∈ S: pᵢ = σ₀²/‖E‖_F² = σ₀²/(|S|·σ₀²) = 1/|S|
  have h_frob_sq_eq_S : frobeniusNorm' E ^ 2 = S.card * σ₀ ^ 2 := by
    calc frobeniusNorm' E ^ 2
        = ∑ i, SVD.singularValues E i ^ 2 := h_frob_sq_eq
      _ = ∑ i ∈ S, SVD.singularValues E i ^ 2 +
          ∑ i ∈ Finset.univ \ S, SVD.singularValues E i ^ 2 := by
          conv_lhs => rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ S)]
          congr 1
          · exact Finset.sum_congr (by ext; simp) (fun _ _ => rfl)
          · exact Finset.sum_congr (by ext; simp [Finset.mem_sdiff]) (fun _ _ => rfl)
      _ = ∑ i ∈ S, SVD.singularValues E i ^ 2 := by
          have h_compl_zero : ∑ i ∈ Finset.univ \ S, SVD.singularValues E i ^ 2 = 0 := by
            apply Finset.sum_eq_zero
            intro i hi
            simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hi
            have h_eq : SVD.singularValues E i = 0 := by
              by_contra h_ne
              exact hi ((h_mem_S i).mpr h_ne)
            rw [h_eq, sq, mul_zero]
          rw [h_compl_zero, add_zero]
      _ = ∑ _i ∈ S, σ₀ ^ 2 := by
          apply Finset.sum_congr rfl
          intro i hi
          have h_ne := (h_mem_S i).mp hi
          rw [h_sv_eq i h_ne]
      _ = S.card * σ₀ ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]

  have h_σ₀_pos : 0 < σ₀ := by
    have h_nonneg := SVD.singularValues_nonneg E i₀
    rcases h_nonneg.lt_or_eq with h_lt | h_eq
    · exact h_lt
    · exact absurd h_eq.symm hi₀

  have h_σ₀_sq_ne : σ₀ ^ 2 ≠ 0 := by
    intro h_eq
    have := sq_eq_zero_iff.mp h_eq
    exact hi₀ this

  -- For i ∈ S: pᵢ = σ₀²/(|S|·σ₀²) = 1/|S|
  have h_p_in_S : ∀ i ∈ S, normalizedSingularValueSq E i = 1 / S.card := by
    intro i hi
    have h_ne := (h_mem_S i).mp hi
    simp only [normalizedSingularValueSq, if_neg h_frob_ne]
    rw [h_sv_eq i h_ne, h_frob_sq_eq_S]
    field_simp

  -- For i ∉ S: pᵢ = 0
  have h_p_not_in_S : ∀ i ∉ S, normalizedSingularValueSq E i = 0 := by
    intro i hi
    have h_eq : SVD.singularValues E i = 0 := by
      by_contra h_ne
      exact hi ((h_mem_S i).mpr h_ne)
    simp only [normalizedSingularValueSq, if_neg h_frob_ne]
    rw [h_eq, sq, mul_zero, zero_div]

  -- Step 5: Compute entropy H = -∑ pᵢ·log(pᵢ) = -|S|·(1/|S|)·log(1/|S|) = log(|S|)
  have h_entropy : ∑ i, normalizedSingularValueSq E i *
      (if normalizedSingularValueSq E i = 0 then 0
       else Real.log (normalizedSingularValueSq E i)) =
      - Real.log S.card := by
    -- Split sum over S and Sᶜ
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => i ∈ S)]
    -- The Sᶜ sum is 0
    have h_compl_zero : ∑ i ∈ Finset.univ.filter (fun i => i ∉ S),
        normalizedSingularValueSq E i *
        (if normalizedSingularValueSq E i = 0 then 0
         else Real.log (normalizedSingularValueSq E i)) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      rw [h_p_not_in_S i hi]
      simp only [↓reduceIte, mul_zero]
    rw [h_compl_zero, add_zero]
    -- Simplify filter to S
    have h_filter_eq : Finset.univ.filter (fun i => i ∈ S) = S := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [h_filter_eq]
    -- Each term in S: (1/|S|) · log(1/|S|)
    have h_each_term : ∀ i ∈ S, normalizedSingularValueSq E i *
        (if normalizedSingularValueSq E i = 0 then 0
         else Real.log (normalizedSingularValueSq E i)) =
        (1 / S.card) * Real.log (1 / S.card) := by
      intro i hi
      rw [h_p_in_S i hi]
      have h_S_pos : (0 : ℝ) < S.card := Nat.cast_pos.mpr h_S_card_pos
      have h_one_div_ne : (1 : ℝ) / S.card ≠ 0 := one_div_ne_zero (ne_of_gt h_S_pos)
      simp only [h_one_div_ne, ↓reduceIte]
    rw [Finset.sum_congr rfl h_each_term, Finset.sum_const, nsmul_eq_mul]
    -- |S| · (1/|S|) · log(1/|S|) = log(1/|S|) = -log(|S|)
    have h_S_pos : (0 : ℝ) < S.card := Nat.cast_pos.mpr h_S_card_pos
    field_simp
    rw [one_div, Real.log_inv]

  -- Step 6: exp(-H) = exp(log(|S|)) = |S| = rank
  rw [h_entropy, neg_neg, Real.exp_log (Nat.cast_pos.mpr h_S_card_pos), h_S_card_eq_rank]

/-! ### Connection to Coherence Factor

The coherence factor and the effective rank both measure how spread out the singular values
are. With pᵢ = σᵢ² / ‖E‖_F², the stable rank ‖E‖_F² / ‖E‖₂² = 1 / maxᵢ pᵢ is exp of the
min-entropy of p, and `effectiveRank` is exp of its Shannon entropy, so the stable rank is at
most the effective rank (`stableRank_le_effectiveRank`). Since μ² · rank equals the stable rank
(`coherenceFactor_sq_mul_rank_eq`), μ(E)² · rank(E) ≤ effectiveRank E.
-/

omit [Nonempty n] in
/-- **Coherence and stable rank:** μ(E)² · rank(E) = (‖E‖_F / ‖E‖₂)², the stable rank of E,
    for E ≠ 0. -/
theorem coherenceFactor_sq_mul_rank_eq (E : Matrix n n ℂ) (hE : E ≠ 0) :
    coherenceFactor E ^ 2 * E.rank =
    (frobeniusNorm' E / ‖E‖) ^ 2 := by
  unfold coherenceFactor
  simp only [hE, ↓reduceIte]
  have h_spectral_pos : 0 < ‖E‖ := norm_pos_iff.mpr hE
  have h_rank_pos : 0 < E.rank := rank_pos_of_ne_zero E hE
  have h_sqrt_rank_pos : 0 < Real.sqrt E.rank := Real.sqrt_pos.mpr (Nat.cast_pos.mpr h_rank_pos)
  have h_rank_nonneg : (0 : ℝ) ≤ E.rank := Nat.cast_nonneg _
  -- μ = ‖E‖_F / (√r · ‖E‖)
  -- μ² · r = (‖E‖_F / (√r · ‖E‖))² · r = ‖E‖_F² / (r · ‖E‖²) · r = ‖E‖_F² / ‖E‖²
  rw [div_pow, div_pow, mul_pow, Real.sq_sqrt h_rank_nonneg]
  field_simp

/-- **Stable rank is at most effective rank:** (‖E‖_F / ‖E‖₂)² ≤ effectiveRank E for E ≠ 0.

    With pᵢ = σᵢ² / ‖E‖_F², every pᵢ ≤ ‖E‖₂² / ‖E‖_F², so the entropy -Σ pᵢ log pᵢ is at least
    -log(‖E‖₂² / ‖E‖_F²). -/
theorem stableRank_le_effectiveRank (E : Matrix n n ℂ) (hE : E ≠ 0) :
    (frobeniusNorm' E / ‖E‖) ^ 2 ≤ effectiveRank E := by
  have h_spec_pos : 0 < ‖E‖ := norm_pos_iff.mpr hE
  have h_frob_pos : 0 < frobeniusNorm' E :=
    lt_of_lt_of_le h_spec_pos (spectral_norm_le_frobenius_norm E)
  have h_pmax_pos : 0 < ‖E‖ ^ 2 / frobeniusNorm' E ^ 2 :=
    div_pos (pow_pos h_spec_pos 2) (pow_pos h_frob_pos 2)
  -- Each σᵢ is at most the largest singular value ‖E‖₂
  have h_sv_le : ∀ i, SVD.singularValues E i ≤ ‖E‖ := by
    intro i
    rw [spectral_norm_eq_max_singularValue]
    exact Finset.le_sup' _ (Finset.mem_univ i)
  -- So every pᵢ is at most pmax = ‖E‖₂² / ‖E‖_F²
  have h_p_le : ∀ i, normalizedSingularValueSq E i ≤ ‖E‖ ^ 2 / frobeniusNorm' E ^ 2 := by
    intro i
    unfold normalizedSingularValueSq
    rw [if_neg h_frob_pos.ne']
    exact div_le_div_of_nonneg_right
      (pow_le_pow_left₀ (SVD.singularValues_nonneg E i) (h_sv_le i) 2) (sq_nonneg _)
  -- Termwise, pᵢ log pᵢ ≤ pᵢ log pmax (both sides vanish when pᵢ = 0)
  have h_term : ∀ i, normalizedSingularValueSq E i *
      (if normalizedSingularValueSq E i = 0 then 0
        else Real.log (normalizedSingularValueSq E i)) ≤
      normalizedSingularValueSq E i * Real.log (‖E‖ ^ 2 / frobeniusNorm' E ^ 2) := by
    intro i
    by_cases hp : normalizedSingularValueSq E i = 0
    · rw [hp, zero_mul, zero_mul]
    · rw [if_neg hp]
      have hp_pos : 0 < normalizedSingularValueSq E i :=
        lt_of_le_of_ne (normalizedSingularValueSq_nonneg E i) (Ne.symm hp)
      exact mul_le_mul_of_nonneg_left (Real.log_le_log hp_pos (h_p_le i)) hp_pos.le
  -- Summing, the entropy is at least -log pmax
  have h_entropy : -Real.log (‖E‖ ^ 2 / frobeniusNorm' E ^ 2) ≤
      -∑ i, normalizedSingularValueSq E i *
        (if normalizedSingularValueSq E i = 0 then 0
          else Real.log (normalizedSingularValueSq E i)) := by
    rw [neg_le_neg_iff]
    calc ∑ i, normalizedSingularValueSq E i *
          (if normalizedSingularValueSq E i = 0 then 0
            else Real.log (normalizedSingularValueSq E i))
        ≤ ∑ i, normalizedSingularValueSq E i * Real.log (‖E‖ ^ 2 / frobeniusNorm' E ^ 2) :=
          Finset.sum_le_sum (fun i _ => h_term i)
      _ = Real.log (‖E‖ ^ 2 / frobeniusNorm' E ^ 2) := by
          rw [← Finset.sum_mul, normalizedSingularValueSq_sum_eq_one E, one_mul]
  -- exp(-log pmax) = 1 / pmax = (‖E‖_F / ‖E‖₂)²
  have h_lhs : (frobeniusNorm' E / ‖E‖) ^ 2 =
      Real.exp (-Real.log (‖E‖ ^ 2 / frobeniusNorm' E ^ 2)) := by
    rw [Real.exp_neg, Real.exp_log h_pmax_pos, inv_div, div_pow]
  rw [h_lhs]
  unfold effectiveRank
  exact Real.exp_le_exp.mpr h_entropy

/-- **Coherence bounds effective rank:** μ(E)² · rank(E) ≤ effectiveRank E for E ≠ 0. -/
theorem coherenceFactor_sq_mul_rank_le_effectiveRank (E : Matrix n n ℂ) (hE : E ≠ 0) :
    coherenceFactor E ^ 2 * E.rank ≤ effectiveRank E := by
  rw [coherenceFactor_sq_mul_rank_eq E hE]
  exact stableRank_le_effectiveRank E hE

/-! ### Equality cases

μ(E) = 1 exactly for flat spectra, and ‖E‖₂ = ‖E‖_F exactly for rank ≤ 1. Both follow from
‖E‖_F² = Σᵢ σᵢ² over the r = rank(E) nonzero singular values, each at most ‖E‖₂.
-/

/-- Every singular value is at most the spectral norm. -/
theorem singularValues_le_norm (E : Matrix n n ℂ) (i : n) : SVD.singularValues E i ≤ ‖E‖ := by
  rw [spectral_norm_eq_max_singularValue]
  exact Finset.le_sup' _ (Finset.mem_univ i)

omit [Nonempty n] in
/-- ‖E‖_F² is the sum of the squared nonzero singular values. -/
theorem frobeniusNorm'_sq_eq_sum_nonzero (E : Matrix n n ℂ) :
    frobeniusNorm' E ^ 2 = ∑ i ∈ Finset.univ.filter (fun i => SVD.singularValues E i ≠ 0),
      SVD.singularValues E i ^ 2 := by
  have h_all : frobeniusNorm' E ^ 2 = ∑ i, SVD.singularValues E i ^ 2 := by
    rw [frobeniusNorm'_sq, SVD.sum_sq_singularValues_eq_trace]
    simp only [trace, diag_apply, mul_apply, conjTranspose_apply]
    rw [Finset.sum_comm]
    simp [Complex.re_sum, Complex.normSq]
  rw [h_all, ← Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
    (p := fun i => SVD.singularValues E i ≠ 0)]
  have h_zero : ∑ i ∈ Finset.univ.filter (fun i => ¬SVD.singularValues E i ≠ 0),
      SVD.singularValues E i ^ 2 = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp only [ne_eq, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hi
    simp [hi]
  rw [h_zero, add_zero]

omit [Nonempty n] in
/-- The number of nonzero singular values, as a `Finset` filter, is the rank. -/
theorem card_filter_singularValues_ne_zero (E : Matrix n n ℂ) :
    (Finset.univ.filter (fun i => SVD.singularValues E i ≠ 0)).card = E.rank := by
  rw [rank_eq_card_nonzero_singularValues, ← Finset.card_subtype]
  congr 1
  ext i
  simp

/-- **Coherence factor one iff flat spectrum:** for E ≠ 0, μ(E) = 1 exactly when every nonzero
    singular value equals ‖E‖₂. The `←` direction is `flat_spectrum_coherence_eq_one`. -/
theorem coherenceFactor_eq_one_iff (E : Matrix n n ℂ) (hE : E ≠ 0) :
    coherenceFactor E = 1 ↔
      ∀ i, SVD.singularValues E i ≠ 0 → SVD.singularValues E i = ‖E‖ := by
  have h_spec_pos : 0 < ‖E‖ := norm_pos_iff.mpr hE
  constructor
  · intro h_coh i hi
    -- μ = 1 gives ‖E‖_F² = rank(E) · ‖E‖²
    have h_key : frobeniusNorm' E ^ 2 = E.rank * ‖E‖ ^ 2 := by
      have h := coherenceFactor_sq_mul_rank_eq E hE
      rw [h_coh, one_pow, one_mul, div_pow, eq_div_iff (pow_ne_zero 2 h_spec_pos.ne')] at h
      exact h.symm
    -- Over the nonzero singular values, the nonnegative terms ‖E‖² - σⱼ² sum to 0
    have h_nonneg : ∀ j ∈ Finset.univ.filter (fun i => SVD.singularValues E i ≠ 0),
        0 ≤ ‖E‖ ^ 2 - SVD.singularValues E j ^ 2 := fun j _ =>
      sub_nonneg.mpr (pow_le_pow_left₀ (SVD.singularValues_nonneg E j)
        (singularValues_le_norm E j) 2)
    have h_sum : ∑ j ∈ Finset.univ.filter (fun i => SVD.singularValues E i ≠ 0),
        (‖E‖ ^ 2 - SVD.singularValues E j ^ 2) = 0 := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
        ← frobeniusNorm'_sq_eq_sum_nonzero, h_key, card_filter_singularValues_ne_zero]
      ring
    have h_term := (Finset.sum_eq_zero_iff_of_nonneg h_nonneg).mp h_sum i
      (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)
    have h_sq : SVD.singularValues E i ^ 2 = ‖E‖ ^ 2 := by linarith
    exact (sq_eq_sq₀ (SVD.singularValues_nonneg E i) h_spec_pos.le).mp h_sq
  · intro h_flat
    apply flat_spectrum_coherence_eq_one E hE
    intro i j hi hj
    rw [h_flat i hi, h_flat j hj]

/-- **Spectral equals Frobenius iff rank at most one:** ‖E‖₂ = ‖E‖_F exactly when
    rank E ≤ 1. -/
theorem norm_eq_frobeniusNorm'_iff_rank_le_one (E : Matrix n n ℂ) :
    ‖E‖ = frobeniusNorm' E ↔ E.rank ≤ 1 := by
  by_cases hE : E = 0
  · -- Both sides hold at E = 0
    subst hE
    have h0 : frobeniusNorm' (0 : Matrix n n ℂ) = 0 := by
      have h := frobeniusNorm'_sq (0 : Matrix n n ℂ)
      simp only [zero_apply, map_zero, Finset.sum_const_zero] at h
      exact (pow_eq_zero_iff two_ne_zero).mp h
    rw [h0, norm_zero, Matrix.rank_zero]
    simp
  have h_spec_pos : 0 < ‖E‖ := norm_pos_iff.mpr hE
  -- The largest singular value is ‖E‖ and is nonzero
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (SVD.singularValues E)
  have hj_eq : SVD.singularValues E j = ‖E‖ := by
    rw [spectral_norm_eq_max_singularValue]
    exact hj.symm
  have hjS : j ∈ Finset.univ.filter (fun i => SVD.singularValues E i ≠ 0) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ j, by rw [hj_eq]; exact h_spec_pos.ne'⟩
  constructor
  · intro h_eq
    -- Σ over nonzero σᵢ of σᵢ² = ‖E‖² = σⱼ², so the other nonzero terms sum to 0
    have h_sum : ∑ i ∈ Finset.univ.filter (fun i => SVD.singularValues E i ≠ 0),
        SVD.singularValues E i ^ 2 = ‖E‖ ^ 2 := by
      rw [← frobeniusNorm'_sq_eq_sum_nonzero, h_eq]
    have h_rest : ∑ i ∈ (Finset.univ.filter (fun i => SVD.singularValues E i ≠ 0)).erase j,
        SVD.singularValues E i ^ 2 = 0 := by
      rw [← Finset.add_sum_erase _ _ hjS, hj_eq] at h_sum
      linarith
    -- A zero sum of squares of nonzero numbers is empty, so only j is left
    have h_erase : (Finset.univ.filter (fun i => SVD.singularValues E i ≠ 0)).erase j = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro i hi
      have h0 := (Finset.sum_eq_zero_iff_of_nonneg
        (fun k _ => sq_nonneg (SVD.singularValues E k))).mp h_rest i hi
      have hi_ne := (Finset.mem_filter.mp (Finset.mem_erase.mp hi).2).2
      exact hi_ne ((pow_eq_zero_iff two_ne_zero).mp h0)
    have h_card := Finset.card_erase_of_mem hjS
    rw [h_erase, Finset.card_empty, card_filter_singularValues_ne_zero] at h_card
    omega
  · intro h_rank
    -- rank E = 1, so j is the only nonzero singular value
    have h_rank_one : E.rank = 1 := by
      have := rank_pos_of_ne_zero E hE
      omega
    have h_card : (Finset.univ.filter (fun i => SVD.singularValues E i ≠ 0)).card = 1 := by
      rw [card_filter_singularValues_ne_zero, h_rank_one]
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h_card
    have hja : j = a := by
      rw [ha] at hjS
      exact Finset.mem_singleton.mp hjS
    have h_frob_sq : frobeniusNorm' E ^ 2 = ‖E‖ ^ 2 := by
      rw [frobeniusNorm'_sq_eq_sum_nonzero, ha, Finset.sum_singleton, ← hja, hj_eq]
    exact ((sq_eq_sq₀ h_spec_pos.le (frobeniusNorm'_nonneg E)).mp h_frob_sq.symm)

end IncoherentCase

/-! ## Kronecker Coherence

### References

* Van Loan & Pitsianis (1993). "Approximation with Kronecker Products"
* SpectralNormGap.lean for the base inequality

### Tags

kronecker, coherence, spectral norm, approximation, rearrangement
-/

section KroneckerCoherence

open Matrix.KroneckerRearrangement
open Matrix.SVD

variable {m n p q : Type*}
variable [Fintype m] [Fintype n] [Fintype p] [Fintype q]
variable [DecidableEq m] [DecidableEq n] [DecidableEq p] [DecidableEq q]

-- Enable L2 operator norm instances locally
attribute [local instance] Matrix.instL2OpNormedAddCommGroup
attribute [local instance] Matrix.instL2OpNormedSpace
attribute [local instance] Matrix.frobeniusSeminormedAddCommGroup

/-- Notation for L2 operator norm. -/
local notation "‖" A "‖₂" => @Norm.norm _ Matrix.instL2OpNormedAddCommGroup.toNorm A

/-- Notation for Frobenius norm. -/
local notation "‖" A "‖_F" => @Norm.norm _ Matrix.frobeniusSeminormedAddCommGroup.toNorm A

/-! ### Section 4a: Kronecker Space Coherence

Define coherence in the rearranged R-space. The coherence of a matrix C in Kronecker
space is the coherence factor of R(C) as a rectangular matrix.
-/

/-- **Kronecker Coherence**: The coherence factor of the rearranged matrix R(C).

For C : Matrix (m × n) (p × q) ℂ, we have R(C) : Matrix (m × p) (n × q) ℂ.
The Kronecker coherence μ_R(C) measures how concentrated the singular values of R(C) are.
No theorem here turns it into a bound on the Kronecker approximation error ‖C - R⁻¹M‖₂.

- μ_R ≈ 1: R(C) is incoherent (flat singular value spectrum)
- μ_R ≈ 1/√rank: R(C) is coherent (rank-1 dominated, like A⊗B) -/
noncomputable def kroneckerCoherence (C : Matrix (m × n) (p × q) ℂ) : ℝ :=
  coherenceFactorRect (R C)

omit [DecidableEq m] [DecidableEq p] in
/-- For the zero matrix, Kronecker coherence is 1. -/
theorem kroneckerCoherence_zero : kroneckerCoherence (0 : Matrix (m × n) (p × q) ℂ) = 1 := by
  unfold kroneckerCoherence
  have h_R_zero : R (0 : Matrix (m × n) (p × q) ℂ) = 0 := by
    ext ⟨i, k⟩ ⟨j, l⟩
    rfl
  rw [h_R_zero, coherenceFactorRect_zero]

omit [DecidableEq m] [DecidableEq p] in
/-- Kronecker coherence is non-negative. -/
theorem kroneckerCoherence_nonneg (C : Matrix (m × n) (p × q) ℂ) :
    0 ≤ kroneckerCoherence C :=
  coherenceFactorRect_nonneg (R C)

omit [DecidableEq m] [DecidableEq p] in
/-- For nonzero matrices, Kronecker coherence is positive. -/
theorem kroneckerCoherence_pos_of_ne_zero (C : Matrix (m × n) (p × q) ℂ)
    (hC : R C ≠ 0) :
    0 < kroneckerCoherence C :=
  coherenceFactorRect_pos_of_ne_zero (R C) hC

/-- Kronecker coherence is at most 1. -/
theorem kroneckerCoherence_le_one
    (C : Matrix (m × n) (p × q) ℂ) :
    kroneckerCoherence C ≤ 1 :=
  coherenceFactorRect_le_one (R C)

/-- Kronecker coherence is at least 1/√rank(R(C)) when R(C) ≠ 0. -/
theorem kroneckerCoherence_ge_inv_sqrt_rank
    (C : Matrix (m × n) (p × q) ℂ) (hC : R C ≠ 0) :
    1 / Real.sqrt (R C).rank ≤ kroneckerCoherence C :=
  coherenceFactorRect_ge_inv_sqrt_rank (R C) hC

/-- Combined bounds for Kronecker coherence: 1/√rank ≤ μ_R(C) ≤ 1. -/
theorem kroneckerCoherence_bounds
    (C : Matrix (m × n) (p × q) ℂ) (hC : R C ≠ 0) :
    1 / Real.sqrt (R C).rank ≤ kroneckerCoherence C ∧ kroneckerCoherence C ≤ 1 :=
  ⟨kroneckerCoherence_ge_inv_sqrt_rank C hC, kroneckerCoherence_le_one C⟩

/-- **The R⁻¹ bound is attained when R⁻¹ X has rank one:** for X = R(u vᵀ), ‖R⁻¹ X‖₂ = ‖X‖_F.
    So the constant in `Matrix.Kronecker.SpectralBounds.R_inv_spectral_le_frobenius`
    (‖R⁻¹ X‖₂ ≤ ‖X‖_F) cannot be improved; `Matrix.Kronecker.SpectralBounds.R_inv_spectral_lt_frobenius_R_one` shows the bound
    is strict for X = R(1). -/
theorem R_inv_spectral_eq_frobenius_R_outerProduct [Nonempty (m × n)] [Nonempty (p × q)]
    (u : EuclideanSpace ℂ (m × n)) (v : EuclideanSpace ℂ (p × q)) :
    ‖R_inv (R (KroneckerRearrangement.outerProduct u v))‖₂ =
      ‖R (KroneckerRearrangement.outerProduct u v)‖_F := by
  have h1 : R_inv (R (KroneckerRearrangement.outerProduct u v)) =
      KroneckerRearrangement.outerProduct u v := R_inv_R _
  have h2 : ‖R (KroneckerRearrangement.outerProduct u v)‖_F =
      ‖KroneckerRearrangement.outerProduct u v‖_F := R_frobenius_norm_eq _
  rw [h1, h2]
  exact rank_one_spectral_eq_frobenius u v

/-- **Equality case of the R⁻¹ bound:** ‖R⁻¹ X‖₂ = ‖X‖_F exactly when R⁻¹ X has rank ≤ 1. Since R
    is a Frobenius isometry, ‖X‖_F = ‖R⁻¹ X‖_F, and this is
    `spectral_eq_frobenius_rect_iff_rank_le_one` for R⁻¹ X. -/
theorem R_inv_spectral_eq_frobenius_iff_rank_le_one (X : Matrix (m × p) (n × q) ℂ) :
    ‖R_inv X‖₂ = ‖X‖_F ↔ (R_inv X).rank ≤ 1 := by
  have h_iso : ‖X‖_F = ‖R_inv X‖_F := by
    have h := R_frobenius_norm_eq (R_inv X)
    rw [R_R_inv] at h
    exact h
  rw [h_iso]
  exact spectral_eq_frobenius_rect_iff_rank_le_one (R_inv X)

end KroneckerCoherence

/-! ## Frobenius-Spectral Solution Distance

For a square matrix `A`, compare
- `A_F = truncatedSVD A 1`, the Frobenius-optimal rank-1 approximation, and
- `A_* = spectralOptimalRank1 A`, an arbitrary (`Classical.choose`) spectral-norm minimizer
  over rank-1 matrices.

In the Kronecker application `A` is the rearrangement `R C`; nothing here uses that.

**Main results** (`‖·‖` is the L2 operator norm):
- `spectral_error_truncatedSVD_one_eq_spectralOptimalRank1`: `‖A - A_F‖ = ‖A - A_*‖`. By the
  spectral Eckart–Young theorem, `A_F` is itself a spectral minimizer.
- `norm_sub_truncatedSVD_one_eq_norm_sub_spectralGap`: `‖A - A_F‖ = ‖A‖ - spectralGap A`
  (that is, `σ₁` when `card n > 1`, 0-indexed).
- `frobenius_spectral_solution_distance`: `‖A_F - A_*‖ ≤ 2 · ‖A - A_F‖`.
- `frobenius_spectral_distance_with_gap`: `‖A_F - A_*‖ ≤ 2 · (‖A‖ - spectralGap A)`.
- `decision_criterion`: a gap of at least `(1 - δ/2) · ‖A‖` gives `‖A_F - A_*‖ ≤ δ · ‖A‖`.

Spectral minimizers are not unique, so `‖A_F - A_*‖` need not be 0. For `A = diag(2, 1)`,
both `diag(2, 0)` and `diag(3, 0)` have spectral error 1.
-/

section SolutionDistance

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-! ### Basic Definitions -/

/-- The spectral gap of a matrix: σ₀ - σ₁, the difference between the two largest singular
    values (0-indexed). For a 1×1 matrix it is σ₀. -/
noncomputable def spectralGap (A : Matrix n n ℂ) : ℝ :=
  if h : 1 < Fintype.card n then
    SVD.singularValues₀ A 0 - SVD.singularValues₀ A ⟨1, h⟩
  else
    SVD.singularValues₀ A 0  -- Only one singular value, gap is the value itself

/-- The spectral gap is nonnegative (since singular values are sorted in decreasing order). -/
theorem spectralGap_nonneg (A : Matrix n n ℂ) : 0 ≤ spectralGap A := by
  unfold spectralGap
  split_ifs with h
  · -- Case: card n > 1
    have h_antitone := SVD.singularValues₀_antitone A
    have h_le : SVD.singularValues₀ A ⟨1, h⟩ ≤ SVD.singularValues₀ A 0 :=
      h_antitone (Fin.zero_le _)
    linarith
  · -- Case: card n ≤ 1
    exact SVD.singularValues₀_nonneg A _

/-- The spectral gap is at most the spectral norm: `spectralGap A ≤ ‖A‖`. -/
theorem spectralGap_le_norm (A : Matrix n n ℂ) : spectralGap A ≤ ‖A‖ := by
  have h_norm : ‖A‖ = SVD.singularValues₀ A 0 :=
    Matrix.SVD.spectral_norm_eq_singularValues₀_zero A
  rw [h_norm]
  unfold spectralGap
  split_ifs with h
  · linarith [SVD.singularValues₀_nonneg A ⟨1, h⟩]
  · exact le_refl _

/-- **Existence of Spectral-Optimal Solution**

For any matrix A, there exists a rank-1 matrix M* that minimizes the spectral norm ‖A - M‖₂
over all rank-1 matrices M.

The rank-1 truncated SVD is such a minimizer, by the spectral-norm
Eckart-Young theorem (`eckart_young_spectral`). -/
theorem exists_spectral_minimizer_rank1 (A : Matrix n n ℂ) :
    ∃ M : Matrix n n ℂ, M.rank ≤ 1 ∧
      ∀ N : Matrix n n ℂ, N.rank ≤ 1 → ‖A - M‖ ≤ ‖A - N‖ :=
  ⟨Matrix.SVD.truncatedSVD A 1, Matrix.SVD.truncatedSVD_rank_le A 1,
    fun N hN => Matrix.SVD.eckart_young_spectral A 1 N hN⟩

/-- The spectral-optimal rank-1 approximation (chosen via `Classical.choose`). -/
noncomputable def spectralOptimalRank1 (A : Matrix n n ℂ) : Matrix n n ℂ :=
  Classical.choose (exists_spectral_minimizer_rank1 A)

/-- The spectral-optimal approximation achieves the minimum. -/
theorem spectralOptimalRank1_is_optimal (A : Matrix n n ℂ) :
    (spectralOptimalRank1 A).rank ≤ 1 ∧
    ∀ N : Matrix n n ℂ, N.rank ≤ 1 → ‖A - spectralOptimalRank1 A‖ ≤ ‖A - N‖ :=
  Classical.choose_spec (exists_spectral_minimizer_rank1 A)

/-! ### Main Distance Bound -/

/-- **The Frobenius-optimal rank-1 approximation is spectrally optimal:**
    ‖A - A_F‖₂ = ‖A - A_*‖₂ for A_F = truncatedSVD A 1 and A_* = spectralOptimalRank1 A. -/
theorem spectral_error_truncatedSVD_one_eq_spectralOptimalRank1 (A : Matrix n n ℂ) :
    ‖A - Matrix.SVD.truncatedSVD A 1‖ = ‖A - spectralOptimalRank1 A‖ := by
  have ⟨h_rank, h_opt⟩ := spectralOptimalRank1_is_optimal A
  -- A_F is no worse than A_*, by spectral Eckart–Young
  have h_le : ‖A - Matrix.SVD.truncatedSVD A 1‖ ≤ ‖A - spectralOptimalRank1 A‖ :=
    Matrix.SVD.eckart_young_spectral A 1 _ h_rank
  -- A_* is no worse than A_F, by its own optimality
  have h_ge : ‖A - spectralOptimalRank1 A‖ ≤ ‖A - Matrix.SVD.truncatedSVD A 1‖ :=
    h_opt _ (Matrix.SVD.truncatedSVD_rank_le A 1)
  exact le_antisymm h_le h_ge

/-- **Spectral error of the rank-1 truncation in terms of the gap:**
    ‖A - truncatedSVD A 1‖₂ = ‖A‖₂ - spectralGap A.

    For `card n > 1` both sides equal σ₁ (0-indexed); for `card n = 1` both are 0. -/
theorem norm_sub_truncatedSVD_one_eq_norm_sub_spectralGap (A : Matrix n n ℂ) :
    ‖A - Matrix.SVD.truncatedSVD A 1‖ = ‖A‖ - spectralGap A := by
  have h_norm : ‖A‖ = SVD.singularValues₀ A 0 :=
    Matrix.SVD.spectral_norm_eq_singularValues₀_zero A
  rw [h_norm]
  unfold spectralGap
  split_ifs with h
  · -- card n > 1: the error is σ₁
    have h_err : ‖A - Matrix.SVD.truncatedSVD A 1‖ = SVD.singularValues₀ A ⟨1, h⟩ :=
      Matrix.SVD.spectral_error_truncatedSVD A 1 h
    rw [h_err]
    ring
  · -- card n ≤ 1: the truncation is A itself
    have h_full : Matrix.SVD.truncatedSVD A 1 = A :=
      Matrix.SVD.truncatedSVD_full A 1 (Nat.le_of_not_lt h)
    rw [h_full, sub_self, norm_zero, sub_self]

/-- `spectralOptimalRank1 A` is no worse than A_F = truncatedSVD A 1, so it satisfies the
    hypothesis `h_le` of the distance bounds below. -/
theorem norm_sub_spectralOptimalRank1_le (A : Matrix n n ℂ) :
    ‖A - spectralOptimalRank1 A‖ ≤ ‖A - Matrix.SVD.truncatedSVD A 1‖ :=
  (spectralOptimalRank1_is_optimal A).2 _ (Matrix.SVD.truncatedSVD_rank_le A 1)

omit [Nonempty n] in
/-- **Main Theorem: Distance Between Frobenius and Spectral Solutions**

Let A_F = truncatedSVD(A, 1) be the Frobenius-optimal rank-1 approximation. Every M whose
spectral error is at most that of A_F satisfies

  ‖A_F - M‖₂ ≤ 2 · ‖A - A_F‖₂.

This covers every spectral-optimal rank-1 approximation, for instance `spectralOptimalRank1 A`
(`norm_sub_spectralOptimalRank1_le`).

**Proof:** ‖A_F - M‖ ≤ ‖A - M‖ + ‖A - A_F‖ ≤ 2 · ‖A - A_F‖. -/
theorem frobenius_spectral_solution_distance (A M : Matrix n n ℂ)
    (h_le : ‖A - M‖ ≤ ‖A - Matrix.SVD.truncatedSVD A 1‖) :
    ‖Matrix.SVD.truncatedSVD A 1 - M‖ ≤ 2 * ‖A - Matrix.SVD.truncatedSVD A 1‖ := by
  calc ‖Matrix.SVD.truncatedSVD A 1 - M‖
      = ‖(A - M) - (A - Matrix.SVD.truncatedSVD A 1)‖ := by congr 1; abel
    _ ≤ ‖A - M‖ + ‖A - Matrix.SVD.truncatedSVD A 1‖ := norm_sub_le _ _
    _ ≤ 2 * ‖A - Matrix.SVD.truncatedSVD A 1‖ := by linarith

/-- **Frobenius form of the solution distance:** ‖A_F - M‖₂ ≤ 2 · ‖A - A_F‖_F for every M with
    ‖A - M‖₂ ≤ ‖A - A_F‖₂.

    Weaker than `frobenius_spectral_solution_distance`, since ‖·‖₂ ≤ ‖·‖_F. -/
theorem frobenius_spectral_solution_distance_le_frobenius (A M : Matrix n n ℂ)
    (h_le : ‖A - M‖ ≤ ‖A - Matrix.SVD.truncatedSVD A 1‖) :
    ‖Matrix.SVD.truncatedSVD A 1 - M‖ ≤
      2 * frobeniusNorm' (A - Matrix.SVD.truncatedSVD A 1) := by
  have h_dist := frobenius_spectral_solution_distance A M h_le
  have h_spec_frob : ‖A - Matrix.SVD.truncatedSVD A 1‖ ≤
      frobeniusNorm' (A - Matrix.SVD.truncatedSVD A 1) :=
    spectral_norm_le_frobenius_norm (A - Matrix.SVD.truncatedSVD A 1)
  linarith

/-- **Solution distance in terms of the spectral gap:** for every M with
    ‖A - M‖₂ ≤ ‖A - A_F‖₂ (every spectral minimizer), ‖A_F - M‖₂ ≤ 2 · (‖A‖₂ - spectralGap A),
    together with the Frobenius tail formula ‖A - A_F‖_F² = Σᵢ≥₁ σᵢ² (0-indexed, so σ₀ is the
    largest).

    The larger the gap σ₀ - σ₁ relative to ‖A‖₂ = σ₀, the closer every spectral minimizer is
    to A_F. -/
theorem frobenius_spectral_distance_with_gap (A M : Matrix n n ℂ)
    (h_le : ‖A - M‖ ≤ ‖A - Matrix.SVD.truncatedSVD A 1‖) :
    ‖Matrix.SVD.truncatedSVD A 1 - M‖ ≤ 2 * (‖A‖ - spectralGap A) ∧
    -- The squared Frobenius error is the sum of the squared tail singular values
    frobeniusNorm' (A - Matrix.SVD.truncatedSVD A 1) ^ 2 =
      ∑ i : Fin (Fintype.card n), if i.val = 0 then 0 else (SVD.singularValues₀ A i) ^ 2 := by
  constructor
  · rw [← norm_sub_truncatedSVD_one_eq_norm_sub_spectralGap]
    exact frobenius_spectral_solution_distance A M h_le
  · -- The Frobenius error of truncatedSVD equals the sum of tail singular values squared
    -- Use frobenius_error_truncatedSVD from FrobeniusNorm.lean which gives:
    -- ‖A - truncatedSVD A k‖² = ∑ i : n, (truncatedSingularValues_tail A k i)²
    -- where the norm is the Frobenius norm (via frobeniusSeminormedAddCommGroup).
    -- frobeniusNorm' is definitionally equal to this norm.
    --
    -- Step 1: Apply frobenius_error_truncatedSVD
    have h_frob_error := Matrix.FrobeniusNorm.frobenius_error_truncatedSVD A 1
    -- h_frob_error : ‖A - truncatedSVD A 1‖² = ∑ i, (truncatedSingularValues_tail A 1 i)²
    -- where ‖·‖ uses frobeniusSeminormedAddCommGroup
    -- frobeniusNorm' uses frobeniusNormedAddCommGroup which has the same toNorm
    have h_norm_eq : frobeniusNorm' (A - SVD.truncatedSVD A 1) ^ 2 =
                     ∑ i : n, (SVD.truncatedSingularValues_tail A 1 i)^2 := by
      -- The two norms are definitionally equal
      convert h_frob_error using 1
    rw [h_norm_eq]
    -- Step 2: Reindex from n to Fin (Fintype.card n)
    -- truncatedSingularValues_tail A 1 i = if 1 ≤ (e.symm i).val then singularValues₀ A (e.symm i) else 0
    let e := (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n)) : Fin (Fintype.card n) ≃ n)
    have h_sum_reindex : ∑ i : n, (SVD.truncatedSingularValues_tail A 1 i)^2 =
                         ∑ j : Fin (Fintype.card n), (SVD.truncatedSingularValues_tail A 1 (e j))^2 :=
      (Fintype.sum_equiv e _ _ (fun _ => rfl)).symm
    rw [h_sum_reindex]
    apply Finset.sum_congr rfl
    intro j _
    -- Step 3: Show the conditional equivalence
    -- The key is that e.symm (e j) = j, but inside truncatedSingularValues_tail there's
    -- another equivOfCardEq which is definitionally equal to e
    have h_equiv_simpl : (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n))).symm (e j) = j :=
      Equiv.symm_apply_apply _ j
    -- Unfold the definition and use the simplification
    unfold SVD.truncatedSingularValues_tail
    simp only [h_equiv_simpl]
    -- Goal: (if 1 ≤ j.val then singularValues₀ A j else 0)² = if j.val = 0 then 0 else (singularValues₀ A j)²
    by_cases hj : j.val = 0
    · -- j.val = 0: LHS uses ¬(1 ≤ 0), so if-then-else gives 0²
      simp only [hj, Nat.one_le_iff_ne_zero, ne_eq, not_true_eq_false, ↓reduceIte]
      ring
    · -- j.val ≠ 0: both sides are (singularValues₀ A j)²
      have h1 : 1 ≤ j.val := Nat.one_le_iff_ne_zero.mpr hj
      simp only [h1, ↓reduceIte, hj]

omit [Nonempty n] in
/-- **Coherence form of the distance bound**

  ‖A_F - M‖₂ ≤ 2 · ‖E‖_F / (√r · μ)

for every M with ‖A - M‖₂ ≤ ‖A - A_F‖₂, where E = A - A_F, r = rank(E) and
μ = coherenceFactor(E). The right side equals 2 · ‖E‖₂
(`spectral_norm_eq_frobenius_div_coherence`), so this is `frobenius_spectral_solution_distance` written
in coherence terms. Since ‖E‖₂ ≤ ‖E‖_F, it is at most ‖E‖_F · (1 + 1/(√r · μ)). -/
theorem frobenius_spectral_distance_coherence_aware (A M : Matrix n n ℂ)
    (h_le : ‖A - M‖ ≤ ‖A - Matrix.SVD.truncatedSVD A 1‖)
    (h_err : A - Matrix.SVD.truncatedSVD A 1 ≠ 0) :
    let E := A - Matrix.SVD.truncatedSVD A 1
    let μ := coherenceFactor E
    let r := E.rank
    ‖Matrix.SVD.truncatedSVD A 1 - M‖ ≤
      2 * (frobeniusNorm' E / (Real.sqrt r * μ)) := by
  intro E μ r
  -- ‖E‖₂ = ‖E‖_F / (√r · μ)
  have h_coh_eq : ‖E‖ = frobeniusNorm' E / (Real.sqrt r * μ) :=
    spectral_norm_eq_frobenius_div_coherence E h_err
  have h_dist : ‖Matrix.SVD.truncatedSVD A 1 - M‖ ≤ 2 * ‖E‖ :=
    frobenius_spectral_solution_distance A M h_le
  rw [← h_coh_eq]
  exact h_dist

/-- **Decision criterion.** If the spectral gap is at least (1 - δ/2) · ‖A‖₂, then every M with
    ‖A - M‖₂ ≤ ‖A - A_F‖₂, in particular every spectral-optimal rank-1 approximation, is within
    δ · ‖A‖₂ of A_F:

      spectralGap A ≥ (1 - δ/2) · ‖A‖₂  ⟹  ‖A_F - M‖₂ ≤ δ · ‖A‖₂. -/
theorem decision_criterion (A M : Matrix n n ℂ) (δ : ℝ)
    (h_le : ‖A - M‖ ≤ ‖A - Matrix.SVD.truncatedSVD A 1‖)
    (h_gap : (1 - δ / 2) * ‖A‖ ≤ spectralGap A) :
    ‖Matrix.SVD.truncatedSVD A 1 - M‖ ≤ δ * ‖A‖ := by
  have h_dist := (frobenius_spectral_distance_with_gap A M h_le).1
  calc ‖Matrix.SVD.truncatedSVD A 1 - M‖
      ≤ 2 * (‖A‖ - spectralGap A) := h_dist
    _ ≤ 2 * (‖A‖ - (1 - δ / 2) * ‖A‖) := by linarith
    _ = δ * ‖A‖ := by ring

end SolutionDistance

end Matrix.Coherence
