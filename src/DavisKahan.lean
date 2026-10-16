/-
Copyright (c) 2025 FLYWHEEL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aleksandar Markovski
-/
import CoherenceCharacterization

/-!
# Davis–Kahan sin θ bound for the top eigenvector

For a Hermitian A with eigenvalues λ₀ ≥ λ₁ ≥ ⋯ (0-indexed) and top unit eigenvector u₀, let v be
an eigenvector of a perturbation A + E with eigenvalue μ > λ₁. Then the part of v orthogonal to
u₀ is small:

  (μ - λ₁) ‖v - ⟨u₀, v⟩ u₀‖ ≤ ‖E‖₂ ‖v‖                                  (`davis_kahan_top`)

Proof: (A - μ) v = -E v. In A's eigenbasis the i-th coefficient of E v is (μ - λᵢ) cᵢ with
cᵢ = ⟨uᵢ, v⟩, and |μ - λᵢ| ≥ μ - λ₁ for every i other than the top index. E need not be
Hermitian for this step.

With Weyl's inequality (μ = λ₀(A + E) ≥ λ₀(A) - ‖E‖₂ for Hermitian E) this gives, for
‖E‖₂ < δ := λ₀ - λ₁ and a unit top eigenvector v of A + E,

  ‖v - ⟨u₀, v⟩ u₀‖ ≤ ‖E‖₂ / (δ - ‖E‖₂)                        (`davis_kahan_top_of_norm_lt_gap`).

Applied to the Gram matrices Aᴴ A and Ãᴴ Ã it bounds the top right singular vector of a
perturbed matrix (`top_right_singular_vector_perturbation`), with the gap σ₀² - σ₁²; that gap is
at least `Matrix.Coherence.spectralGap A * ‖A‖₂` (`spectralGap_mul_norm_le_sq_sub_sq`). This is
a Wedin-type bound through the Gram matrix, not Wedin's theorem itself (which has the gap
σ₀ - σ₁ and the perturbation ‖E‖₂ directly).

Here ‖·‖ on square matrices is the L2 operator norm (the global instance of
MatrixNormRelations).

Not formalized: the top-k eigenspace version (sin Θ for invariant subspaces).
-/

open scoped ComplexOrder Matrix
open Matrix

namespace Matrix.DavisKahan

variable {n : Type*} [Fintype n] [DecidableEq n]

local notation "⟪" x ", " y "⟫" => @inner ℂ (EuclideanSpace ℂ n) _ x y

/-! ## The top eigenvector -/

section TopIndex

/-- The index of the largest eigenvalue: the position of sorted index 0 under Mathlib's
    eigenvalue bijection. -/
noncomputable def topIndex (h2 : 1 < Fintype.card n) : n :=
  Fintype.equivOfCardEq (Fintype.card_fin _) ⟨0, by omega⟩

/-- The eigenvalue at `topIndex` is the largest one, λ₀. -/
theorem eigenvalues_topIndex {A : Matrix n n ℂ} (hA : A.IsHermitian) (h2 : 1 < Fintype.card n) :
    hA.eigenvalues (topIndex h2) = hA.eigenvalues₀ ⟨0, by omega⟩ := by
  rw [CourantFischer.eigenvalues_eq_eigenvalues₀_comp A hA, topIndex, Equiv.symm_apply_apply]

/-- Every eigenvalue other than the top one is at most λ₁. -/
theorem eigenvalues_le_of_ne_topIndex {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (h2 : 1 < Fintype.card n) (i : n) (hi : i ≠ topIndex h2) :
    hA.eigenvalues i ≤ hA.eigenvalues₀ ⟨1, h2⟩ := by
  have h_ne : ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm i).val ≠ 0 := by
    intro h0
    apply hi
    rw [topIndex, ← Equiv.symm_apply_eq]
    exact Fin.ext h0
  rw [CourantFischer.eigenvalues_eq_eigenvalues₀_comp A hA]
  exact hA.eigenvalues₀_antitone (Fin.le_def.mpr (Nat.one_le_iff_ne_zero.mpr h_ne))

end TopIndex

/-! ## The sin θ bound -/

section SinTheta

/-- **Davis–Kahan sin θ bound for the top eigenvector.** Let A be Hermitian with top unit
    eigenvector u₀ and second eigenvalue λ₁ (0-indexed), and let v satisfy (A + E) v = μ v with
    μ > λ₁. Then (μ - λ₁) ‖v - ⟨u₀, v⟩ u₀‖ ≤ ‖E‖₂ ‖v‖. E need not be Hermitian. -/
theorem davis_kahan_top (A E : Matrix n n ℂ) (hA : A.IsHermitian) (h2 : 1 < Fintype.card n)
    (v : EuclideanSpace ℂ n) (μ : ℝ) (hv : toEuclideanLin (A + E) v = (μ : ℂ) • v)
    (hμ : hA.eigenvalues₀ ⟨1, h2⟩ < μ) :
    (μ - hA.eigenvalues₀ ⟨1, h2⟩) *
        ‖v - ⟪hA.eigenvectorBasis (topIndex h2), v⟫ • hA.eigenvectorBasis (topIndex h2)‖ ≤
      ‖E‖ * ‖v‖ := by
  have hSym : (toEuclideanLin A).IsSymmetric := isHermitian_iff_isSymmetric.mp hA
  have hEig : ∀ i, toEuclideanLin A (hA.eigenvectorBasis i) =
      (hA.eigenvalues i : ℂ) • hA.eigenvectorBasis i := by
    intro i
    ext j
    have := hA.mulVec_eigenvectorBasis i
    simp only [Matrix.toEuclideanLin_apply] at this ⊢
    exact congr_fun this j
  -- Coefficients of A x in the eigenbasis: ⟨uᵢ, A x⟩ = λᵢ ⟨uᵢ, x⟩
  have hcoefA : ∀ i x, ⟪hA.eigenvectorBasis i, toEuclideanLin A x⟫ =
      (hA.eigenvalues i : ℂ) * ⟪hA.eigenvectorBasis i, x⟫ := by
    intro i x
    rw [← hSym (hA.eigenvectorBasis i) x, hEig i, inner_smul_left, Complex.conj_ofReal]
  -- E v = μ v - A v, so ⟨uᵢ, E v⟩ = (μ - λᵢ) ⟨uᵢ, v⟩
  have hEv : toEuclideanLin E v = (μ : ℂ) • v - toEuclideanLin A v := by
    rw [← hv, WeylInequality.toEuclideanLin_add]
    abel
  have hcoefE : ∀ i, ⟪hA.eigenvectorBasis i, toEuclideanLin E v⟫ =
      ((μ - hA.eigenvalues i : ℝ) : ℂ) * ⟪hA.eigenvectorBasis i, v⟫ := by
    intro i
    rw [hEv, inner_sub_right, inner_smul_right, hcoefA]
    push_cast
    ring
  -- ‖E v‖² = Σᵢ (μ - λᵢ)² |cᵢ|²
  have hEv_sq : ‖toEuclideanLin E v‖ ^ 2 =
      ∑ i, (μ - hA.eigenvalues i) ^ 2 * ‖⟪hA.eigenvectorBasis i, v⟫‖ ^ 2 := by
    rw [← hA.eigenvectorBasis.sum_sq_norm_inner_right (toEuclideanLin E v)]
    apply Finset.sum_congr rfl
    intro i _
    rw [hcoefE i, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  -- The residual w = v - ⟨u₀, v⟩ u₀ has coefficients cᵢ off the top index and 0 on it
  obtain ⟨w, hw⟩ : ∃ w : EuclideanSpace ℂ n,
      w = v - ⟪hA.eigenvectorBasis (topIndex h2), v⟫ • hA.eigenvectorBasis (topIndex h2) :=
    ⟨_, rfl⟩
  rw [← hw]
  have hw_coef : ∀ i, ⟪hA.eigenvectorBasis i, w⟫ =
      if i = topIndex h2 then 0 else ⟪hA.eigenvectorBasis i, v⟫ := by
    intro i
    rw [hw, inner_sub_right, inner_smul_right,
      orthonormal_iff_ite.mp hA.eigenvectorBasis.orthonormal i (topIndex h2)]
    split_ifs with h
    · subst h
      ring
    · ring
  have hw_sq : ‖w‖ ^ 2 =
      ∑ i ∈ Finset.univ.erase (topIndex h2), ‖⟪hA.eigenvectorBasis i, v⟫‖ ^ 2 := by
    have h_split : ‖⟪hA.eigenvectorBasis (topIndex h2), w⟫‖ ^ 2 +
        ∑ i ∈ Finset.univ.erase (topIndex h2), ‖⟪hA.eigenvectorBasis i, w⟫‖ ^ 2 =
        ∑ i, ‖⟪hA.eigenvectorBasis i, w⟫‖ ^ 2 :=
      Finset.add_sum_erase Finset.univ (fun i => ‖⟪hA.eigenvectorBasis i, w⟫‖ ^ 2)
        (Finset.mem_univ _)
    rw [← hA.eigenvectorBasis.sum_sq_norm_inner_right w, ← h_split, hw_coef (topIndex h2),
      if_pos rfl, norm_zero, zero_pow two_ne_zero, zero_add]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hw_coef i, if_neg (Finset.ne_of_mem_erase hi)]
  -- Off the top index, (μ - λᵢ)² ≥ (μ - λ₁)²
  have h_gap_i : ∀ i ∈ Finset.univ.erase (topIndex h2),
      (μ - hA.eigenvalues₀ ⟨1, h2⟩) ^ 2 ≤ (μ - hA.eigenvalues i) ^ 2 := by
    intro i hi
    have h_le := eigenvalues_le_of_ne_topIndex hA h2 i (Finset.ne_of_mem_erase hi)
    exact pow_le_pow_left₀ (by linarith) (by linarith) 2
  have h_key : (μ - hA.eigenvalues₀ ⟨1, h2⟩) ^ 2 * ‖w‖ ^ 2 ≤ ‖toEuclideanLin E v‖ ^ 2 := by
    rw [hw_sq, Finset.mul_sum, hEv_sq]
    calc ∑ i ∈ Finset.univ.erase (topIndex h2),
          (μ - hA.eigenvalues₀ ⟨1, h2⟩) ^ 2 * ‖⟪hA.eigenvectorBasis i, v⟫‖ ^ 2
        ≤ ∑ i ∈ Finset.univ.erase (topIndex h2),
          (μ - hA.eigenvalues i) ^ 2 * ‖⟪hA.eigenvectorBasis i, v⟫‖ ^ 2 :=
          Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_right (h_gap_i i hi) (sq_nonneg _))
      _ ≤ ∑ i, (μ - hA.eigenvalues i) ^ 2 * ‖⟪hA.eigenvectorBasis i, v⟫‖ ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
            (fun i _ _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  -- ‖E v‖ ≤ ‖E‖₂ ‖v‖
  have h_op : ‖toEuclideanLin E v‖ ≤ ‖E‖ * ‖v‖ := Matrix.l2_opNorm_mulVec E v
  have h1 : (μ - hA.eigenvalues₀ ⟨1, h2⟩) * ‖w‖ ≤ ‖toEuclideanLin E v‖ := by
    refine le_of_sq_le_sq ?_ (norm_nonneg _)
    rw [mul_pow]
    exact h_key
  exact h1.trans h_op

end SinTheta

/-! ## Weyl's bound and the gap form -/

section WeylForm

/-- Every eigenvalue of a Hermitian E has absolute value at most ‖E‖₂. -/
theorem abs_eigenvalues₀_le_norm {E : Matrix n n ℂ} (hE : E.IsHermitian)
    (j : Fin (Fintype.card n)) : |hE.eigenvalues₀ j| ≤ ‖E‖ := by
  haveI : Nonempty n := Fintype.card_pos_iff.mp (Nat.lt_of_le_of_lt (Nat.zero_le _) j.isLt)
  have h_norm := Matrix.SpectralNorm.l2_opNorm_hermitian_eq_sup_abs_eigenvalues E hE
  have h_eq : hE.eigenvalues₀ j =
      hE.eigenvalues (Fintype.equivOfCardEq (Fintype.card_fin _) j) := by
    rw [CourantFischer.eigenvalues_eq_eigenvalues₀_comp E hE, Equiv.symm_apply_apply]
  rw [h_eq]
  exact (Finset.le_sup' (fun i => |hE.eigenvalues i|) (Finset.mem_univ _)).trans_eq h_norm.symm

/-- **Weyl's bound for one eigenvalue:** λₖ(A) - ‖E‖₂ ≤ λₖ(A + E) for Hermitian A, E. -/
theorem eigenvalues₀_sub_norm_le_add {A E : Matrix n n ℂ} (hA : A.IsHermitian)
    (hE : E.IsHermitian) (k : Fin (Fintype.card n)) :
    hA.eigenvalues₀ k - ‖E‖ ≤ (hA.add hE).eigenvalues₀ k := by
  haveI : Nonempty n := Fintype.card_pos_iff.mp (Nat.lt_of_le_of_lt (Nat.zero_le _) k.isLt)
  have h_weyl := WeylInequality.weyl_eigenvalue_lower_bound A E hA hE k
  have h_min := abs_eigenvalues₀_le_norm hE WeylInequality.minEigenvalueIdx
  have h_neg := neg_abs_le (hE.eigenvalues₀ WeylInequality.minEigenvalueIdx)
  linarith

/-- **Davis–Kahan in gap form.** Let A be Hermitian with gap δ = λ₀ - λ₁ > ‖E‖₂, and let v be a
    unit vector with (A + E) v = μ v for some μ ≥ λ₀ - ‖E‖₂ (by `eigenvalues₀_sub_norm_le_add`
    this holds for the top eigenvalue μ = λ₀(A + E) when E is Hermitian). Then
    ‖v - ⟨u₀, v⟩ u₀‖ ≤ ‖E‖₂ / (δ - ‖E‖₂). -/
theorem davis_kahan_top_of_norm_lt_gap (A E : Matrix n n ℂ) (hA : A.IsHermitian)
    (h2 : 1 < Fintype.card n) (v : EuclideanSpace ℂ n) (hv1 : ‖v‖ = 1) (μ : ℝ)
    (hv : toEuclideanLin (A + E) v = (μ : ℂ) • v)
    (hμ : hA.eigenvalues₀ ⟨0, by omega⟩ - ‖E‖ ≤ μ)
    (h_small : ‖E‖ < hA.eigenvalues₀ ⟨0, by omega⟩ - hA.eigenvalues₀ ⟨1, h2⟩) :
    ‖v - ⟪hA.eigenvectorBasis (topIndex h2), v⟫ • hA.eigenvectorBasis (topIndex h2)‖ ≤
      ‖E‖ / (hA.eigenvalues₀ ⟨0, by omega⟩ - hA.eigenvalues₀ ⟨1, h2⟩ - ‖E‖) := by
  have hμ1 : hA.eigenvalues₀ ⟨1, h2⟩ < μ := by linarith
  have h_main := davis_kahan_top A E hA h2 v μ hv hμ1
  rw [hv1, mul_one] at h_main
  have h_den : 0 < hA.eigenvalues₀ ⟨0, by omega⟩ - hA.eigenvalues₀ ⟨1, h2⟩ - ‖E‖ := by linarith
  rw [le_div_iff₀ h_den]
  calc ‖v - ⟪hA.eigenvectorBasis (topIndex h2), v⟫ • hA.eigenvectorBasis (topIndex h2)‖ *
        (hA.eigenvalues₀ ⟨0, by omega⟩ - hA.eigenvalues₀ ⟨1, h2⟩ - ‖E‖)
      ≤ ‖v - ⟪hA.eigenvectorBasis (topIndex h2), v⟫ • hA.eigenvectorBasis (topIndex h2)‖ *
        (μ - hA.eigenvalues₀ ⟨1, h2⟩) :=
        mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
    _ = (μ - hA.eigenvalues₀ ⟨1, h2⟩) *
        ‖v - ⟪hA.eigenvectorBasis (topIndex h2), v⟫ • hA.eigenvectorBasis (topIndex h2)‖ :=
        mul_comm _ _
    _ ≤ ‖E‖ := h_main

/-- **Davis–Kahan for the top eigenvector of A + E.** For Hermitian A, E with
    ‖E‖₂ < δ = λ₀(A) - λ₁(A) and a unit eigenvector v of A + E for its largest eigenvalue,
    ‖v - ⟨u₀, v⟩ u₀‖ ≤ ‖E‖₂ / (δ - ‖E‖₂). -/
theorem davis_kahan_top_eigenvector (A E : Matrix n n ℂ) (hA : A.IsHermitian)
    (hE : E.IsHermitian) (h2 : 1 < Fintype.card n) (v : EuclideanSpace ℂ n) (hv1 : ‖v‖ = 1)
    (hv : toEuclideanLin (A + E) v = ((hA.add hE).eigenvalues₀ ⟨0, by omega⟩ : ℂ) • v)
    (h_small : ‖E‖ < hA.eigenvalues₀ ⟨0, by omega⟩ - hA.eigenvalues₀ ⟨1, h2⟩) :
    ‖v - ⟪hA.eigenvectorBasis (topIndex h2), v⟫ • hA.eigenvectorBasis (topIndex h2)‖ ≤
      ‖E‖ / (hA.eigenvalues₀ ⟨0, by omega⟩ - hA.eigenvalues₀ ⟨1, h2⟩ - ‖E‖) :=
  davis_kahan_top_of_norm_lt_gap A E hA h2 v hv1 _ hv
    (eigenvalues₀_sub_norm_le_add hA hE ⟨0, by omega⟩) h_small

end WeylForm

/-! ## Top right singular vectors (through the Gram matrix) -/

section SingularVector

/-- Hermitian matrices that are equal have the same sorted eigenvalues. -/
theorem eigenvalues₀_congr {M N : Matrix n n ℂ} (h : M = N) (hM : M.IsHermitian)
    (hN : N.IsHermitian) : hM.eigenvalues₀ = hN.eigenvalues₀ := by
  subst h
  rfl

/-- **Perturbation of the top right singular vector.** Let A, Ã be square, with Gram matrices
    G = Aᴴ A and G̃ = Ãᴴ Ã, F = G̃ - G, and u₀ the top eigenvector of G (a top right singular
    vector of A). If ‖F‖₂ < σ₀(A)² - σ₁(A)² and v is a unit eigenvector of G̃ for its largest
    eigenvalue σ₀(Ã)² (a top right singular vector of Ã), then
    ‖v - ⟨u₀, v⟩ u₀‖ ≤ ‖F‖₂ / (σ₀(A)² - σ₁(A)² - ‖F‖₂). -/
theorem top_right_singular_vector_perturbation (A Ã : Matrix n n ℂ) (h2 : 1 < Fintype.card n)
    (v : EuclideanSpace ℂ n) (hv1 : ‖v‖ = 1)
    (hv : toEuclideanLin (Ãᴴ * Ã) v =
      ((posSemidef_conjTranspose_mul_self Ã).isHermitian.eigenvalues₀ ⟨0, by omega⟩ : ℂ) • v)
    (h_small : ‖Ãᴴ * Ã - Aᴴ * A‖ <
      SVD.singularValues₀ A ⟨0, by omega⟩ ^ 2 - SVD.singularValues₀ A ⟨1, h2⟩ ^ 2) :
    ‖v - ⟪(posSemidef_conjTranspose_mul_self A).isHermitian.eigenvectorBasis (topIndex h2), v⟫ •
        (posSemidef_conjTranspose_mul_self A).isHermitian.eigenvectorBasis (topIndex h2)‖ ≤
      ‖Ãᴴ * Ã - Aᴴ * A‖ /
        (SVD.singularValues₀ A ⟨0, by omega⟩ ^ 2 - SVD.singularValues₀ A ⟨1, h2⟩ ^ 2 -
          ‖Ãᴴ * Ã - Aᴴ * A‖) := by
  have hG := (posSemidef_conjTranspose_mul_self A).isHermitian
  have hG' := (posSemidef_conjTranspose_mul_self Ã).isHermitian
  have hF : (Ãᴴ * Ã - Aᴴ * A).IsHermitian := hG'.sub hG
  have h_sum : Aᴴ * A + (Ãᴴ * Ã - Aᴴ * A) = Ãᴴ * Ã := by abel
  -- σᵢ(A)² are the sorted eigenvalues of the Gram matrix
  have h_sq0 := SVD.singularValues₀_sq A ⟨0, by omega⟩
  have h_sq1 := SVD.singularValues₀_sq A ⟨1, h2⟩
  rw [h_sq0, h_sq1] at h_small ⊢
  -- The top eigenvalue of G̃ = G + F is at least λ₀(G) - ‖F‖₂
  have hμ : hG.eigenvalues₀ ⟨0, by omega⟩ - ‖Ãᴴ * Ã - Aᴴ * A‖ ≤
      hG'.eigenvalues₀ ⟨0, by omega⟩ := by
    have h := eigenvalues₀_sub_norm_le_add hG hF ⟨0, by omega⟩
    rwa [eigenvalues₀_congr h_sum (hG.add hF) hG'] at h
  have hv' : toEuclideanLin (Aᴴ * A + (Ãᴴ * Ã - Aᴴ * A)) v =
      (hG'.eigenvalues₀ ⟨0, by omega⟩ : ℂ) • v := by
    rw [h_sum]
    exact hv
  exact davis_kahan_top_of_norm_lt_gap (Aᴴ * A) (Ãᴴ * Ã - Aᴴ * A) hG h2 v hv1 _ hv' hμ h_small

/-- The Gram gap σ₀² - σ₁² is at least `spectralGap A * ‖A‖₂`, since
    σ₀² - σ₁² = (σ₀ - σ₁)(σ₀ + σ₁) and σ₀ = ‖A‖₂. -/
theorem spectralGap_mul_norm_le_sq_sub_sq [Nonempty n] (A : Matrix n n ℂ)
    (h2 : 1 < Fintype.card n) :
    Coherence.spectralGap A * ‖A‖ ≤
      SVD.singularValues₀ A ⟨0, by omega⟩ ^ 2 - SVD.singularValues₀ A ⟨1, h2⟩ ^ 2 := by
  have h0 : (0 : Fin (Fintype.card n)) = ⟨0, by omega⟩ := Fin.ext (by simp)
  have h_norm0 : ‖A‖ = SVD.singularValues₀ A 0 := Matrix.SVD.spectral_norm_eq_singularValues₀_zero A
  have h_norm : ‖A‖ = SVD.singularValues₀ A ⟨0, by omega⟩ := by
    rw [h_norm0, h0]
  have h_gap : Coherence.spectralGap A =
      SVD.singularValues₀ A ⟨0, by omega⟩ - SVD.singularValues₀ A ⟨1, h2⟩ := by
    unfold Coherence.spectralGap
    rw [dif_pos h2, h0]
  rw [h_gap, h_norm]
  have h1 := SVD.singularValues₀_nonneg A ⟨1, h2⟩
  have h01 : SVD.singularValues₀ A ⟨1, h2⟩ ≤ SVD.singularValues₀ A ⟨0, by omega⟩ :=
    SVD.singularValues₀_antitone A (Fin.le_def.mpr (Nat.zero_le _))
  nlinarith

end SingularVector

end Matrix.DavisKahan
