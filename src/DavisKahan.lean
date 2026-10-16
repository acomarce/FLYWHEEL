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

The same argument with the indices of λ₀, …, λₖ₋₁ (`topIndices k`) in place of the top index
gives the top-k version: if μ > λₖ and P is the orthogonal projection onto the span of the
eigenvectors for λ₀, …, λₖ₋₁, then (μ - λₖ) ‖v - P v‖ ≤ ‖E‖₂ ‖v‖ (`davis_kahan_topIndices`).
Summed over the top-k eigenvectors ũⱼ of A + E, this bounds ‖sin Θ‖_F² = Σⱼ ‖ũⱼ - P ũⱼ‖² by
k (‖E‖₂ / (λₖ₋₁ - λₖ - ‖E‖₂))² (`davis_kahan_sin_theta`).

Here ‖·‖ on square matrices is the L2 operator norm (the global instance of
MatrixNormRelations).

Not formalized: the operator-norm sin Θ bound ‖sin Θ‖₂ ≤ ‖E‖₂ / δ for k > 1 (it needs a
Sylvester-equation argument, not a vector-by-vector one), and Wedin's theorem for left and right
singular subspaces of rectangular matrices.
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

/-! ## Coefficients in the eigenbasis -/

section Eigenbasis

/-- The vectors of `hA.eigenvectorBasis` are eigenvectors of `toEuclideanLin A`. -/
theorem toEuclideanLin_eigenvectorBasis {A : Matrix n n ℂ} (hA : A.IsHermitian) (i : n) :
    toEuclideanLin A (hA.eigenvectorBasis i) = (hA.eigenvalues i : ℂ) • hA.eigenvectorBasis i := by
  ext j
  have := hA.mulVec_eigenvectorBasis i
  simp only [Matrix.toLpLin_apply] at this ⊢
  exact congr_fun this j

/-- If (A + E) v = μ v for a Hermitian A with eigenvector basis uᵢ, then
    ‖E v‖² = Σᵢ (μ - λᵢ)² |⟨uᵢ, v⟩|². E need not be Hermitian. -/
theorem norm_sq_perturbation_eq_sum (A E : Matrix n n ℂ) (hA : A.IsHermitian)
    (v : EuclideanSpace ℂ n) (μ : ℝ) (hv : toEuclideanLin (A + E) v = (μ : ℂ) • v) :
    ‖toEuclideanLin E v‖ ^ 2 =
      ∑ i, (μ - hA.eigenvalues i) ^ 2 * ‖⟪hA.eigenvectorBasis i, v⟫‖ ^ 2 := by
  have hSym : (toEuclideanLin A).IsSymmetric := isSymmetric_toEuclideanLin_iff.mpr hA
  -- Coefficients of A x in the eigenbasis: ⟨uᵢ, A x⟩ = λᵢ ⟨uᵢ, x⟩
  have hcoefA : ∀ i x, ⟪hA.eigenvectorBasis i, toEuclideanLin A x⟫ =
      (hA.eigenvalues i : ℂ) * ⟪hA.eigenvectorBasis i, x⟫ := by
    intro i x
    rw [← hSym (hA.eigenvectorBasis i) x, toEuclideanLin_eigenvectorBasis hA i, inner_smul_left,
      Complex.conj_ofReal]
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
  -- Parseval in the eigenbasis
  rw [← hA.eigenvectorBasis.sum_sq_norm_inner_right (toEuclideanLin E v)]
  apply Finset.sum_congr rfl
  intro i _
  rw [hcoefE i, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]

end Eigenbasis

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
  -- ‖E v‖² = Σᵢ (μ - λᵢ)² |cᵢ|² with cᵢ = ⟨uᵢ, v⟩
  have hEv_sq := norm_sq_perturbation_eq_sum A E hA v μ hv
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
      ite_eq_left rfl, norm_zero, zero_pow two_ne_zero, zero_add]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hw_coef i, ite_eq_right (Finset.ne_of_mem_erase hi)]
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
  have : Nonempty n := Fintype.card_pos_iff.mp (Nat.lt_of_le_of_lt (Nat.zero_le _) j.isLt)
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
  have : Nonempty n := Fintype.card_pos_iff.mp (Nat.lt_of_le_of_lt (Nat.zero_le _) k.isLt)
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

/-! ## Top-k eigenspaces -/

section TopK

/-- The indices of the k largest eigenvalues: the images of the sorted indices 0, …, k - 1 under
    Mathlib's eigenvalue bijection. The set depends only on `n`, not on the matrix. -/
noncomputable def topIndices (k : ℕ) (hk : k < Fintype.card n) : Finset n :=
  (Finset.Iio (⟨k, hk⟩ : Fin (Fintype.card n))).map
    (Fintype.equivOfCardEq (Fintype.card_fin _) : Fin (Fintype.card n) ≃ n).toEmbedding

omit [DecidableEq n] in
/-- `topIndices k` has k elements. -/
theorem card_topIndices (k : ℕ) (hk : k < Fintype.card n) : (topIndices k hk).card = k := by
  have h := Fin.card_Iio (⟨k, hk⟩ : Fin (Fintype.card n))
  rw [topIndices, Finset.card_map]
  exact h

omit [DecidableEq n] in
/-- i ∈ `topIndices k` iff the sorted index of i is less than k. -/
theorem mem_topIndices {k : ℕ} {hk : k < Fintype.card n} {i : n} :
    i ∈ topIndices k hk ↔ ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm i).val < k := by
  rw [topIndices, Finset.mem_map_equiv, Finset.mem_Iio, Fin.lt_def]

/-- An eigenvalue whose index is not in `topIndices k` is at most λₖ. -/
theorem eigenvalues_le_of_not_mem_topIndices {A : Matrix n n ℂ} (hA : A.IsHermitian) {k : ℕ}
    (hk : k < Fintype.card n) {i : n} (hi : i ∉ topIndices k hk) :
    hA.eigenvalues i ≤ hA.eigenvalues₀ ⟨k, hk⟩ := by
  have h_le : k ≤ ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm i).val :=
    not_lt.mp (fun h => hi (mem_topIndices.mpr h))
  rw [CourantFischer.eigenvalues_eq_eigenvalues₀_comp A hA]
  exact hA.eigenvalues₀_antitone (Fin.le_def.mpr h_le)

/-- An eigenvalue whose index is in `topIndices k` is at least λₖ₋₁. -/
theorem le_eigenvalues_of_mem_topIndices {A : Matrix n n ℂ} (hA : A.IsHermitian) {k : ℕ}
    (hk : k < Fintype.card n) {i : n} (hi : i ∈ topIndices k hk) :
    hA.eigenvalues₀ ⟨k - 1, by omega⟩ ≤ hA.eigenvalues i := by
  have h_le : ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm i).val ≤ k - 1 :=
    Nat.le_sub_one_of_lt (mem_topIndices.mp hi)
  rw [CourantFischer.eigenvalues_eq_eigenvalues₀_comp A hA]
  exact hA.eigenvalues₀_antitone (Fin.le_def.mpr h_le)

/-- **Davis–Kahan sin θ bound for a top-k eigenspace, one vector at a time.** Let A be Hermitian
    with eigenvector basis uᵢ and (k+1)-th largest eigenvalue λₖ (0-indexed), and let v satisfy
    (A + E) v = μ v with μ > λₖ. With P v = Σ_{i ∈ topIndices k} ⟨uᵢ, v⟩ uᵢ the orthogonal
    projection onto the span of the eigenvectors for λ₀, …, λₖ₋₁,
    (μ - λₖ) ‖v - P v‖ ≤ ‖E‖₂ ‖v‖. E need not be Hermitian. -/
theorem davis_kahan_topIndices (A E : Matrix n n ℂ) (hA : A.IsHermitian) (k : ℕ)
    (hk : k < Fintype.card n) (v : EuclideanSpace ℂ n) (μ : ℝ)
    (hv : toEuclideanLin (A + E) v = (μ : ℂ) • v) (hμ : hA.eigenvalues₀ ⟨k, hk⟩ < μ) :
    (μ - hA.eigenvalues₀ ⟨k, hk⟩) *
        ‖v - ∑ i ∈ topIndices k hk, ⟪hA.eigenvectorBasis i, v⟫ • hA.eigenvectorBasis i‖ ≤
      ‖E‖ * ‖v‖ := by
  -- ‖E v‖² = Σᵢ (μ - λᵢ)² |cᵢ|² with cᵢ = ⟨uᵢ, v⟩
  have hEv_sq := norm_sq_perturbation_eq_sum A E hA v μ hv
  -- The residual w = v - P v has coefficients 0 on topIndices k and cᵢ off it
  obtain ⟨w, hw⟩ : ∃ w : EuclideanSpace ℂ n,
      w = v - ∑ i ∈ topIndices k hk, ⟪hA.eigenvectorBasis i, v⟫ • hA.eigenvectorBasis i :=
    ⟨_, rfl⟩
  rw [← hw]
  have hw_coef : ∀ i, ⟪hA.eigenvectorBasis i, w⟫ =
      if i ∈ topIndices k hk then 0 else ⟪hA.eigenvectorBasis i, v⟫ := by
    intro i
    have h_term : ∀ l ∈ topIndices k hk,
        ⟪hA.eigenvectorBasis i, ⟪hA.eigenvectorBasis l, v⟫ • hA.eigenvectorBasis l⟫ =
          if i = l then ⟪hA.eigenvectorBasis l, v⟫ else 0 := by
      intro l _
      rw [inner_smul_right, orthonormal_iff_ite.mp hA.eigenvectorBasis.orthonormal i l]
      split_ifs <;> ring
    rw [hw, inner_sub_right, inner_sum, Finset.sum_congr rfl h_term, Finset.sum_ite_eq]
    split_ifs <;> ring
  have hw_sq : ‖w‖ ^ 2 = ∑ i ∈ (topIndices k hk)ᶜ, ‖⟪hA.eigenvectorBasis i, v⟫‖ ^ 2 := by
    have h_in : ∑ i ∈ topIndices k hk, ‖⟪hA.eigenvectorBasis i, w⟫‖ ^ 2 = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [hw_coef i, ite_eq_left hi, norm_zero, zero_pow two_ne_zero]
    rw [← hA.eigenvectorBasis.sum_sq_norm_inner_right w,
      ← Finset.sum_add_sum_compl (topIndices k hk), h_in, zero_add]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hw_coef i, ite_eq_right (Finset.mem_compl.mp hi)]
  -- Off topIndices k, λᵢ ≤ λₖ, so (μ - λᵢ)² ≥ (μ - λₖ)²
  have h_gap_i : ∀ i ∈ (topIndices k hk)ᶜ,
      (μ - hA.eigenvalues₀ ⟨k, hk⟩) ^ 2 ≤ (μ - hA.eigenvalues i) ^ 2 := by
    intro i hi
    have h_le := eigenvalues_le_of_not_mem_topIndices hA hk (Finset.mem_compl.mp hi)
    exact pow_le_pow_left₀ (by linarith) (by linarith) 2
  have h_key : (μ - hA.eigenvalues₀ ⟨k, hk⟩) ^ 2 * ‖w‖ ^ 2 ≤ ‖toEuclideanLin E v‖ ^ 2 := by
    rw [hw_sq, Finset.mul_sum, hEv_sq]
    calc ∑ i ∈ (topIndices k hk)ᶜ,
          (μ - hA.eigenvalues₀ ⟨k, hk⟩) ^ 2 * ‖⟪hA.eigenvectorBasis i, v⟫‖ ^ 2
        ≤ ∑ i ∈ (topIndices k hk)ᶜ,
          (μ - hA.eigenvalues i) ^ 2 * ‖⟪hA.eigenvectorBasis i, v⟫‖ ^ 2 :=
          Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_right (h_gap_i i hi) (sq_nonneg _))
      _ ≤ ∑ i, (μ - hA.eigenvalues i) ^ 2 * ‖⟪hA.eigenvectorBasis i, v⟫‖ ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun i _ _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  -- ‖E v‖ ≤ ‖E‖₂ ‖v‖
  have h_op : ‖toEuclideanLin E v‖ ≤ ‖E‖ * ‖v‖ := Matrix.l2_opNorm_mulVec E v
  have h1 : (μ - hA.eigenvalues₀ ⟨k, hk⟩) * ‖w‖ ≤ ‖toEuclideanLin E v‖ := by
    refine le_of_sq_le_sq ?_ (norm_nonneg _)
    rw [mul_pow]
    exact h_key
  exact h1.trans h_op

/-- **Davis–Kahan for a top-k eigenspace in gap form, one vector at a time.** Let A be Hermitian
    with gap δ = λₖ₋₁ - λₖ > ‖E‖₂, and let v be a unit vector with (A + E) v = μ v for some
    μ ≥ λₖ₋₁ - ‖E‖₂. Then ‖v - P v‖ ≤ ‖E‖₂ / (δ - ‖E‖₂), with P as in `davis_kahan_topIndices`.
    (For k = 0 the index k - 1 is 0 in ℕ, so δ = 0 and the hypothesis cannot hold.) -/
theorem davis_kahan_topIndices_of_norm_lt_gap (A E : Matrix n n ℂ) (hA : A.IsHermitian) (k : ℕ)
    (hk : k < Fintype.card n) (v : EuclideanSpace ℂ n) (hv1 : ‖v‖ = 1) (μ : ℝ)
    (hv : toEuclideanLin (A + E) v = (μ : ℂ) • v)
    (hμ : hA.eigenvalues₀ ⟨k - 1, by omega⟩ - ‖E‖ ≤ μ)
    (h_small : ‖E‖ < hA.eigenvalues₀ ⟨k - 1, by omega⟩ - hA.eigenvalues₀ ⟨k, hk⟩) :
    ‖v - ∑ i ∈ topIndices k hk, ⟪hA.eigenvectorBasis i, v⟫ • hA.eigenvectorBasis i‖ ≤
      ‖E‖ / (hA.eigenvalues₀ ⟨k - 1, by omega⟩ - hA.eigenvalues₀ ⟨k, hk⟩ - ‖E‖) := by
  have hμk : hA.eigenvalues₀ ⟨k, hk⟩ < μ := by linarith
  have h_main := davis_kahan_topIndices A E hA k hk v μ hv hμk
  rw [hv1, mul_one] at h_main
  have h_den : 0 < hA.eigenvalues₀ ⟨k - 1, by omega⟩ - hA.eigenvalues₀ ⟨k, hk⟩ - ‖E‖ := by
    linarith
  rw [le_div_iff₀ h_den]
  calc ‖v - ∑ i ∈ topIndices k hk, ⟪hA.eigenvectorBasis i, v⟫ • hA.eigenvectorBasis i‖ *
        (hA.eigenvalues₀ ⟨k - 1, by omega⟩ - hA.eigenvalues₀ ⟨k, hk⟩ - ‖E‖)
      ≤ ‖v - ∑ i ∈ topIndices k hk, ⟪hA.eigenvectorBasis i, v⟫ • hA.eigenvectorBasis i‖ *
        (μ - hA.eigenvalues₀ ⟨k, hk⟩) :=
        mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
    _ = (μ - hA.eigenvalues₀ ⟨k, hk⟩) *
        ‖v - ∑ i ∈ topIndices k hk, ⟪hA.eigenvectorBasis i, v⟫ • hA.eigenvectorBasis i‖ :=
        mul_comm _ _
    _ ≤ ‖E‖ := h_main

/-- **Davis–Kahan sin Θ bound for the top-k eigenspace (Frobenius form).** Let A, E be
    Hermitian, k < n, and ‖E‖₂ < δ = λₖ₋₁(A) - λₖ(A) (which forces k ≥ 1). Let uᵢ and ũᵢ be the
    eigenvector bases of A and A + E, and P the orthogonal projection onto
    span {uᵢ : i ∈ topIndices k}. Then Σ_{j ∈ topIndices k} ‖ũⱼ - P ũⱼ‖² ≤ k (‖E‖₂ / (δ - ‖E‖₂))².
    The left side is ‖sin Θ‖_F² for the top-k eigenspaces of A and A + E. -/
theorem davis_kahan_sin_theta (A E : Matrix n n ℂ) (hA : A.IsHermitian) (hE : E.IsHermitian)
    (k : ℕ) (hk : k < Fintype.card n)
    (h_small : ‖E‖ < hA.eigenvalues₀ ⟨k - 1, by omega⟩ - hA.eigenvalues₀ ⟨k, hk⟩) :
    ∑ j ∈ topIndices k hk,
        ‖(hA.add hE).eigenvectorBasis j - ∑ i ∈ topIndices k hk,
          ⟪hA.eigenvectorBasis i, (hA.add hE).eigenvectorBasis j⟫ • hA.eigenvectorBasis i‖ ^ 2 ≤
      k * (‖E‖ / (hA.eigenvalues₀ ⟨k - 1, by omega⟩ - hA.eigenvalues₀ ⟨k, hk⟩ - ‖E‖)) ^ 2 := by
  have h_each : ∀ j ∈ topIndices k hk,
      ‖(hA.add hE).eigenvectorBasis j - ∑ i ∈ topIndices k hk,
          ⟪hA.eigenvectorBasis i, (hA.add hE).eigenvectorBasis j⟫ • hA.eigenvectorBasis i‖ ^ 2 ≤
        (‖E‖ / (hA.eigenvalues₀ ⟨k - 1, by omega⟩ - hA.eigenvalues₀ ⟨k, hk⟩ - ‖E‖)) ^ 2 := by
    intro j hj
    -- ũⱼ is a unit eigenvector of A + E with eigenvalue ≥ λₖ₋₁(A + E) ≥ λₖ₋₁(A) - ‖E‖₂
    have hv1 : ‖(hA.add hE).eigenvectorBasis j‖ = 1 :=
      (hA.add hE).eigenvectorBasis.orthonormal.1 j
    have hμ : hA.eigenvalues₀ ⟨k - 1, by omega⟩ - ‖E‖ ≤ (hA.add hE).eigenvalues j :=
      (eigenvalues₀_sub_norm_le_add hA hE ⟨k - 1, by omega⟩).trans
        (le_eigenvalues_of_mem_topIndices (hA.add hE) hk hj)
    have h := davis_kahan_topIndices_of_norm_lt_gap A E hA k hk _ hv1 _
      (toEuclideanLin_eigenvectorBasis (hA.add hE) j) hμ h_small
    exact pow_le_pow_left₀ (norm_nonneg _) h 2
  have h_sum := Finset.sum_le_sum h_each
  rw [Finset.sum_const, card_topIndices, nsmul_eq_mul] at h_sum
  exact h_sum

end TopK

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
    rw [dite_eq_left h2, h0]
  rw [h_gap, h_norm]
  have h1 := SVD.singularValues₀_nonneg A ⟨1, h2⟩
  have h01 : SVD.singularValues₀ A ⟨1, h2⟩ ≤ SVD.singularValues₀ A ⟨0, by omega⟩ :=
    SVD.singularValues₀_antitone A (Fin.le_def.mpr (Nat.zero_le _))
  nlinarith

/-- ‖Ãᴴ Ã - Aᴴ A‖₂ ≤ ‖Ã - A‖₂ (‖Ã‖₂ + ‖A‖₂), from Ãᴴ Ã - Aᴴ A = Ãᴴ (Ã - A) + (Ã - A)ᴴ A. -/
theorem norm_gram_sub_le (A Ã : Matrix n n ℂ) :
    ‖Ãᴴ * Ã - Aᴴ * A‖ ≤ ‖Ã - A‖ * (‖Ã‖ + ‖A‖) := by
  have h_split : Ãᴴ * Ã - Aᴴ * A = Ãᴴ * (Ã - A) + (Ã - A)ᴴ * A := by
    rw [conjTranspose_sub, Matrix.mul_sub, Matrix.sub_mul]
    abel
  have h_star : ∀ X : Matrix n n ℂ, ‖Xᴴ‖ = ‖X‖ := fun X => Matrix.l2_opNorm_conjTranspose X
  calc ‖Ãᴴ * Ã - Aᴴ * A‖ = ‖Ãᴴ * (Ã - A) + (Ã - A)ᴴ * A‖ := by rw [h_split]
    _ ≤ ‖Ãᴴ * (Ã - A)‖ + ‖(Ã - A)ᴴ * A‖ := norm_add_le _ _
    _ ≤ ‖Ãᴴ‖ * ‖Ã - A‖ + ‖(Ã - A)ᴴ‖ * ‖A‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = ‖Ã - A‖ * (‖Ã‖ + ‖A‖) := by rw [h_star, h_star]; ring

/-- **Perturbation of the top right singular vector, in ‖Ã - A‖₂ and the spectral gap.** Let
    η = ‖Ã - A‖₂ (‖Ã‖₂ + ‖A‖₂) and γ = `spectralGap A * ‖A‖₂` = (σ₀ - σ₁) σ₀. If η < γ and v is
    a unit eigenvector of Ãᴴ Ã for its largest eigenvalue, then ‖v - ⟨u₀, v⟩ u₀‖ ≤ η / (γ - η),
    where u₀ is the top eigenvector of Aᴴ A. For small ‖Ã - A‖₂ this is about
    2 ‖Ã - A‖₂ / (σ₀ - σ₁), twice Wedin's bound. -/
theorem top_right_singular_vector_perturbation_of_spectralGap [Nonempty n] (A Ã : Matrix n n ℂ)
    (h2 : 1 < Fintype.card n) (v : EuclideanSpace ℂ n) (hv1 : ‖v‖ = 1)
    (hv : toEuclideanLin (Ãᴴ * Ã) v =
      ((posSemidef_conjTranspose_mul_self Ã).isHermitian.eigenvalues₀ ⟨0, by omega⟩ : ℂ) • v)
    (h_small : ‖Ã - A‖ * (‖Ã‖ + ‖A‖) < Coherence.spectralGap A * ‖A‖) :
    ‖v - ⟪(posSemidef_conjTranspose_mul_self A).isHermitian.eigenvectorBasis (topIndex h2), v⟫ •
        (posSemidef_conjTranspose_mul_self A).isHermitian.eigenvectorBasis (topIndex h2)‖ ≤
      ‖Ã - A‖ * (‖Ã‖ + ‖A‖) / (Coherence.spectralGap A * ‖A‖ - ‖Ã - A‖ * (‖Ã‖ + ‖A‖)) := by
  have hF := norm_gram_sub_le A Ã
  have hγ := spectralGap_mul_norm_le_sq_sub_sq A h2
  have h_small' : ‖Ãᴴ * Ã - Aᴴ * A‖ <
      SVD.singularValues₀ A ⟨0, by omega⟩ ^ 2 - SVD.singularValues₀ A ⟨1, h2⟩ ^ 2 := by
    linarith
  have h := top_right_singular_vector_perturbation A Ã h2 v hv1 hv h_small'
  exact h.trans (div_le_div₀ (by positivity) hF (by linarith) (by linarith))

end SingularVector

end Matrix.DavisKahan
