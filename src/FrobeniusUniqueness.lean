/-
Copyright (c) 2025 FLYWHEEL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aleksandar Markovski
-/
import TightBounds

/-!
# Uniqueness of the best rank-k approximation in the Frobenius norm

Eckart–Young says that the truncated SVD is *a* best rank-k approximation. In the Frobenius
norm it is the *only* one when the singular values have a gap σₖ₋₁ > σₖ (0-indexed):

- `eckart_young_frobenius_unique` (square): if rank B ≤ k and ‖A - B‖_F ≤ ‖A - Aₖ‖_F, then
  B = `Matrix.SVD.truncatedSVD A k`;
- `eckart_young_frobenius_rect_unique`: the same for rectangular A and
  `Matrix.TightBounds.truncatedSVD_rect`;
- `kroneckerApprox_unique` (Van Loan–Pitsianis): if σ₀(R C) > σ₁(R C), every Kronecker product
  A ⊗ B that is a best Kronecker approximation of C equals `Matrix.TightBounds.kroneckerApprox C`.
  The factors A, B themselves are not unique (A ⊗ B = (cA) ⊗ (c⁻¹B)).

In the spectral norm optima are not unique (`Matrix.SVD.spectral_best_rank_one_not_unique`).

## Proof

Work in the SVD basis, A = U S Vᴴ with SᴴS = diag(d), dⱼ = σⱼ². For C = Uᴴ B V let Q be the
orthogonal projection onto the row space of C (`exists_rowSpace_projection`; C Q = C and
tr Q = rank C). Then
- ‖S - C‖² = ‖S (1 - Q)‖² + ‖S Q - C‖² (Pythagoras: the cross terms vanish because C Q = C);
- ‖S (1 - Q)‖² = Σⱼ dⱼ - Σⱼ dⱼ wⱼ with wⱼ = Re Qⱼⱼ ∈ [0, 1] and Σⱼ wⱼ = rank C ≤ k
  (`frobenius_sq_mul_one_sub_proj`);
- Σⱼ dⱼ wⱼ ≤ Σ_{j ∈ T} dⱼ for the index set T of the k largest dⱼ, with equality only for
  w = 1_T when the dⱼ in T are strictly larger than those outside
  (`sum_mul_le_sum_of_threshold`).
So the error is at least Σ_{j ∉ T} dⱼ, and attaining it forces w = 1_T, hence Q = diag(1_T), and
S Q = C, i.e. C = S diag(1_T), the truncation (`eq_mul_indicator_of_frobenius_sq_le`). No
eigenvalue interlacing is needed.
-/

open scoped ComplexOrder Matrix
open Matrix

namespace Matrix.FrobeniusUniqueness

/-! ## A weighted sum bounded by its top part -/

section WeightedSum

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Weighted top sum.** Let 0 ≤ wᵢ ≤ 1 with Σᵢ wᵢ ≤ #T, and let τ ≥ 0 separate T from its
    complement: sᵢ > τ for i ∈ T and sᵢ < τ for i ∉ T. Then Σᵢ sᵢ wᵢ ≤ Σ_{i ∈ T} sᵢ, and
    equality forces w to be the indicator of T.

    Proof: Σ_{i ∈ T} sᵢ - Σᵢ sᵢ wᵢ = Σᵢ (sᵢ - τ)(1_T(i) - wᵢ) + τ (#T - Σᵢ wᵢ), a sum of
    nonnegative terms that vanishes only when every wᵢ = 1_T(i). -/
theorem sum_mul_le_sum_of_threshold (s w : ι → ℝ) (T : Finset ι) (τ : ℝ) (hτ : 0 ≤ τ)
    (hT : ∀ i ∈ T, τ < s i) (hTc : ∀ i ∉ T, s i < τ)
    (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∀ i, w i ≤ 1) (hw : ∑ i, w i ≤ T.card) :
    ∑ i, s i * w i ≤ ∑ i ∈ T, s i ∧
      (∑ i, s i * w i = ∑ i ∈ T, s i → ∀ i, w i = if i ∈ T then 1 else 0) := by
  -- The indicator of T, its sum and the T-sum of s
  have h_sum_e : ∑ i, (if i ∈ T then (1 : ℝ) else 0) = T.card := by
    rw [Fintype.sum_ite_mem, Finset.sum_const, nsmul_eq_mul, mul_one]
  have h_T : ∑ i ∈ T, s i = ∑ i, s i * (if i ∈ T then (1 : ℝ) else 0) := by
    simp only [mul_ite, mul_one, mul_zero, Fintype.sum_ite_mem]
  -- Each term (sᵢ - τ)(1_T(i) - wᵢ) is nonnegative
  have h_term : ∀ i, 0 ≤ (s i - τ) * ((if i ∈ T then (1 : ℝ) else 0) - w i) := by
    intro i
    by_cases hi : i ∈ T
    · rw [if_pos hi]
      exact mul_nonneg (by linarith [hT i hi]) (by linarith [hw1 i])
    · rw [if_neg hi]
      exact mul_nonneg_of_nonpos_of_nonpos (by linarith [hTc i hi]) (by linarith [hw0 i])
  -- The gap identity
  have h_key : ∑ i, s i * (if i ∈ T then (1 : ℝ) else 0) - ∑ i, s i * w i =
      ∑ i, (s i - τ) * ((if i ∈ T then (1 : ℝ) else 0) - w i) +
        τ * (∑ i, (if i ∈ T then (1 : ℝ) else 0) - ∑ i, w i) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have h_nonneg : 0 ≤ ∑ i, (s i - τ) * ((if i ∈ T then (1 : ℝ) else 0) - w i) :=
    Finset.sum_nonneg (fun i _ => h_term i)
  have h_slack : 0 ≤ τ * (∑ i, (if i ∈ T then (1 : ℝ) else 0) - ∑ i, w i) :=
    mul_nonneg hτ (by rw [h_sum_e]; linarith)
  refine ⟨?_, ?_⟩
  · rw [h_T]
    linarith
  · intro h_eq i
    -- every term of the gap identity vanishes
    have h_zero : ∑ i, (s i - τ) * ((if i ∈ T then (1 : ℝ) else 0) - w i) = 0 := by
      rw [h_T] at h_eq
      linarith
    have h_each := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => h_term i)).mp h_zero i
      (Finset.mem_univ i)
    have h_ne : s i - τ ≠ 0 := by
      by_cases hi : i ∈ T
      · exact (sub_pos.mpr (hT i hi)).ne'
      · exact (sub_neg.mpr (hTc i hi)).ne
    have h_diff := (mul_eq_zero.mp h_each).resolve_left h_ne
    linarith

end WeightedSum

/-! ## The orthogonal projection onto the row space -/

section RowSpaceProjection

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- **Row-space projection.** Every C : Matrix m n ℂ has a Hermitian idempotent Q with C Q = C
    and tr Q = rank C: Q = W diag(1_{λᵢ ≠ 0}) Wᴴ from the spectral decomposition
    Cᴴ C = W diag(λ) Wᴴ. -/
theorem exists_rowSpace_projection (C : Matrix m n ℂ) :
    ∃ Q : Matrix n n ℂ, Qᴴ = Q ∧ Q * Q = Q ∧ C * Q = C ∧ (trace Q).re = C.rank := by
  classical
  have hH : (Cᴴ * C).IsHermitian := (posSemidef_conjTranspose_mul_self C).isHermitian
  let W : Matrix n n ℂ := (hH.eigenvectorUnitary : Matrix n n ℂ)
  have hWW : star W * W = 1 := mem_unitaryGroup_iff'.mp hH.eigenvectorUnitary.2
  let ε : n → ℂ := fun i => if hH.eigenvalues i = 0 then 0 else 1
  -- Cᴴ C = W diag(λ) Wᴴ
  have h_spec : Cᴴ * C = W * diagonal (Complex.ofReal ∘ hH.eigenvalues) * star W :=
    hH.spectral_theorem
  have hεε : diagonal ε * diagonal ε = diagonal ε := by
    rw [diagonal_mul_diagonal]
    congr 1
    funext i
    by_cases h : hH.eigenvalues i = 0 <;> simp [ε, h]
  have hεΛ : diagonal ε * diagonal (Complex.ofReal ∘ hH.eigenvalues) =
      diagonal (Complex.ofReal ∘ hH.eigenvalues) := by
    rw [diagonal_mul_diagonal]
    congr 1
    funext i
    by_cases h : hH.eigenvalues i = 0 <;> simp [ε, h]
  -- Q = W diag(ε) Wᴴ, kept opaque so that `simp` does not reassociate it
  obtain ⟨Q, hQ_def⟩ : ∃ Q : Matrix n n ℂ, Q = W * diagonal ε * star W := ⟨_, rfl⟩
  have hQh : Qᴴ = Q := by
    -- ε is real
    have hε : star ε = ε := by
      funext i
      by_cases h : hH.eigenvalues i = 0 <;> simp [ε, h]
    rw [hQ_def, conjTranspose_mul, conjTranspose_mul, star_eq_conjTranspose,
      conjTranspose_conjTranspose, diagonal_conjTranspose, hε, Matrix.mul_assoc]
  have hQQ : Q * Q = Q := by
    -- ε² = ε
    rw [hQ_def]
    calc W * diagonal ε * star W * (W * diagonal ε * star W)
        = W * (diagonal ε * (star W * W) * diagonal ε) * star W := by
          simp only [Matrix.mul_assoc]
      _ = W * diagonal ε * star W := by
          rw [hWW, Matrix.mul_one, hεε]
  -- Q (Cᴴ C) = Cᴴ C, since ε λ = λ
  have hQH : Q * (Cᴴ * C) = Cᴴ * C := by
    rw [hQ_def, h_spec]
    calc W * diagonal ε * star W * (W * diagonal (Complex.ofReal ∘ hH.eigenvalues) * star W)
        = W * (diagonal ε * (star W * W) * diagonal (Complex.ofReal ∘ hH.eigenvalues)) *
            star W := by
          simp only [Matrix.mul_assoc]
      _ = W * diagonal (Complex.ofReal ∘ hH.eigenvalues) * star W := by
          rw [hWW, Matrix.mul_one, hεΛ]
  refine ⟨Q, hQh, hQQ, ?_, ?_⟩
  · -- C Q = C: (C - C Q)ᴴ (C - C Q) = 0
    have hHQ : Cᴴ * C * Q = Cᴴ * C := by
      have h := congrArg conjTranspose hQH
      rwa [conjTranspose_mul, hQh, hH.eq] at h
    have hHQ' : Cᴴ * (C * Q) = Cᴴ * C := by
      rw [← Matrix.mul_assoc, hHQ]
    have hX : (C - C * Q)ᴴ * (C - C * Q) = 0 := by
      have h1 : (C - C * Q)ᴴ = Cᴴ - Q * Cᴴ := by
        rw [conjTranspose_sub, conjTranspose_mul, hQh]
      rw [h1]
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc, hHQ', hQH, sub_self]
    have h0 := Matrix.conjTranspose_mul_self_eq_zero.mp hX
    exact (sub_eq_zero.mp h0).symm
  · -- tr Q = #{λᵢ ≠ 0} = rank (Cᴴ C) = rank C
    have h_trQ : trace Q = trace (diagonal ε) := by
      rw [hQ_def, trace_mul_comm, ← Matrix.mul_assoc, hWW, Matrix.one_mul]
    rw [h_trQ, trace_diagonal, Complex.re_sum, ← rank_conjTranspose_mul_self C,
      hH.rank_eq_card_non_zero_eigs, Fintype.card_subtype, Finset.card_filter, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : hH.eigenvalues i = 0 <;> simp [ε, h]

end RowSpaceProjection

/-! ## The core lemma, in the SVD basis -/

section Core

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

attribute [local instance] Matrix.frobeniusSeminormedAddCommGroup

omit [DecidableEq n] in
/-- ‖X‖_F² = Re tr(Xᴴ X). -/
private lemma frob_sq (X : Matrix m n ℂ) : ‖X‖ ^ 2 = (trace (Xᴴ * X)).re :=
  FrobeniusNorm.frobenius_norm_sq_eq_trace X

omit [DecidableEq n] in
/-- A matrix with Frobenius norm 0 is 0. -/
private lemma eq_zero_of_frob_eq_zero {X : Matrix m n ℂ} (h : ‖X‖ = 0) : X = 0 :=
  (@norm_eq_zero (Matrix m n ℂ) Matrix.frobeniusNormedAddCommGroup.toNormedAddGroup X).mp h

/-- **Error of cutting S by a projection.** If SᴴS = diag(d) and Q is Hermitian idempotent, then
    ‖S (1 - Q)‖_F² = Σⱼ dⱼ - Σⱼ dⱼ Re Qⱼⱼ. -/
theorem frobenius_sq_mul_one_sub_proj (S : Matrix m n ℂ) (d : n → ℝ)
    (hSS : Sᴴ * S = diagonal (fun j => (d j : ℂ))) (Q : Matrix n n ℂ) (hQh : Qᴴ = Q)
    (hQQ : Q * Q = Q) :
    ‖S * (1 - Q)‖ ^ 2 = ∑ j, d j - ∑ j, d j * (Q j j).re := by
  have h1Q : (1 - Q)ᴴ = 1 - Q := by rw [conjTranspose_sub, conjTranspose_one, hQh]
  have h1Q1Q : (1 - Q) * (1 - Q) = 1 - Q := by
    simp only [sub_mul, mul_sub, one_mul, mul_one, hQQ, sub_self, sub_zero]
  have h_mat : (S * (1 - Q))ᴴ * (S * (1 - Q)) =
      (1 - Q) * (diagonal (fun j => (d j : ℂ)) * (1 - Q)) := by
    rw [conjTranspose_mul, h1Q, Matrix.mul_assoc, ← Matrix.mul_assoc Sᴴ S, hSS]
  have h_tr : trace ((S * (1 - Q))ᴴ * (S * (1 - Q))) =
      trace (diagonal (fun j => (d j : ℂ))) - trace (diagonal (fun j => (d j : ℂ)) * Q) := by
    rw [h_mat, trace_mul_comm, Matrix.mul_assoc, h1Q1Q, Matrix.mul_sub, Matrix.mul_one, trace_sub]
  rw [frob_sq, h_tr, Complex.sub_re, trace_diagonal, Complex.re_sum]
  simp only [trace, diag_apply, diagonal_mul, Complex.re_sum, Complex.re_ofReal_mul,
    Complex.ofReal_re]

/-- **Core uniqueness lemma.** Let SᴴS = diag(d) with d ≥ 0, and let T be a set of indices whose
    dⱼ are strictly larger than those outside T. If rank C ≤ #T and
    ‖S - C‖_F² ≤ Σ_{j ∉ T} dⱼ, then C = S diag(1_T): C is the truncation of S to the columns in
    T. -/
theorem eq_mul_indicator_of_frobenius_sq_le (S C : Matrix m n ℂ) (d : n → ℝ)
    (hd : ∀ j, 0 ≤ d j) (hSS : Sᴴ * S = diagonal (fun j => (d j : ℂ)))
    (T : Finset n) (h_gap : ∀ i ∈ T, ∀ j ∉ T, d j < d i) (hC : C.rank ≤ T.card)
    (h_le : ‖S - C‖ ^ 2 ≤ ∑ j ∈ Tᶜ, d j) :
    C = S * diagonal (fun j => if j ∈ T then (1 : ℂ) else 0) := by
  -- Case T = univ: the error bound is 0, so C = S
  by_cases hTc : Tᶜ = ∅
  · have h0 : ‖S - C‖ ^ 2 ≤ 0 := by
      rw [hTc, Finset.sum_empty] at h_le
      exact h_le
    have h_norm : ‖S - C‖ = 0 := le_antisymm (by nlinarith [norm_nonneg (S - C)]) (norm_nonneg _)
    have hSC : S - C = 0 := eq_zero_of_frob_eq_zero h_norm
    have hT_all : ∀ j, j ∈ T := fun j => by
      by_contra hj
      have hjc : j ∈ Tᶜ := Finset.mem_compl.mpr hj
      rw [hTc] at hjc
      exact Finset.notMem_empty j hjc
    have hE : diagonal (fun j => if j ∈ T then (1 : ℂ) else 0) = 1 := by
      simp [hT_all]
    rw [hE, Matrix.mul_one]
    exact (sub_eq_zero.mp hSC).symm
  have hTc_ne : Tᶜ.Nonempty := Finset.nonempty_iff_ne_empty.mpr hTc
  obtain ⟨Q, hQh, hQQ, hCQ, hQtr⟩ := exists_rowSpace_projection C
  -- Pythagoras: ‖S - C‖² = ‖S (1 - Q)‖² + ‖S Q - C‖²
  have h_pyth : ‖S - C‖ ^ 2 = ‖S * (1 - Q)‖ ^ 2 + ‖S * Q - C‖ ^ 2 := by
    have h1Q : (1 - Q)ᴴ = 1 - Q := by rw [conjTranspose_sub, conjTranspose_one, hQh]
    have hQQ' : Q * (Q * Sᴴ) = Q * Sᴴ := by rw [← Matrix.mul_assoc, hQQ]
    have hCQ' : C * (Q * Sᴴ) = C * Sᴴ := by rw [← Matrix.mul_assoc, hCQ]
    have hYX : (S * Q - C) * (S * (1 - Q))ᴴ = 0 := by
      rw [conjTranspose_mul, h1Q]
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_assoc, hQQ', hCQ',
        sub_self]
    have hXY : (S * (1 - Q)) * (S * Q - C)ᴴ = 0 := by
      have h := congrArg conjTranspose hYX
      rwa [conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_zero] at h
    have h_split : S - C = S * (1 - Q) + (S * Q - C) := by
      rw [Matrix.mul_sub, Matrix.mul_one]
      abel
    rw [h_split, frob_sq, frob_sq, frob_sq, conjTranspose_add, Matrix.add_mul, Matrix.mul_add,
      Matrix.mul_add, trace_add, trace_add, trace_add,
      trace_mul_comm (S * (1 - Q))ᴴ (S * Q - C), trace_mul_comm (S * Q - C)ᴴ (S * (1 - Q)), hYX,
      hXY, trace_zero, add_zero, zero_add, Complex.add_re]
  have h_X := frobenius_sq_mul_one_sub_proj S d hSS Q hQh hQQ
  -- The weights wⱼ = Re Qⱼⱼ: Qⱼⱼ = Σᵢ |Qᵢⱼ|², so 0 ≤ wⱼ ≤ 1
  have h_re : ∀ z : ℂ, (star z * z).re = Complex.normSq z := fun z => by
    rw [Complex.normSq_apply]
    simp only [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  have h_im : ∀ z : ℂ, (star z * z).im = 0 := fun z => by
    simp only [Complex.star_def, Complex.mul_im, Complex.conj_re, Complex.conj_im]
    ring
  have hQcol : ∀ j, Q j j = ∑ i, star (Q i j) * Q i j := by
    intro j
    have h : Qᴴ * Q = Q := by rw [hQh, hQQ]
    calc Q j j = (Qᴴ * Q) j j := by rw [h]
      _ = ∑ i, star (Q i j) * Q i j := by simp [mul_apply, conjTranspose_apply]
  have hw_sum : ∀ j, (Q j j).re = ∑ i, Complex.normSq (Q i j) := by
    intro j
    rw [hQcol j, Complex.re_sum]
    simp only [h_re]
  have hw0 : ∀ j, 0 ≤ (Q j j).re := fun j => by
    rw [hw_sum j]
    exact Finset.sum_nonneg (fun i _ => Complex.normSq_nonneg _)
  have hQjj_im : ∀ j, (Q j j).im = 0 := fun j => by
    rw [hQcol j, Complex.im_sum]
    exact Finset.sum_eq_zero (fun i _ => h_im _)
  have hw1 : ∀ j, (Q j j).re ≤ 1 := fun j => by
    have h_single : Complex.normSq (Q j j) ≤ (Q j j).re := by
      rw [hw_sum j]
      exact Finset.single_le_sum (fun i _ => Complex.normSq_nonneg (Q i j)) (Finset.mem_univ j)
    rw [Complex.normSq_apply, hQjj_im j, mul_zero, add_zero] at h_single
    nlinarith [hw0 j]
  have hw_total : ∑ j, (Q j j).re ≤ T.card := by
    have h : ∑ j, (Q j j).re = (trace Q).re := by
      simp only [trace, diag_apply, Complex.re_sum]
    rw [h, hQtr]
    exact_mod_cast hC
  -- A threshold strictly between the values on T and off T
  obtain ⟨j₀, hj₀, hbj₀⟩ := Finset.exists_mem_eq_sup' hTc_ne d
  have hdb : ∀ j ∉ T, d j ≤ d j₀ := fun j hj =>
    (Finset.le_sup' d (Finset.mem_compl.mpr hj)).trans_eq hbj₀
  obtain ⟨τ, hτ0, hτT, hτTc⟩ :
      ∃ τ : ℝ, 0 ≤ τ ∧ (∀ i ∈ T, τ < d i) ∧ (∀ j ∉ T, d j < τ) := by
    by_cases hT : T.Nonempty
    · obtain ⟨i₀, hi₀, hai₀⟩ := Finset.exists_mem_eq_inf' hT d
      have hdi : ∀ i ∈ T, d i₀ ≤ d i := fun i hi => hai₀.symm.trans_le (Finset.inf'_le d hi)
      have hgap0 : d j₀ < d i₀ := h_gap i₀ hi₀ j₀ (Finset.mem_compl.mp hj₀)
      refine ⟨(d i₀ + d j₀) / 2, by linarith [hd j₀], fun i hi => ?_, fun j hj => ?_⟩
      · linarith [hdi i hi]
      · linarith [hdb j hj]
    · exact ⟨d j₀ + 1, by linarith [hd j₀], fun i hi => absurd ⟨i, hi⟩ hT,
        fun j hj => by linarith [hdb j hj]⟩
  have hks := sum_mul_le_sum_of_threshold d (fun j => (Q j j).re) T τ hτ0 hτT hτTc hw0 hw1
    hw_total
  have h_ks1 : ∑ j, d j * (Q j j).re ≤ ∑ j ∈ T, d j := hks.1
  -- Both the error excess and ‖S Q - C‖² vanish
  have h_total : ∑ j, d j = ∑ j ∈ T, d j + ∑ j ∈ Tᶜ, d j := (Finset.sum_add_sum_compl T d).symm
  have h_Y_nonneg : 0 ≤ ‖S * Q - C‖ ^ 2 := sq_nonneg _
  rw [h_pyth, h_X] at h_le
  have hY_sq : ‖S * Q - C‖ ^ 2 = 0 := by linarith
  have h_eq : ∑ j, d j * (Q j j).re = ∑ j ∈ T, d j := by linarith
  have hw_eq : ∀ j, (Q j j).re = if j ∈ T then 1 else 0 := hks.2 h_eq
  have hY : S * Q - C = 0 := eq_zero_of_frob_eq_zero ((pow_eq_zero_iff two_ne_zero).mp hY_sq)
  -- w = 1_T forces Q = diag(1_T)
  have hQE : Q = diagonal (fun j => if j ∈ T then (1 : ℂ) else 0) := by
    ext i j
    rw [diagonal_apply]
    by_cases hj : j ∈ T
    · have hwj : (Q j j).re = 1 := by rw [hw_eq j, if_pos hj]
      have hQjj : Q j j = 1 := Complex.ext (by simpa using hwj) (by simpa using hQjj_im j)
      have h_rest : ∑ l ∈ Finset.univ.erase j, Complex.normSq (Q l j) = 0 := by
        have h_split : Complex.normSq (Q j j) +
            ∑ l ∈ Finset.univ.erase j, Complex.normSq (Q l j) = ∑ l, Complex.normSq (Q l j) :=
          Finset.add_sum_erase Finset.univ (fun l => Complex.normSq (Q l j)) (Finset.mem_univ j)
        rw [hQjj, Complex.normSq_one] at h_split
        linarith [hw_sum j]
      by_cases hij : i = j
      · subst hij
        simp [hj, hQjj]
      · have h0 := (Finset.sum_eq_zero_iff_of_nonneg
          (fun l _ => Complex.normSq_nonneg (Q l j))).mp h_rest i
          (Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩)
        rw [if_neg hij]
        exact Complex.normSq_eq_zero.mp h0
    · have hwj : (Q j j).re = 0 := by rw [hw_eq j, if_neg hj]
      have h0 := (Finset.sum_eq_zero_iff_of_nonneg
        (fun l _ => Complex.normSq_nonneg (Q l j))).mp ((hw_sum j).symm.trans hwj) i
        (Finset.mem_univ i)
      rw [Complex.normSq_eq_zero.mp h0]
      by_cases hij : i = j
      · subst hij
        simp [hj]
      · simp [hij]
  calc C = S * Q := (sub_eq_zero.mp hY).symm
    _ = S * diagonal (fun j => if j ∈ T then (1 : ℂ) else 0) := by rw [hQE]

end Core

/-! ## Uniqueness in a given SVD basis -/

section SVDBasis

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

attribute [local instance] Matrix.frobeniusSeminormedAddCommGroup

/-- **Uniqueness for a given decomposition A = U S Vᴴ.** Let U, V be unitary, SᴴS = diag(d) with
    d ≥ 0, and T a set of indices with dⱼ < dᵢ for i ∈ T, j ∉ T. Every B with rank B ≤ #T and
    ‖A - B‖_F ≤ ‖A - U (S diag(1_T)) Vᴴ‖_F equals U (S diag(1_T)) Vᴴ. -/
theorem eq_of_frobenius_le_of_svd (A : Matrix m n ℂ) (U : unitaryGroup m ℂ)
    (V : unitaryGroup n ℂ) (S : Matrix m n ℂ)
    (hA : A = (U : Matrix m m ℂ) * S * star (V : Matrix n n ℂ))
    (d : n → ℝ) (hd : ∀ j, 0 ≤ d j) (hSS : Sᴴ * S = diagonal (fun j => (d j : ℂ)))
    (T : Finset n) (h_gap : ∀ i ∈ T, ∀ j ∉ T, d j < d i)
    (B : Matrix m n ℂ) (hB : B.rank ≤ T.card)
    (h_opt : ‖A - B‖ ≤ ‖A - (U : Matrix m m ℂ) *
      (S * diagonal (fun j => if j ∈ T then (1 : ℂ) else 0)) * star (V : Matrix n n ℂ)‖) :
    B = (U : Matrix m m ℂ) * (S * diagonal (fun j => if j ∈ T then (1 : ℂ) else 0)) *
      star (V : Matrix n n ℂ) := by
  have hUU' : (U : Matrix m m ℂ) * star (U : Matrix m m ℂ) = 1 := mem_unitaryGroup_iff.mp U.2
  have hVV' : (V : Matrix n n ℂ) * star (V : Matrix n n ℂ) = 1 := mem_unitaryGroup_iff.mp V.2
  -- C = Uᴴ B V, so B = U C Vᴴ and rank C = rank B
  have hB_eq : B = (U : Matrix m m ℂ) * (star (U : Matrix m m ℂ) * B * (V : Matrix n n ℂ)) *
      star (V : Matrix n n ℂ) := by
    simp only [← Matrix.mul_assoc, hUU', Matrix.one_mul]
    rw [Matrix.mul_assoc, hVV', Matrix.mul_one]
  have hCrank : (star (U : Matrix m m ℂ) * B * (V : Matrix n n ℂ)).rank ≤ T.card := by
    have h_det : IsUnit (star (U : Matrix m m ℂ)).det := by
      rw [star_eq_conjTranspose, det_conjTranspose]
      exact (UnitaryGroup.det_isUnit U).star
    rw [rank_mul_eq_left_of_isUnit_det _ _ (UnitaryGroup.det_isUnit V),
      rank_mul_eq_right_of_isUnit_det _ _ h_det]
    exact hB
  -- Both errors in the SVD basis
  have h_AB : ‖A - B‖ = ‖S - star (U : Matrix m m ℂ) * B * (V : Matrix n n ℂ)‖ := by
    conv_lhs => rw [hB_eq, hA, ← Matrix.sub_mul, ← Matrix.mul_sub]
    exact TightBounds.frobenius_norm_unitary_conj_rect U V _
  have h_AT : ‖A - (U : Matrix m m ℂ) *
      (S * diagonal (fun j => if j ∈ T then (1 : ℂ) else 0)) * star (V : Matrix n n ℂ)‖ =
      ‖S - S * diagonal (fun j => if j ∈ T then (1 : ℂ) else 0)‖ := by
    rw [hA, ← Matrix.sub_mul, ← Matrix.mul_sub]
    exact TightBounds.frobenius_norm_unitary_conj_rect U V _
  -- The error of the truncation is Σ_{j ∉ T} dⱼ
  have h_err : ‖S - S * diagonal (fun j => if j ∈ T then (1 : ℂ) else 0)‖ ^ 2 =
      ∑ j ∈ Tᶜ, d j := by
    have hEh : (diagonal (fun j => if j ∈ T then (1 : ℂ) else 0))ᴴ =
        diagonal (fun j => if j ∈ T then (1 : ℂ) else 0) := by
      rw [diagonal_conjTranspose]
      congr 1
      funext j
      by_cases h : j ∈ T <;> simp [h]
    have hEE : diagonal (fun j => if j ∈ T then (1 : ℂ) else 0) *
        diagonal (fun j => if j ∈ T then (1 : ℂ) else 0) =
        diagonal (fun j => if j ∈ T then (1 : ℂ) else 0) := by
      rw [diagonal_mul_diagonal]
      congr 1
      funext j
      by_cases h : j ∈ T <;> simp [h]
    have h1 : S - S * diagonal (fun j => if j ∈ T then (1 : ℂ) else 0) =
        S * (1 - diagonal (fun j => if j ∈ T then (1 : ℂ) else 0)) := by
      rw [Matrix.mul_sub, Matrix.mul_one]
    have h2 : ∑ j, d j * ((diagonal (fun j => if j ∈ T then (1 : ℂ) else 0)) j j).re =
        ∑ j ∈ T, d j := by
      rw [← Fintype.sum_ite_mem T d]
      apply Finset.sum_congr rfl
      intro j _
      by_cases h : j ∈ T <;> simp [h]
    rw [h1, frobenius_sq_mul_one_sub_proj S d hSS _ hEh hEE, h2,
      ← Finset.sum_add_sum_compl T d]
    ring
  have h_le : ‖S - star (U : Matrix m m ℂ) * B * (V : Matrix n n ℂ)‖ ^ 2 ≤ ∑ j ∈ Tᶜ, d j := by
    rw [← h_err, ← h_AB, ← h_AT]
    exact pow_le_pow_left₀ (norm_nonneg _) h_opt 2
  have hC_eq := eq_mul_indicator_of_frobenius_sq_le S _ d hd hSS T h_gap hCrank h_le
  rw [hB_eq, hC_eq]

end SVDBasis

/-! ## Square matrices -/

section Square

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The Frobenius norm, written out because square matrices carry the L2 norm by default here. -/
local notation "‖" A "‖_F" => @Norm.norm _ Matrix.frobeniusSeminormedAddCommGroup.toNorm A

/-- **Uniqueness of the Frobenius-optimal rank-k approximation (square).** If the singular values
    have a gap σₖ₋₁ > σₖ (0-indexed, 0 < k < n), then every B with rank B ≤ k and
    ‖A - B‖_F ≤ ‖A - truncatedSVD A k‖_F equals `truncatedSVD A k`. -/
theorem eckart_young_frobenius_unique (A : Matrix n n ℂ) (k : ℕ) (hk : k < Fintype.card n)
    (h_gap : SVD.singularValues₀ A ⟨k, hk⟩ < SVD.singularValues₀ A ⟨k - 1, by omega⟩)
    (B : Matrix n n ℂ) (hB : B.rank ≤ k)
    (h_opt : ‖A - B‖_F ≤ ‖A - SVD.truncatedSVD A k‖_F) :
    B = SVD.truncatedSVD A k := by
  -- The SVD A = U S Vᴴ with S = diag(σ)
  have hA : A = (SVD.constructedU A : Matrix n n ℂ) *
      diagonal (Complex.ofReal ∘ SVD.singularValues A) *
      star (SVD.rightUnitary A : Matrix n n ℂ) := by
    have h_AV := SVD.AV_eq_constructedU_mul_sigma A
    have hVV : (SVD.rightUnitary A : Matrix n n ℂ) * star (SVD.rightUnitary A : Matrix n n ℂ) = 1 :=
      mem_unitaryGroup_iff.mp (SVD.rightUnitary A).2
    calc A = A * ((SVD.rightUnitary A : Matrix n n ℂ) * star (SVD.rightUnitary A : Matrix n n ℂ)) := by
          rw [hVV, Matrix.mul_one]
      _ = A * (SVD.rightUnitary A : Matrix n n ℂ) * star (SVD.rightUnitary A : Matrix n n ℂ) := by
          rw [Matrix.mul_assoc]
      _ = _ := by rw [h_AV]
  -- SᴴS = diag(σ²)
  have hSS : (diagonal (Complex.ofReal ∘ SVD.singularValues A))ᴴ *
      diagonal (Complex.ofReal ∘ SVD.singularValues A) =
      diagonal (fun j => ((SVD.singularValues A j ^ 2 : ℝ) : ℂ)) := by
    rw [diagonal_conjTranspose, diagonal_mul_diagonal]
    congr 1
    funext j
    simp only [Pi.star_apply, Function.comp_apply, Complex.star_def, Complex.conj_ofReal]
    push_cast
    ring
  -- T: the indices whose sorted position is < k
  let T : Finset n :=
    Finset.univ.filter (fun j => ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm j).val < k)
  have hT_mem : ∀ j, j ∈ T ↔ ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm j).val < k :=
    fun j => by simp [T]
  have hkT : k ≤ T.card := by
    have h := Finset.card_le_card_of_injOn
      (fun p : Fin k => (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n)))
        ⟨p.val, by omega⟩) (s := Finset.univ) (t := T)
      (fun p _ => by
        rw [Finset.mem_coe, hT_mem, Equiv.symm_apply_apply]
        exact p.isLt)
      (fun p _ q _ hpq => Fin.ext (by simpa using hpq))
    simpa using h
  have h_gapd : ∀ i ∈ T, ∀ j ∉ T,
      SVD.singularValues A j ^ 2 < SVD.singularValues A i ^ 2 := by
    intro i hi j hj
    rw [hT_mem] at hi hj
    have h_i : SVD.singularValues₀ A ⟨k - 1, by omega⟩ ≤ SVD.singularValues A i := by
      rw [SVD.singularValues_eq_singularValues₀]
      exact SVD.singularValues₀_antitone A (Fin.le_def.mpr (Nat.le_sub_one_of_lt hi))
    have h_j : SVD.singularValues A j ≤ SVD.singularValues₀ A ⟨k, hk⟩ := by
      rw [SVD.singularValues_eq_singularValues₀]
      exact SVD.singularValues₀_antitone A (Fin.le_def.mpr (not_lt.mp hj))
    exact pow_lt_pow_left₀ (by linarith) (SVD.singularValues_nonneg A j) two_ne_zero
  -- S diag(1_T) is the truncated singular-value diagonal
  have hSE : diagonal (Complex.ofReal ∘ SVD.singularValues A) *
      diagonal (fun j => if j ∈ T then (1 : ℂ) else 0) =
      diagonal (Complex.ofReal ∘ SVD.truncatedSingularValues A k) := by
    rw [diagonal_mul_diagonal]
    congr 1
    funext j
    simp only [Function.comp_apply, SVD.truncatedSingularValues, hT_mem]
    split_ifs with h
    · rw [mul_one, SVD.singularValues_eq_singularValues₀]
    · rw [mul_zero, Complex.ofReal_zero]
  have h_trunc : SVD.truncatedSVD A k = (SVD.constructedU A : Matrix n n ℂ) *
      (diagonal (Complex.ofReal ∘ SVD.singularValues A) *
        diagonal (fun j => if j ∈ T then (1 : ℂ) else 0)) *
      star (SVD.rightUnitary A : Matrix n n ℂ) := by
    rw [hSE]
    rfl
  rw [h_trunc] at h_opt ⊢
  exact eq_of_frobenius_le_of_svd A (SVD.constructedU A) (SVD.rightUnitary A) _ hA
    (fun j => SVD.singularValues A j ^ 2) (fun j => sq_nonneg _) hSS T h_gapd B (hB.trans hkT)
    h_opt

end Square

/-! ## Rectangular matrices -/

section Rectangular

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

attribute [local instance] Matrix.frobeniusSeminormedAddCommGroup

/-- **Uniqueness of the Frobenius-optimal rank-k approximation (rectangular).** If the sorted
    singular values have a gap σₖ₋₁ > σₖ (0-indexed, 0 < k < min(#m, #n)), then every B with
    rank B ≤ k and ‖A - B‖_F ≤ ‖A - truncatedSVD_rect A k‖_F equals `truncatedSVD_rect A k`. -/
theorem eckart_young_frobenius_rect_unique (A : Matrix m n ℂ) (k : ℕ)
    (hk : k < min (Fintype.card m) (Fintype.card n))
    (h_gap : SVD.Rectangular.singularValues A ⟨k, hk⟩ <
      SVD.Rectangular.singularValues A ⟨k - 1, by omega⟩)
    (B : Matrix m n ℂ) (hB : B.rank ≤ k)
    (h_opt : ‖A - B‖ ≤ ‖A - TightBounds.truncatedSVD_rect A k‖) :
    B = TightBounds.truncatedSVD_rect A k := by
  have hH := (posSemidef_conjTranspose_mul_self A).isHermitian
  -- The SVD A = U S Vᴴ
  have hA : A = (SVD.Rectangular.constructedU_rectangular A : Matrix m m ℂ) *
      SVD.Rectangular.singularDiagonal A * star (SVD.Rectangular.rightUnitary A : Matrix n n ℂ) := by
    have h_AV := SVD.Rectangular.AV_eq_US_rectangular A
    have hVV : (SVD.Rectangular.rightUnitary A : Matrix n n ℂ) *
        star (SVD.Rectangular.rightUnitary A : Matrix n n ℂ) = 1 :=
      mem_unitaryGroup_iff.mp (SVD.Rectangular.rightUnitary A).2
    calc A = A * ((SVD.Rectangular.rightUnitary A : Matrix n n ℂ) *
          star (SVD.Rectangular.rightUnitary A : Matrix n n ℂ)) := by
          rw [hVV, Matrix.mul_one]
      _ = A * (SVD.Rectangular.rightUnitary A : Matrix n n ℂ) *
          star (SVD.Rectangular.rightUnitary A : Matrix n n ℂ) := by
          rw [Matrix.mul_assoc]
      _ = _ := by rw [h_AV]
  -- SᴴS = diag(eigenvalues of AᴴA)
  have hSS : (SVD.Rectangular.singularDiagonal A)ᴴ * SVD.Rectangular.singularDiagonal A =
      diagonal (fun j => (hH.eigenvalues j : ℂ)) := by
    have h1 : (A * (SVD.Rectangular.rightUnitary A : Matrix n n ℂ))ᴴ *
        (A * (SVD.Rectangular.rightUnitary A : Matrix n n ℂ)) =
        diagonal (Complex.ofReal ∘ hH.eigenvalues) :=
      SVD.Rectangular.conjTranspose_AV_mul_AV_rectangular A
    have hUU : (SVD.Rectangular.constructedU_rectangular A : Matrix m m ℂ)ᴴ *
        (SVD.Rectangular.constructedU_rectangular A : Matrix m m ℂ) = 1 := by
      rw [← star_eq_conjTranspose]
      exact mem_unitaryGroup_iff'.mp (SVD.Rectangular.constructedU_rectangular A).2
    rw [SVD.Rectangular.AV_eq_US_rectangular, conjTranspose_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc (SVD.Rectangular.constructedU_rectangular A : Matrix m m ℂ)ᴴ, hUU,
      Matrix.one_mul] at h1
    exact h1
  -- T: the columns whose sorted position is < k
  let T : Finset n :=
    Finset.univ.filter (fun j => (SVD.Rectangular.eigenvaluesBijection n j).val < k)
  have hT_mem : ∀ j, j ∈ T ↔ (SVD.Rectangular.eigenvaluesBijection n j).val < k :=
    fun j => by simp [T]
  have hk_n : k < Fintype.card n := lt_of_lt_of_le hk (Nat.min_le_right _ _)
  have hkT : k ≤ T.card := by
    have h := Finset.card_le_card_of_injOn
      (fun p : Fin k => (SVD.Rectangular.eigenvaluesBijection n).symm ⟨p.val, by omega⟩)
      (s := Finset.univ) (t := T)
      (fun p _ => by
        rw [Finset.mem_coe, hT_mem, Equiv.apply_symm_apply]
        exact p.isLt)
      (fun p _ q _ hpq => Fin.ext (by simpa using hpq))
    simpa using h
  -- The gap on the eigenvalues of AᴴA, which are the σ² in sorted position
  have hlam_k1 : hH.eigenvalues₀ ⟨k, hk_n⟩ < hH.eigenvalues₀ ⟨k - 1, by omega⟩ := by
    have hsq_k := SVD.Rectangular.singularValues_sq_rect A ⟨k, hk⟩
    have hsq_k1 := SVD.Rectangular.singularValues_sq_rect A ⟨k - 1, by omega⟩
    have h0 := SVD.Rectangular.singularValues_nonneg A ⟨k, hk⟩
    have h_eq_k : hH.eigenvalues₀ ⟨k, hk_n⟩ = SVD.Rectangular.singularValues A ⟨k, hk⟩ ^ 2 :=
      hsq_k.symm
    have h_eq_k1 : hH.eigenvalues₀ ⟨k - 1, by omega⟩ =
        SVD.Rectangular.singularValues A ⟨k - 1, by omega⟩ ^ 2 := hsq_k1.symm
    rw [h_eq_k, h_eq_k1]
    exact pow_lt_pow_left₀ h_gap h0 two_ne_zero
  have h_gapd : ∀ i ∈ T, ∀ j ∉ T, hH.eigenvalues j < hH.eigenvalues i := by
    intro i hi j hj
    rw [hT_mem] at hi hj
    have h_i : hH.eigenvalues₀ ⟨k - 1, by omega⟩ ≤ hH.eigenvalues i :=
      hH.eigenvalues₀_antitone (Fin.le_def.mpr (Nat.le_sub_one_of_lt hi))
    have h_j : hH.eigenvalues j ≤ hH.eigenvalues₀ ⟨k, hk_n⟩ :=
      hH.eigenvalues₀_antitone (Fin.le_def.mpr (not_lt.mp hj))
    linarith
  -- S diag(1_T) is the truncated singular diagonal
  have hSE : SVD.Rectangular.singularDiagonal A *
      diagonal (fun j => if j ∈ T then (1 : ℂ) else 0) =
      TightBounds.truncatedSingularDiagonal_rect A k := by
    ext i j
    rw [mul_diagonal]
    simp only [SVD.Rectangular.singularDiagonal, TightBounds.truncatedSingularDiagonal_rect,
      hT_mem]
    split_ifs <;> first | omega | simp
  have h_trunc : TightBounds.truncatedSVD_rect A k =
      (SVD.Rectangular.constructedU_rectangular A : Matrix m m ℂ) *
      (SVD.Rectangular.singularDiagonal A * diagonal (fun j => if j ∈ T then (1 : ℂ) else 0)) *
      star (SVD.Rectangular.rightUnitary A : Matrix n n ℂ) := by
    rw [hSE]
    rfl
  rw [h_trunc] at h_opt ⊢
  exact eq_of_frobenius_le_of_svd A _ _ _ hA (fun j => hH.eigenvalues j)
    (fun j => (posSemidef_conjTranspose_mul_self A).eigenvalues_nonneg j) hSS T h_gapd B
    (hB.trans hkT) h_opt

end Rectangular

/-! ## The Van Loan–Pitsianis approximation -/

section KroneckerUnique

variable {m n p q : Type*} [Fintype m] [Fintype n] [Fintype p] [Fintype q]
variable [DecidableEq m] [DecidableEq n] [DecidableEq p] [DecidableEq q]

attribute [local instance] Matrix.frobeniusSeminormedAddCommGroup

/-- **Uniqueness of the best Kronecker approximation (Van Loan–Pitsianis).** If the two largest
    singular values of the rearrangement R(C) differ, σ₀(R C) > σ₁(R C), then every Kronecker
    product A ⊗ B with ‖C - A ⊗ B‖_F ≤ ‖C - kroneckerApprox C‖_F equals `kroneckerApprox C`.
    The matrix A ⊗ B is unique; the factors are not (A ⊗ B = (cA) ⊗ (c⁻¹B)). -/
theorem kroneckerApprox_unique (C : Matrix (m × n) (p × q) ℂ)
    (hk : 1 < min (Fintype.card (m × p)) (Fintype.card (n × q)))
    (h_gap : SVD.Rectangular.singularValues (KroneckerRearrangement.R C) ⟨1, hk⟩ <
      SVD.Rectangular.singularValues (KroneckerRearrangement.R C) ⟨0, by omega⟩)
    (A : Matrix m p ℂ) (B : Matrix n q ℂ)
    (h_opt : ‖C - kroneckerMap (· * ·) A B‖ ≤ ‖C - TightBounds.kroneckerApprox C‖) :
    kroneckerMap (· * ·) A B = TightBounds.kroneckerApprox C := by
  -- Move to the rearranged space, where A ⊗ B becomes the rank-1 matrix vec A vec Bᵀ
  have h_rank : (KroneckerRearrangement.R (kroneckerMap (· * ·) A B)).rank ≤ 1 :=
    Kronecker.SpectralBounds.rank_R_kronecker_le_one A B
  have h_err : ‖C - kroneckerMap (· * ·) A B‖ =
      ‖KroneckerRearrangement.R C - KroneckerRearrangement.R (kroneckerMap (· * ·) A B)‖ := by
    have h := TightBounds.frobenius_error_via_R_isometry C
      (KroneckerRearrangement.R (kroneckerMap (· * ·) A B))
    rwa [KroneckerRearrangement.R_inv_R] at h
  have h_opt' : ‖KroneckerRearrangement.R C - KroneckerRearrangement.R (kroneckerMap (· * ·) A B)‖ ≤
      ‖KroneckerRearrangement.R C - TightBounds.truncatedSVD_rect (KroneckerRearrangement.R C) 1‖ := by
    rw [← h_err, ← TightBounds.frobenius_error_via_R_isometry]
    exact h_opt
  have h_eq := eckart_young_frobenius_rect_unique (KroneckerRearrangement.R C) 1 hk h_gap _
    h_rank h_opt'
  calc kroneckerMap (· * ·) A B
      = KroneckerRearrangement.R_inv (KroneckerRearrangement.R (kroneckerMap (· * ·) A B)) :=
        (KroneckerRearrangement.R_inv_R _).symm
    _ = TightBounds.kroneckerApprox C := by rw [h_eq]; rfl

end KroneckerUnique

end Matrix.FrobeniusUniqueness
