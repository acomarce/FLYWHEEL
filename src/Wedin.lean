/-
Copyright (c) 2026 FLYWHEEL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aleksandar Markovski
-/
module

public import DavisKahan

/-!
# Wedin's sin Θ theorem (Frobenius form)

Wedin's theorem bounds how far the singular subspaces of a matrix move under a perturbation.
Let A be m × n with singular triples (σᵢ, uᵢ, vᵢ), so A vᵢ = σᵢ uᵢ and Aᴴ uᵢ = σᵢ vᵢ, and let
P_U, P_V be the orthogonal projections onto span {uᵢ : i < k} and span {vᵢ : i < k}. For any
(μ, x, y) with μ ≥ σₖ, the residuals μ x - A y and μ y - Aᴴ x control the parts of x and y
outside these spans:

  (μ - σₖ)² (‖x - P_U x‖² + ‖y - P_V y‖²) ≤ ‖μ x - A y‖² + ‖μ y - Aᴴ x‖²     (`wedin_residual`)

Summed over the top-k singular triples (σ̃ⱼ, ũⱼ, ṽⱼ) of Ã = A + E, whose residuals are E ṽⱼ and
Eᴴ ũⱼ, this is Wedin's sin Θ theorem in Frobenius form with δ = σ̃ₖ₋₁ - σₖ > 0:

  ‖sin Θ(U, Ũ)‖_F² + ‖sin Θ(V, Ṽ)‖_F² ≤ (‖E Ṽ‖_F² + ‖Eᴴ Ũ‖_F²) / δ²         (`wedin_sin_theta`)

where ‖sin Θ(U, Ũ)‖_F² = Σⱼ ‖ũⱼ - P_U ũⱼ‖². There is no factor k: the Frobenius form adds up
column by column.

## Proof

Write x₂ = x - P_U x and y₂ = y - P_V y.
1. A maps span {vᵢ} into span {uᵢ} and Aᴴ maps span {uᵢ} into span {vᵢ}, so A y₂ ⊥ uᵢ and
   Aᴴ x₂ ⊥ vᵢ. By Pythagoras ‖μ x - A y‖ ≥ ‖μ x₂ - A y₂‖ and ‖μ y - Aᴴ x‖ ≥ ‖μ y₂ - Aᴴ x₂‖
   (`norm_sq_residual_proj_le`).
2. Off span {vᵢ}, ‖A y₂‖ ≤ σₖ ‖y₂‖, and then also ‖Aᴴ x₂‖ ≤ σₖ ‖x₂‖, from
   ‖Aᴴ x₂‖² = ⟨x₂, A Aᴴ x₂⟩.
3. The triangle inequality gives ‖μ x₂ - A y₂‖ ≥ μ ‖x₂‖ - σₖ ‖y₂‖ and the same with x, y
   swapped, and a two-variable inequality (`sq_sub_mul_add_sq_le`) turns these into
   (μ - σₖ)² (‖x₂‖² + ‖y₂‖²).

Steps 1–3 are stated for any pair of linear maps T, S between complex inner product spaces with
⟨x, T y⟩ = ⟨S x, y⟩. The matrix version takes T = A, S = Aᴴ and builds the singular triples
from the eigenvector basis of the Gram matrix Aᴴ A: vᵢ is its i-th eigenvector, σᵢ = √λᵢ and
uᵢ = σᵢ⁻¹ A vᵢ (`rightSingularVector`, `leftSingularVector`). The index set of the top k
singular values is `DavisKahan.topIndices k`, the same set for A and Ã.

Not formalized: the operator-norm form max(‖sin Θ_U‖₂, ‖sin Θ_V‖₂) ≤ max(‖E Ṽ‖₂, ‖Eᴴ Ũ‖₂) / δ.
-/

@[expose] public section

open scoped ComplexOrder Matrix
open Matrix

namespace Matrix.Wedin

local notation "⟪" x ", " y "⟫" => inner ℂ x y

/-! ## A two-variable inequality -/

section Real

/-- If s α - c β ≤ P and s β - c α ≤ Q with α, β ≥ 0 and 0 ≤ c ≤ s, then
    (s - c)² (α² + β²) ≤ P² + Q². -/
theorem sq_sub_mul_add_sq_le {s c α β P Q : ℝ} (hc : 0 ≤ c) (hcs : c ≤ s) (hα : 0 ≤ α)
    (hβ : 0 ≤ β) (h1 : s * α - c * β ≤ P) (h2 : s * β - c * α ≤ Q) :
    (s - c) ^ 2 * (α ^ 2 + β ^ 2) ≤ P ^ 2 + Q ^ 2 := by
  have hN : 0 ≤ α ^ 2 + β ^ 2 := by positivity
  -- (s - c)(α² + β²) ≤ P α + Q β: multiply h1 by α, h2 by β, and use c (α - β)² ≥ 0
  have h3 : (s - c) * (α ^ 2 + β ^ 2) ≤ P * α + Q * β := by
    nlinarith [mul_le_mul_of_nonneg_right h1 hα, mul_le_mul_of_nonneg_right h2 hβ,
      mul_nonneg hc (sq_nonneg (α - β))]
  -- Cauchy–Schwarz in ℝ²: (P α + Q β)² ≤ (P² + Q²)(α² + β²)
  have h4 : (P * α + Q * β) ^ 2 ≤ (P ^ 2 + Q ^ 2) * (α ^ 2 + β ^ 2) := by
    nlinarith [sq_nonneg (P * β - Q * α)]
  have h5 : 0 ≤ (s - c) * (α ^ 2 + β ^ 2) := mul_nonneg (by linarith) hN
  have h6 : ((s - c) * (α ^ 2 + β ^ 2)) ^ 2 ≤ (P ^ 2 + Q ^ 2) * (α ^ 2 + β ^ 2) :=
    (pow_le_pow_left₀ h5 h3 2).trans h4
  rcases hN.eq_or_lt with h0 | hpos
  · rw [← h0, mul_zero]
    positivity
  · refine le_of_mul_le_mul_right ?_ hpos
    calc (s - c) ^ 2 * (α ^ 2 + β ^ 2) * (α ^ 2 + β ^ 2)
        = ((s - c) * (α ^ 2 + β ^ 2)) ^ 2 := by ring
      _ ≤ (P ^ 2 + Q ^ 2) * (α ^ 2 + β ^ 2) := h6

end Real

/-! ## Projections onto orthonormal families -/

section Projection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {ι : Type*} [DecidableEq ι]

/-- For a family w orthonormal on s, the residual z - Σ_{l ∈ s} ⟨w l, z⟩ w l of the orthogonal
    projection onto span {w l : l ∈ s} is orthogonal to every w i, i ∈ s. -/
theorem inner_sub_sum_smul_eq_zero (s : Finset ι) (w : ι → E)
    (hw : ∀ i ∈ s, ∀ j ∈ s, ⟪w i, w j⟫ = if i = j then (1 : ℂ) else 0) (z : E) {i : ι}
    (hi : i ∈ s) : ⟪w i, z - ∑ l ∈ s, ⟪w l, z⟫ • w l⟫ = 0 := by
  have h_term : ∀ l ∈ s, ⟪w i, ⟪w l, z⟫ • w l⟫ = if i = l then ⟪w l, z⟫ else 0 := by
    intro l hl
    rw [inner_smul_right, hw i hi l hl]
    split_ifs <;> ring
  rw [inner_sub_right, inner_sum, Finset.sum_congr rfl h_term, Finset.sum_ite_eq, ite_eq_left hi,
    sub_self]

omit [DecidableEq ι] in
/-- A combination of the w i, i ∈ s, is orthogonal to any vector orthogonal to each of them. -/
theorem inner_sum_smul_eq_zero (s : Finset ι) (w : ι → E) (a : ι → ℂ) (z : E)
    (hz : ∀ i ∈ s, ⟪w i, z⟫ = 0) : ⟪∑ i ∈ s, a i • w i, z⟫ = 0 := by
  rw [sum_inner]
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [inner_smul_left, hz i hi, mul_zero]

end Projection

/-! ## The residual bound for a pair of adjoint maps -/

section Abstract

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {ι : Type*} [DecidableEq ι]

/-- If ⟨x, T y⟩ = ⟨S x, y⟩ for all x, y, then ‖T y‖² ≤ ‖S (T y)‖ ‖y‖. -/
theorem norm_sq_le_of_inner_eq (T : E →ₗ[ℂ] F) (S : F →ₗ[ℂ] E)
    (hTS : ∀ (x : F) (y : E), ⟪x, T y⟫ = ⟪S x, y⟫) (y : E) :
    ‖T y‖ ^ 2 ≤ ‖S (T y)‖ * ‖y‖ :=
  calc ‖T y‖ ^ 2 = RCLike.re ⟪T y, T y⟫ := (inner_self_eq_norm_sq (𝕜 := ℂ) (T y)).symm
    _ ≤ ‖⟪T y, T y⟫‖ := RCLike.re_le_norm _
    _ = ‖⟪S (T y), y⟫‖ := by rw [hTS]
    _ ≤ ‖S (T y)‖ * ‖y‖ := norm_inner_le_norm _ _

/-- Splitting off the spans does not increase the residual: ‖μ x₂ - T y₂‖² ≤ ‖μ x - T y‖² with
    x₂ = x - P_u x and y₂ = y - P_v y, if u is orthonormal on s, T (v i) = σᵢ u i for i ∈ s,
    and T y₂ is orthogonal to the u i. -/
theorem norm_sq_residual_proj_le (T : E →ₗ[ℂ] F) (s : Finset ι) (u : ι → F) (v : ι → E)
    (σ : ι → ℝ) (hu : ∀ i ∈ s, ∀ j ∈ s, ⟪u i, u j⟫ = if i = j then (1 : ℂ) else 0)
    (hTv : ∀ i ∈ s, T (v i) = (σ i : ℂ) • u i) (μ : ℝ) (x : F) (y : E)
    (hy : ∀ i ∈ s, ⟪u i, T (y - ∑ l ∈ s, ⟪v l, y⟫ • v l)⟫ = 0) :
    ‖(μ : ℂ) • (x - ∑ l ∈ s, ⟪u l, x⟫ • u l) - T (y - ∑ l ∈ s, ⟪v l, y⟫ • v l)‖ ^ 2 ≤
      ‖(μ : ℂ) • x - T y‖ ^ 2 := by
  obtain ⟨p, hp⟩ : ∃ p : F,
      p = (μ : ℂ) • (x - ∑ l ∈ s, ⟪u l, x⟫ • u l) - T (y - ∑ l ∈ s, ⟪v l, y⟫ • v l) :=
    ⟨_, rfl⟩
  rw [← hp]
  -- p is orthogonal to the u i
  have hpu : ∀ i ∈ s, ⟪u i, p⟫ = 0 := by
    intro i hi
    rw [hp, inner_sub_right, inner_smul_right, inner_sub_sum_smul_eq_zero s u hu x hi, hy i hi,
      mul_zero, sub_zero]
  -- T maps the projection of y onto span {v i} into span {u i}
  have hTPy : T (∑ l ∈ s, ⟪v l, y⟫ • v l) = ∑ l ∈ s, (⟪v l, y⟫ * (σ l : ℂ)) • u l := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [map_smul, hTv l hl, smul_smul]
  -- so the rest of μ x - T y lies in span {u i}
  have hq : (μ : ℂ) • x - T y - p =
      ∑ l ∈ s, ((μ : ℂ) * ⟪u l, x⟫ - ⟪v l, y⟫ * (σ l : ℂ)) • u l := by
    have h1 : (μ : ℂ) • x - T y - p =
        (μ : ℂ) • ∑ l ∈ s, ⟪u l, x⟫ • u l - T (∑ l ∈ s, ⟪v l, y⟫ • v l) := by
      rw [hp, map_sub, smul_sub]
      abel
    rw [h1, hTPy, Finset.smul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [smul_smul, sub_smul]
  -- Pythagoras
  have h_orth : ⟪(μ : ℂ) • x - T y - p, p⟫ = 0 := by
    rw [hq]
    exact inner_sum_smul_eq_zero s u _ p hpu
  have h_pyth := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ h_orth
  rw [sub_add_cancel] at h_pyth
  nlinarith [h_pyth, mul_self_nonneg ‖(μ : ℂ) • x - T y - p‖]

/-- If T (v i) = σᵢ u i and S (u i) = σᵢ v i with ⟨x, T y⟩ = ⟨S x, y⟩, v orthonormal on s and
    σᵢ ≠ 0, then u is orthonormal on s too. -/
theorem inner_eq_ite_of_singular_pairs (T : E →ₗ[ℂ] F) (S : F →ₗ[ℂ] E)
    (hTS : ∀ (x : F) (y : E), ⟪x, T y⟫ = ⟪S x, y⟫) (s : Finset ι) (u : ι → F) (v : ι → E)
    (σ : ι → ℝ) (hv : ∀ i ∈ s, ∀ j ∈ s, ⟪v i, v j⟫ = if i = j then (1 : ℂ) else 0)
    (hTv : ∀ i ∈ s, T (v i) = (σ i : ℂ) • u i) (hSu : ∀ i ∈ s, S (u i) = (σ i : ℂ) • v i)
    (hσ : ∀ i ∈ s, σ i ≠ 0) :
    ∀ i ∈ s, ∀ j ∈ s, ⟪u i, u j⟫ = if i = j then (1 : ℂ) else 0 := by
  intro i hi j hj
  have hσj : (σ j : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hσ j hj)
  -- σⱼ ⟨u i, u j⟩ = ⟨u i, T v j⟩ = ⟨S u i, v j⟩ = σᵢ ⟨v i, v j⟩
  have h : (σ j : ℂ) * ⟪u i, u j⟫ = (σ i : ℂ) * ⟪v i, v j⟫ := by
    rw [← inner_smul_right (u i) (u j) (σ j : ℂ), ← hTv j hj, hTS, hSu i hi, inner_smul_left,
      Complex.conj_ofReal]
  rw [hv i hi j hj] at h
  split_ifs at h ⊢ with hij
  · subst hij
    exact mul_left_cancel₀ hσj h
  · rw [mul_zero] at h
    exact (mul_eq_zero.mp h).resolve_left hσj

/-- **Wedin's residual bound for one vector.** Let ⟨x, T y⟩ = ⟨S x, y⟩, let u, v be orthonormal
    on s with T (v i) = σᵢ u i and S (u i) = σᵢ v i, and let ‖T y‖ ≤ c ‖y‖ whenever y is
    orthogonal to every v i. Then for all μ ≥ c and all x, y,
    (μ - c)² (‖x - P_u x‖² + ‖y - P_v y‖²) ≤ ‖μ x - T y‖² + ‖μ y - S x‖². -/
theorem wedin_residual (T : E →ₗ[ℂ] F) (S : F →ₗ[ℂ] E)
    (hTS : ∀ (x : F) (y : E), ⟪x, T y⟫ = ⟪S x, y⟫) (s : Finset ι) (u : ι → F) (v : ι → E)
    (σ : ι → ℝ) (hu : ∀ i ∈ s, ∀ j ∈ s, ⟪u i, u j⟫ = if i = j then (1 : ℂ) else 0)
    (hv : ∀ i ∈ s, ∀ j ∈ s, ⟪v i, v j⟫ = if i = j then (1 : ℂ) else 0)
    (hTv : ∀ i ∈ s, T (v i) = (σ i : ℂ) • u i) (hSu : ∀ i ∈ s, S (u i) = (σ i : ℂ) • v i)
    {c : ℝ} (hc : 0 ≤ c) (hTc : ∀ y, (∀ i ∈ s, ⟪v i, y⟫ = 0) → ‖T y‖ ≤ c * ‖y‖)
    (μ : ℝ) (hμ : c ≤ μ) (x : F) (y : E) :
    (μ - c) ^ 2 * (‖x - ∑ i ∈ s, ⟪u i, x⟫ • u i‖ ^ 2 + ‖y - ∑ i ∈ s, ⟪v i, y⟫ • v i‖ ^ 2) ≤
      ‖(μ : ℂ) • x - T y‖ ^ 2 + ‖(μ : ℂ) • y - S x‖ ^ 2 := by
  obtain ⟨x₂, hx₂⟩ : ∃ x₂ : F, x₂ = x - ∑ i ∈ s, ⟪u i, x⟫ • u i := ⟨_, rfl⟩
  obtain ⟨y₂, hy₂⟩ : ∃ y₂ : E, y₂ = y - ∑ i ∈ s, ⟪v i, y⟫ • v i := ⟨_, rfl⟩
  -- x₂ ⊥ u i and y₂ ⊥ v i
  have hx₂u : ∀ i ∈ s, ⟪u i, x₂⟫ = 0 := fun i hi => by
    rw [hx₂]
    exact inner_sub_sum_smul_eq_zero s u hu x hi
  have hy₂v : ∀ i ∈ s, ⟪v i, y₂⟫ = 0 := fun i hi => by
    rw [hy₂]
    exact inner_sub_sum_smul_eq_zero s v hv y hi
  -- T y₂ ⊥ u i and S x₂ ⊥ v i
  have hTy₂ : ∀ i ∈ s, ⟪u i, T y₂⟫ = 0 := fun i hi => by
    rw [hTS, hSu i hi, inner_smul_left, hy₂v i hi, mul_zero]
  have hSx₂ : ∀ i ∈ s, ⟪v i, S x₂⟫ = 0 := fun i hi => by
    have h : ⟪x₂, u i⟫ = 0 := by
      rw [← inner_conj_symm, hx₂u i hi, map_zero]
    rw [← inner_conj_symm, ← hTS, hTv i hi, inner_smul_right, h, mul_zero, map_zero]
  -- ‖T y₂‖ ≤ c ‖y₂‖, and ‖S x₂‖ ≤ c ‖x₂‖ from ‖S x₂‖² ≤ ‖T (S x₂)‖ ‖x₂‖
  have hTy₂c : ‖T y₂‖ ≤ c * ‖y₂‖ := hTc y₂ hy₂v
  have hST : ∀ (a : E) (b : F), ⟪a, S b⟫ = ⟪T a, b⟫ := fun a b => by
    rw [← inner_conj_symm a (S b), ← hTS b a, inner_conj_symm]
  have hSx₂c : ‖S x₂‖ ≤ c * ‖x₂‖ := by
    have h1 := norm_sq_le_of_inner_eq S T hST x₂
    have h2 := mul_le_mul_of_nonneg_right (hTc (S x₂) hSx₂) (norm_nonneg x₂)
    rcases (norm_nonneg (S x₂)).eq_or_lt with h0 | hpos
    · rw [← h0]
      exact mul_nonneg hc (norm_nonneg _)
    · refine le_of_mul_le_mul_right ?_ hpos
      nlinarith [h1, h2]
  -- the triangle inequality
  have hμ0 : 0 ≤ μ := hc.trans hμ
  have hP : μ * ‖x₂‖ - c * ‖y₂‖ ≤ ‖(μ : ℂ) • x₂ - T y₂‖ := by
    have h := norm_sub_norm_le ((μ : ℂ) • x₂) (T y₂)
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hμ0] at h
    linarith
  have hQ : μ * ‖y₂‖ - c * ‖x₂‖ ≤ ‖(μ : ℂ) • y₂ - S x₂‖ := by
    have h := norm_sub_norm_le ((μ : ℂ) • y₂) (S x₂)
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hμ0] at h
    linarith
  have h_real := sq_sub_mul_add_sq_le hc hμ (norm_nonneg x₂) (norm_nonneg y₂) hP hQ
  -- the residuals only shrink when the spans are split off
  have h1 := norm_sq_residual_proj_le T s u v σ hu hTv μ x y (by rw [← hy₂]; exact hTy₂)
  have h2 := norm_sq_residual_proj_le S s v u σ hv hSu μ y x (by rw [← hx₂]; exact hSx₂)
  rw [← hx₂, ← hy₂] at h1 h2
  rw [← hx₂, ← hy₂]
  linarith

/-- **Wedin's sin Θ bound, residual form.** With T, S, u, v, σ, c as in `wedin_residual`, let
    (μⱼ, xⱼ, yⱼ), j ∈ J, satisfy μⱼ ≥ c + δ with δ > 0. Then
    Σⱼ (‖xⱼ - P_u xⱼ‖² + ‖yⱼ - P_v yⱼ‖²) ≤ Σⱼ (‖μⱼ xⱼ - T yⱼ‖² + ‖μⱼ yⱼ - S xⱼ‖²) / δ². -/
theorem wedin_sin_theta_residual (T : E →ₗ[ℂ] F) (S : F →ₗ[ℂ] E)
    (hTS : ∀ (x : F) (y : E), ⟪x, T y⟫ = ⟪S x, y⟫) (s : Finset ι) (u : ι → F) (v : ι → E)
    (σ : ι → ℝ) (hu : ∀ i ∈ s, ∀ j ∈ s, ⟪u i, u j⟫ = if i = j then (1 : ℂ) else 0)
    (hv : ∀ i ∈ s, ∀ j ∈ s, ⟪v i, v j⟫ = if i = j then (1 : ℂ) else 0)
    (hTv : ∀ i ∈ s, T (v i) = (σ i : ℂ) • u i) (hSu : ∀ i ∈ s, S (u i) = (σ i : ℂ) • v i)
    {c : ℝ} (hc : 0 ≤ c) (hTc : ∀ y, (∀ i ∈ s, ⟪v i, y⟫ = 0) → ‖T y‖ ≤ c * ‖y‖)
    {κ : Type*} (J : Finset κ) (μ : κ → ℝ) (x : κ → F) (y : κ → E) {δ : ℝ} (hδ : 0 < δ)
    (hμ : ∀ j ∈ J, c + δ ≤ μ j) :
    ∑ j ∈ J, (‖x j - ∑ i ∈ s, ⟪u i, x j⟫ • u i‖ ^ 2 + ‖y j - ∑ i ∈ s, ⟪v i, y j⟫ • v i‖ ^ 2) ≤
      (∑ j ∈ J, (‖(μ j : ℂ) • x j - T (y j)‖ ^ 2 + ‖(μ j : ℂ) • y j - S (x j)‖ ^ 2)) /
        δ ^ 2 := by
  rw [le_div_iff₀ (pow_pos hδ 2), Finset.sum_mul]
  refine Finset.sum_le_sum fun j hj => ?_
  have hcμ : c ≤ μ j := by linarith [hμ j hj]
  have h := wedin_residual T S hTS s u v σ hu hv hTv hSu hc hTc (μ j) hcμ (x j) (y j)
  have hδμ : δ ^ 2 ≤ (μ j - c) ^ 2 := pow_le_pow_left₀ hδ.le (by linarith [hμ j hj]) 2
  have hN : 0 ≤ ‖x j - ∑ i ∈ s, ⟪u i, x j⟫ • u i‖ ^ 2 + ‖y j - ∑ i ∈ s, ⟪v i, y j⟫ • v i‖ ^ 2 :=
    by positivity
  nlinarith [mul_le_mul_of_nonneg_right hδμ hN]

end Abstract

/-! ## Singular triples of a rectangular matrix -/

section Matrices

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

set_option linter.unusedSectionVars false in
/-- The right singular vectors of A: the eigenvector basis of the Gram matrix Aᴴ A. -/
noncomputable def rightSingularVector (A : Matrix m n ℂ) (i : n) : EuclideanSpace ℂ n :=
  (posSemidef_conjTranspose_mul_self A).isHermitian.eigenvectorBasis i

/-- The left singular vectors of A: uᵢ = σᵢ⁻¹ A vᵢ with σᵢ = √λᵢ(Aᴴ A)
    (`SVD.Rectangular.singularValueFromEigenvalue`). They are orthonormal where σᵢ > 0
    (`inner_leftSingularVector`). -/
noncomputable def leftSingularVector (A : Matrix m n ℂ) (i : n) : EuclideanSpace ℂ m :=
  ((SVD.Rectangular.singularValueFromEigenvalue A i : ℂ)⁻¹) •
    toEuclideanLin A (rightSingularVector A i)

set_option linter.unusedSectionVars false in
/-- σᵢ(A)² = λᵢ(Aᴴ A). -/
theorem singularValueFromEigenvalue_sq (A : Matrix m n ℂ) (i : n) :
    SVD.Rectangular.singularValueFromEigenvalue A i ^ 2 =
      (posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues i :=
  Real.sq_sqrt ((posSemidef_conjTranspose_mul_self A).eigenvalues_nonneg i)

set_option linter.unusedSectionVars false in
/-- Aᴴ is the adjoint of A on Euclidean space: ⟨x, A y⟩ = ⟨Aᴴ x, y⟩. -/
theorem inner_toEuclideanLin_eq (A : Matrix m n ℂ) (x : EuclideanSpace ℂ m)
    (y : EuclideanSpace ℂ n) : ⟪x, toEuclideanLin A y⟫ = ⟪toEuclideanLin Aᴴ x, y⟫ := by
  rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_inner_left]

set_option linter.unusedSectionVars false in
/-- Aᴴ (A y) = (Aᴴ A) y. -/
theorem toEuclideanLin_conjTranspose_apply (A : Matrix m n ℂ) (y : EuclideanSpace ℂ n) :
    toEuclideanLin Aᴴ (toEuclideanLin A y) = toEuclideanLin (Aᴴ * A) y := by
  simp only [Matrix.toLpLin_apply, Matrix.mulVec_mulVec]

set_option linter.unusedSectionVars false in
/-- The right singular vectors are orthonormal. -/
theorem inner_rightSingularVector (A : Matrix m n ℂ) (i j : n) :
    ⟪rightSingularVector A i, rightSingularVector A j⟫ = if i = j then (1 : ℂ) else 0 :=
  orthonormal_iff_ite.mp
    (posSemidef_conjTranspose_mul_self A).isHermitian.eigenvectorBasis.orthonormal i j

set_option linter.unusedSectionVars false in
/-- A vᵢ = σᵢ uᵢ when λᵢ(Aᴴ A) > 0. -/
theorem toEuclideanLin_rightSingularVector (A : Matrix m n ℂ) (i : n)
    (hi : 0 < (posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues i) :
    toEuclideanLin A (rightSingularVector A i) =
      (SVD.Rectangular.singularValueFromEigenvalue A i : ℂ) • leftSingularVector A i := by
  have hσ : (SVD.Rectangular.singularValueFromEigenvalue A i : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hi).ne'
  rw [leftSingularVector, smul_smul, mul_inv_cancel₀ hσ, one_smul]

set_option linter.unusedSectionVars false in
/-- Aᴴ uᵢ = σᵢ vᵢ when λᵢ(Aᴴ A) > 0. -/
theorem toEuclideanLin_conjTranspose_leftSingularVector (A : Matrix m n ℂ) (i : n)
    (hi : 0 < (posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues i) :
    toEuclideanLin Aᴴ (leftSingularVector A i) =
      (SVD.Rectangular.singularValueFromEigenvalue A i : ℂ) • rightSingularVector A i := by
  have hσ : (SVD.Rectangular.singularValueFromEigenvalue A i : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hi).ne'
  have hsq : ((posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues i : ℂ) =
      (SVD.Rectangular.singularValueFromEigenvalue A i : ℂ) *
        (SVD.Rectangular.singularValueFromEigenvalue A i : ℂ) := by
    rw [← Complex.ofReal_mul, ← sq, singularValueFromEigenvalue_sq]
  rw [leftSingularVector, map_smul, toEuclideanLin_conjTranspose_apply, rightSingularVector,
    DavisKahan.toEuclideanLin_eigenvectorBasis, smul_smul, hsq, ← mul_assoc, inv_mul_cancel₀ hσ,
    one_mul]

set_option linter.unusedSectionVars false in
/-- The left singular vectors are orthonormal on any index set where λᵢ(Aᴴ A) > 0. -/
theorem inner_leftSingularVector (A : Matrix m n ℂ) (s : Finset n)
    (hs : ∀ i ∈ s, 0 < (posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues i) :
    ∀ i ∈ s, ∀ j ∈ s,
      ⟪leftSingularVector A i, leftSingularVector A j⟫ = if i = j then (1 : ℂ) else 0 :=
  inner_eq_ite_of_singular_pairs (toEuclideanLin A) (toEuclideanLin Aᴴ)
    (inner_toEuclideanLin_eq A) s (leftSingularVector A) (rightSingularVector A)
    (SVD.Rectangular.singularValueFromEigenvalue A)
    (fun i _ j _ => inner_rightSingularVector A i j)
    (fun i hi => toEuclideanLin_rightSingularVector A i (hs i hi))
    (fun i hi => toEuclideanLin_conjTranspose_leftSingularVector A i (hs i hi))
    (fun i hi => (Real.sqrt_pos.mpr (hs i hi)).ne')

set_option linter.unusedSectionVars false in
/-- If y is orthogonal to the top-k right singular vectors, then ‖(Aᴴ A) y‖ ≤ λₖ(Aᴴ A) ‖y‖. -/
theorem norm_gram_le_of_orthogonal (A : Matrix m n ℂ) (k : ℕ) (hk : k < Fintype.card n)
    (y : EuclideanSpace ℂ n)
    (hy : ∀ i ∈ DavisKahan.topIndices k hk, ⟪rightSingularVector A i, y⟫ = 0) :
    ‖toEuclideanLin (Aᴴ * A) y‖ ≤
      (posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues₀ ⟨k, hk⟩ * ‖y‖ := by
  have hG := (posSemidef_conjTranspose_mul_self A).isHermitian
  have hSym : (toEuclideanLin (Aᴴ * A)).IsSymmetric := isSymmetric_toEuclideanLin_iff.mpr hG
  have h_ev := PosSemidef_eigenvalues₀_nonneg (posSemidef_conjTranspose_mul_self A) ⟨k, hk⟩
  -- coefficients of (Aᴴ A) y in the eigenbasis: ⟨vₗ, Aᴴ A y⟩ = λₗ ⟨vₗ, y⟩
  have hcoef : ∀ l, ⟪hG.eigenvectorBasis l, toEuclideanLin (Aᴴ * A) y⟫ =
      (hG.eigenvalues l : ℂ) * ⟪hG.eigenvectorBasis l, y⟫ := by
    intro l
    rw [← hSym (hG.eigenvectorBasis l) y, DavisKahan.toEuclideanLin_eigenvectorBasis hG l,
      inner_smul_left, Complex.conj_ofReal]
  -- on the top indices the coefficient vanishes, off them 0 ≤ λₗ ≤ λₖ
  have h_term : ∀ l, hG.eigenvalues l ^ 2 * ‖⟪hG.eigenvectorBasis l, y⟫‖ ^ 2 ≤
      hG.eigenvalues₀ ⟨k, hk⟩ ^ 2 * ‖⟪hG.eigenvectorBasis l, y⟫‖ ^ 2 := by
    intro l
    by_cases hl : l ∈ DavisKahan.topIndices k hk
    · have hy' : ⟪hG.eigenvectorBasis l, y⟫ = 0 := hy l hl
      rw [hy', norm_zero]
      simp
    · have h_le := DavisKahan.eigenvalues_le_of_not_mem_topIndices hG hk hl
      have h_nn : 0 ≤ hG.eigenvalues l :=
        (posSemidef_conjTranspose_mul_self A).eigenvalues_nonneg l
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h_nn h_le 2) (sq_nonneg _)
  -- Parseval on both sides
  have h_sq : ‖toEuclideanLin (Aᴴ * A) y‖ ^ 2 ≤ (hG.eigenvalues₀ ⟨k, hk⟩ * ‖y‖) ^ 2 := by
    rw [← hG.eigenvectorBasis.sum_sq_norm_inner_right (toEuclideanLin (Aᴴ * A) y), mul_pow,
      ← hG.eigenvectorBasis.sum_sq_norm_inner_right y, Finset.mul_sum]
    refine Finset.sum_le_sum fun l _ => ?_
    rw [hcoef l, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    exact h_term l
  exact le_of_sq_le_sq h_sq (mul_nonneg h_ev (norm_nonneg y))

set_option linter.unusedSectionVars false in
/-- If y is orthogonal to the top-k right singular vectors, then ‖A y‖ ≤ σₖ ‖y‖ with
    σₖ = √λₖ(Aᴴ A). -/
theorem norm_toEuclideanLin_le_of_orthogonal (A : Matrix m n ℂ) (k : ℕ)
    (hk : k < Fintype.card n) (y : EuclideanSpace ℂ n)
    (hy : ∀ i ∈ DavisKahan.topIndices k hk, ⟪rightSingularVector A i, y⟫ = 0) :
    ‖toEuclideanLin A y‖ ≤
      √((posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues₀ ⟨k, hk⟩) * ‖y‖ := by
  have h_ev := PosSemidef_eigenvalues₀_nonneg (posSemidef_conjTranspose_mul_self A) ⟨k, hk⟩
  -- ‖A y‖² ≤ ‖Aᴴ A y‖ ‖y‖ ≤ λₖ ‖y‖²
  have h1 := norm_sq_le_of_inner_eq (toEuclideanLin A) (toEuclideanLin Aᴴ)
    (inner_toEuclideanLin_eq A) y
  rw [toEuclideanLin_conjTranspose_apply] at h1
  have h2 := mul_le_mul_of_nonneg_right (norm_gram_le_of_orthogonal A k hk y hy) (norm_nonneg y)
  refine le_of_sq_le_sq ?_ (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg y))
  rw [mul_pow, Real.sq_sqrt h_ev]
  nlinarith [h1, h2]

/-! ## Wedin's theorem -/

set_option linter.unusedSectionVars false in
/-- **Wedin's sin Θ theorem (Frobenius form).** Let A, Ã be m × n, k < n, with
    σₖ₋₁(A) > 0 and gap δ = σₖ₋₁(Ã) - σₖ(A) > 0 (σᵢ = √λᵢ of the Gram matrix, 0-indexed). Let
    uᵢ, vᵢ and ũⱼ, ṽⱼ be the left and right singular vectors of A and Ã, and P_U, P_V the
    orthogonal projections onto the spans of the top-k left and right singular vectors of A
    (indices `topIndices k`). Then, with E = Ã - A,
    Σⱼ (‖ũⱼ - P_U ũⱼ‖² + ‖ṽⱼ - P_V ṽⱼ‖²) ≤ Σⱼ (‖E ṽⱼ‖² + ‖Eᴴ ũⱼ‖²) / δ²,
    summing over the top-k indices j. The left side is
    ‖sin Θ(U, Ũ)‖_F² + ‖sin Θ(V, Ṽ)‖_F² and the right side is (‖E Ṽ‖_F² + ‖Eᴴ Ũ‖_F²) / δ². -/
theorem wedin_sin_theta (A Ã : Matrix m n ℂ) (k : ℕ) (hk : k < Fintype.card n)
    (hA : 0 < (posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues₀ ⟨k - 1, by omega⟩)
    (hgap : √((posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues₀ ⟨k, hk⟩) <
      √((posSemidef_conjTranspose_mul_self Ã).isHermitian.eigenvalues₀ ⟨k - 1, by omega⟩)) :
    ∑ j ∈ DavisKahan.topIndices k hk,
        (‖leftSingularVector Ã j - ∑ i ∈ DavisKahan.topIndices k hk,
            ⟪leftSingularVector A i, leftSingularVector Ã j⟫ • leftSingularVector A i‖ ^ 2 +
          ‖rightSingularVector Ã j - ∑ i ∈ DavisKahan.topIndices k hk,
            ⟪rightSingularVector A i, rightSingularVector Ã j⟫ • rightSingularVector A i‖ ^ 2) ≤
      (∑ j ∈ DavisKahan.topIndices k hk,
          (‖toEuclideanLin (Ã - A) (rightSingularVector Ã j)‖ ^ 2 +
            ‖toEuclideanLin (Ã - A)ᴴ (leftSingularVector Ã j)‖ ^ 2)) /
        (√((posSemidef_conjTranspose_mul_self Ã).isHermitian.eigenvalues₀ ⟨k - 1, by omega⟩) -
          √((posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues₀ ⟨k, hk⟩)) ^ 2 := by
  -- on the top indices, λᵢ(Aᴴ A) ≥ λₖ₋₁(Aᴴ A) > 0
  have hApos : ∀ i ∈ DavisKahan.topIndices k hk,
      0 < (posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues i := fun i hi =>
    hA.trans_le (DavisKahan.le_eigenvalues_of_mem_topIndices _ hk hi)
  -- on the top indices, σⱼ(Ã) ≥ σₖ₋₁(Ã) > σₖ(A) ≥ 0
  have hÃge : ∀ j ∈ DavisKahan.topIndices k hk,
      √((posSemidef_conjTranspose_mul_self Ã).isHermitian.eigenvalues₀ ⟨k - 1, by omega⟩) ≤
        SVD.Rectangular.singularValueFromEigenvalue Ã j := fun j hj =>
    Real.sqrt_le_sqrt (DavisKahan.le_eigenvalues_of_mem_topIndices _ hk hj)
  have hÃ0 : 0 < (posSemidef_conjTranspose_mul_self Ã).isHermitian.eigenvalues₀
      ⟨k - 1, by omega⟩ :=
    Real.sqrt_pos.mp ((Real.sqrt_nonneg _).trans_lt hgap)
  have hÃpos : ∀ j ∈ DavisKahan.topIndices k hk,
      0 < (posSemidef_conjTranspose_mul_self Ã).isHermitian.eigenvalues j := fun j hj =>
    hÃ0.trans_le (DavisKahan.le_eigenvalues_of_mem_topIndices _ hk hj)
  -- the residual bound for A with c = σₖ(A), applied to the top-k triples of Ã
  have h := wedin_sin_theta_residual (toEuclideanLin A) (toEuclideanLin Aᴴ)
    (inner_toEuclideanLin_eq A) (DavisKahan.topIndices k hk) (leftSingularVector A)
    (rightSingularVector A) (SVD.Rectangular.singularValueFromEigenvalue A)
    (inner_leftSingularVector A _ hApos) (fun i _ j _ => inner_rightSingularVector A i j)
    (fun i hi => toEuclideanLin_rightSingularVector A i (hApos i hi))
    (fun i hi => toEuclideanLin_conjTranspose_leftSingularVector A i (hApos i hi))
    (Real.sqrt_nonneg ((posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues₀ ⟨k, hk⟩))
    (norm_toEuclideanLin_le_of_orthogonal A k hk) (DavisKahan.topIndices k hk)
    (SVD.Rectangular.singularValueFromEigenvalue Ã) (leftSingularVector Ã)
    (rightSingularVector Ã) (sub_pos.mpr hgap) (fun j hj => by linarith [hÃge j hj])
  -- the residuals of the triples of Ã are E ṽⱼ and Eᴴ ũⱼ
  have h_res : ∀ j ∈ DavisKahan.topIndices k hk,
      ‖(SVD.Rectangular.singularValueFromEigenvalue Ã j : ℂ) • leftSingularVector Ã j -
          toEuclideanLin A (rightSingularVector Ã j)‖ ^ 2 +
        ‖(SVD.Rectangular.singularValueFromEigenvalue Ã j : ℂ) • rightSingularVector Ã j -
          toEuclideanLin Aᴴ (leftSingularVector Ã j)‖ ^ 2 =
      ‖toEuclideanLin (Ã - A) (rightSingularVector Ã j)‖ ^ 2 +
        ‖toEuclideanLin (Ã - A)ᴴ (leftSingularVector Ã j)‖ ^ 2 := by
    intro j hj
    rw [← toEuclideanLin_rightSingularVector Ã j (hÃpos j hj),
      ← toEuclideanLin_conjTranspose_leftSingularVector Ã j (hÃpos j hj), conjTranspose_sub,
      map_sub, map_sub, LinearMap.sub_apply, LinearMap.sub_apply]
  refine h.trans (le_of_eq ?_)
  congr 1
  exact Finset.sum_congr rfl h_res

/-! ## The bound in the operator norm of E -/

section L2

attribute [local instance] Matrix.instL2OpNormedAddCommGroup

set_option linter.unusedSectionVars false in
/-- **Wedin's sin Θ theorem in ‖E‖₂.** Under the hypotheses of `wedin_sin_theta`, with
    E = Ã - A and δ = σₖ₋₁(Ã) - σₖ(A),
    ‖sin Θ(U, Ũ)‖_F² + ‖sin Θ(V, Ṽ)‖_F² ≤ 2 k ‖E‖₂² / δ². -/
theorem wedin_sin_theta_l2 (A Ã : Matrix m n ℂ) (k : ℕ) (hk : k < Fintype.card n)
    (hA : 0 < (posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues₀ ⟨k - 1, by omega⟩)
    (hgap : √((posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues₀ ⟨k, hk⟩) <
      √((posSemidef_conjTranspose_mul_self Ã).isHermitian.eigenvalues₀ ⟨k - 1, by omega⟩)) :
    ∑ j ∈ DavisKahan.topIndices k hk,
        (‖leftSingularVector Ã j - ∑ i ∈ DavisKahan.topIndices k hk,
            ⟪leftSingularVector A i, leftSingularVector Ã j⟫ • leftSingularVector A i‖ ^ 2 +
          ‖rightSingularVector Ã j - ∑ i ∈ DavisKahan.topIndices k hk,
            ⟪rightSingularVector A i, rightSingularVector Ã j⟫ • rightSingularVector A i‖ ^ 2) ≤
      2 * k * ‖Ã - A‖ ^ 2 /
        (√((posSemidef_conjTranspose_mul_self Ã).isHermitian.eigenvalues₀ ⟨k - 1, by omega⟩) -
          √((posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues₀ ⟨k, hk⟩)) ^ 2 := by
  have hÃ0 : 0 < (posSemidef_conjTranspose_mul_self Ã).isHermitian.eigenvalues₀
      ⟨k - 1, by omega⟩ :=
    Real.sqrt_pos.mp ((Real.sqrt_nonneg _).trans_lt hgap)
  have hÃpos : ∀ j ∈ DavisKahan.topIndices k hk,
      0 < (posSemidef_conjTranspose_mul_self Ã).isHermitian.eigenvalues j := fun j hj =>
    hÃ0.trans_le (DavisKahan.le_eigenvalues_of_mem_topIndices _ hk hj)
  -- each term is at most 2 ‖E‖₂², since ũⱼ and ṽⱼ are unit vectors and ‖Eᴴ‖₂ = ‖E‖₂
  have h_each : ∀ j ∈ DavisKahan.topIndices k hk,
      ‖toEuclideanLin (Ã - A) (rightSingularVector Ã j)‖ ^ 2 +
          ‖toEuclideanLin (Ã - A)ᴴ (leftSingularVector Ã j)‖ ^ 2 ≤ 2 * ‖Ã - A‖ ^ 2 := by
    intro j hj
    have hv1 : ‖rightSingularVector Ã j‖ = 1 :=
      (posSemidef_conjTranspose_mul_self Ã).isHermitian.eigenvectorBasis.orthonormal.1 j
    have hu1 : ‖leftSingularVector Ã j‖ ^ 2 = 1 := by
      have h := inner_leftSingularVector Ã _ hÃpos j hj j hj
      rw [ite_eq_left rfl] at h
      rw [← inner_self_eq_norm_sq (𝕜 := ℂ), h, RCLike.one_re]
    have h1 : ‖toEuclideanLin (Ã - A) (rightSingularVector Ã j)‖ ≤
        ‖Ã - A‖ * ‖rightSingularVector Ã j‖ :=
      Matrix.l2_opNorm_mulVec (Ã - A) _
    have h2 : ‖toEuclideanLin (Ã - A)ᴴ (leftSingularVector Ã j)‖ ≤
        ‖(Ã - A)ᴴ‖ * ‖leftSingularVector Ã j‖ :=
      Matrix.l2_opNorm_mulVec (Ã - A)ᴴ _
    rw [hv1, mul_one] at h1
    rw [Matrix.l2_opNorm_conjTranspose] at h2
    have h1' := pow_le_pow_left₀ (norm_nonneg _) h1 2
    have h2' := pow_le_pow_left₀ (norm_nonneg _) h2 2
    rw [mul_pow, hu1, mul_one] at h2'
    linarith
  have h_num : ∑ j ∈ DavisKahan.topIndices k hk,
      (‖toEuclideanLin (Ã - A) (rightSingularVector Ã j)‖ ^ 2 +
        ‖toEuclideanLin (Ã - A)ᴴ (leftSingularVector Ã j)‖ ^ 2) ≤ 2 * k * ‖Ã - A‖ ^ 2 := by
    calc _ ≤ ∑ j ∈ DavisKahan.topIndices k hk, 2 * ‖Ã - A‖ ^ 2 := Finset.sum_le_sum h_each
      _ = 2 * k * ‖Ã - A‖ ^ 2 := by
        rw [Finset.sum_const, DavisKahan.card_topIndices, nsmul_eq_mul]
        ring
  exact (wedin_sin_theta A Ã k hk hA hgap).trans
    (div_le_div₀ (by positivity) h_num (pow_pos (sub_pos.mpr hgap) 2) le_rfl)

end L2

end Matrices

end Matrix.Wedin
