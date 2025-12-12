/-
Copyright (c) 2025 FLYWHEEL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aleksandar Markovski
-/
import Mathlib
import SVD
import CourantFischer

/-!
# Weyl's Eigenvalue Inequalities

For Hermitian A, B: λₖ(A) + λₙ(B) ≤ λₖ(A+B) ≤ λₖ(A) + λ₁(B).

## References

[1] Weyl, H. (1912). Math. Ann. 71, 441–479.
[2] Horn & Johnson (2012), Thm 4.3.1 (eigenvalue interlacing).
[3] Isabelle AFP (2024). Two Theorems on Hermitian Matrices.

-/

-- unused, but keeping around in case we need it for the singular value version
-- private def _root_.Nat.triangular (n : ℕ) : ℕ := n * (n + 1) / 2

open scoped Matrix ComplexOrder
open Finset Matrix BigOperators

namespace Matrix.WeylInequality

variable {n : Type*} [DecidableEq n] [Fintype n] [Nonempty n]

section RayleighAdditivity

omit [Nonempty n] in
theorem toEuclideanLin_add (A B : Matrix n n ℂ) (x : EuclideanSpace ℂ n) :
    Matrix.toEuclideanLin (A + B) x = Matrix.toEuclideanLin A x + Matrix.toEuclideanLin B x := by
  simp only [Matrix.toEuclideanLin_apply, Matrix.add_mulVec]
  rfl

omit [Nonempty n] in
/-- The Rayleigh quotient is additive for Hermitian matrices.

For Hermitian A, B and any vector x:
  Re⟨(A+B)x, x⟩ = Re⟨Ax, x⟩ + Re⟨Bx, x⟩

This is the fundamental lemma enabling Weyl's inequality proof. -/
-- Q: Do we actually need hA and hB here? The proof doesn't seem to use them...
-- A: Yes we do - we need the inner products to be real. Actually wait, we're
-- taking Re anyway so maybe not? TODO: try removing them
theorem rayleigh_add (A B : Matrix n n ℂ) (_hA : A.IsHermitian) (_hB : B.IsHermitian)
    (x : EuclideanSpace ℂ n) :
    (@inner ℂ _ _ (Matrix.toEuclideanLin (A + B) x) x).re =
    (@inner ℂ _ _ (Matrix.toEuclideanLin A x) x).re +
    (@inner ℂ _ _ (Matrix.toEuclideanLin B x) x).re := by
  -- Use linearity: (A+B)x = Ax + Bx
  rw [toEuclideanLin_add]
  -- Use linearity of inner product: ⟨u + v, x⟩ = ⟨u, x⟩ + ⟨v, x⟩
  rw [inner_add_left]
  -- Re(z₁ + z₂) = Re(z₁) + Re(z₂)
  rw [Complex.add_re]

end RayleighAdditivity

/-! ## Weyl Eigenvalue Bounds -/

section WeylEigenvalue

/-!
### Weyl's Eigenvalue Inequality for Hermitian Matrices

For Hermitian matrices A, B with sorted eigenvalues (descending):
  λₖ(A) + λₙ(B) ≤ λₖ(A+B) ≤ λₖ(A) + λ₁(B)

The proof uses Courant-Fischer min-max characterization:
  λₖ = max_{dim W = k+1} min_{x ∈ W, ‖x‖=1} R(x)

Key idea: The eigenspace of A achieving λₖ also gives a lower bound for A+B
via Rayleigh additivity and the global bounds on R_B(x).
-/

/-- The minimum eigenvalue index (last index in sorted order). -/
def minEigenvalueIdx : Fin (Fintype.card n) :=
  ⟨Fintype.card n - 1, Nat.sub_lt Fintype.card_pos Nat.one_pos⟩

/-- **Weyl's Lower Bound**: For Hermitian A, B:
    λₖ(A+B) ≥ λₖ(A) + λₙ₋₁(B)

where eigenvalues are sorted in descending order (λ₀ is the largest). -/
theorem weyl_eigenvalue_lower_bound (A B : Matrix n n ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (k : Fin (Fintype.card n)) :
    (hA.add hB).eigenvalues₀ k ≥ hA.eigenvalues₀ k + hB.eigenvalues₀ minEigenvalueIdx := by
  -- Proof outline:
  -- 1. Take W = span of first k+1 eigenvectors of A (dimension k+1)
  -- 2. For unit x ∈ W: R_A(x) ≥ λₖ(A) and R_B(x) ≥ λₙ₋₁(B)
  -- 3. Therefore R_{A+B}(x) = R_A(x) + R_B(x) ≥ λₖ(A) + λₙ₋₁(B)
  -- 4. By Courant-Fischer: λₖ(A+B) = sup_{dim V = k+1} inf_{x ∈ V} R(x)
  -- 5. So λₖ(A+B) ≥ inf_{x ∈ W} R_{A+B}(x) ≥ λₖ(A) + λₙ₋₁(B)

  -- Take the (k+1)-dimensional eigenspace of A
  let k_succ : Fin (Fintype.card n + 1) := ⟨k.val + 1, by omega⟩
  let W := CourantFischer.eigenvectorSpanHead hA k_succ

  -- Get the k-th eigenvector which achieves λₖ(A)
  let idx := (Fintype.equivOfCardEq (Fintype.card_fin _)) k
  let v := hA.eigenvectorBasis idx
  have hv_unit : ‖v‖ = 1 := hA.eigenvectorBasis.orthonormal.1 idx

  -- v is in W (the span of first k+1 eigenvectors)
  have hv_mem : v ∈ W := by
    unfold W CourantFischer.eigenvectorSpanHead
    apply Submodule.subset_span
    simp only [Set.mem_range]
    have hk_lt : k.val < k.val + 1 := Nat.lt_succ_self k.val
    use ⟨k.val, hk_lt⟩
    simp only [Fin.castLE_mk]
    rfl

  -- R_A(v) = λₖ(A)
  have hRv_A : (@inner ℂ (EuclideanSpace ℂ n) _ (Matrix.toEuclideanLin A v) v).re =
      hA.eigenvalues₀ k := by
    have h := CourantFischer.rayleigh_eq_eigenvalue_on_eigenvector A hA idx
    rw [h]
    rw [CourantFischer.eigenvalues_eq_eigenvalues₀_comp A hA idx]
    congr 1
    exact Equiv.symm_apply_apply _ k

  -- R_B(v) ≥ λₙ₋₁(B) (since v is a unit vector)
  have hRv_B : (@inner ℂ (EuclideanSpace ℂ n) _ (Matrix.toEuclideanLin B v) v).re ≥
      hB.eigenvalues₀ minEigenvalueIdx := by
    exact CourantFischer.rayleigh_ge_eigenvalue_min B hB v hv_unit

  -- R_{A+B}(v) = R_A(v) + R_B(v) ≥ λₖ(A) + λₙ₋₁(B)
  have hRv_sum : (@inner ℂ (EuclideanSpace ℂ n) _ (Matrix.toEuclideanLin (A + B) v) v).re ≥
      hA.eigenvalues₀ k + hB.eigenvalues₀ minEigenvalueIdx := by
    rw [rayleigh_add A B hA hB v]
    have h1 : (@inner ℂ (EuclideanSpace ℂ n) _ (Matrix.toEuclideanLin A v) v).re +
          (@inner ℂ (EuclideanSpace ℂ n) _ (Matrix.toEuclideanLin B v) v).re
        = hA.eigenvalues₀ k + (@inner ℂ (EuclideanSpace ℂ n) _ (Matrix.toEuclideanLin B v) v).re := by
      rw [hRv_A]
    rw [h1]
    linarith

  -- R_{A+B}(v) ≤ λ₀(A+B) (for unit vectors)
  have hRv_le_max : (@inner ℂ (EuclideanSpace ℂ n) _ (Matrix.toEuclideanLin (A + B) v) v).re ≤
      (hA.add hB).eigenvalues₀ 0 := by
    exact CourantFischer.rayleigh_le_eigenvalue_max (A + B) (hA.add hB) v hv_unit

  have h_dim_W : Module.finrank ℂ W = k.val + 1 :=
    CourantFischer.finrank_eigenvectorSpanHead A hA k_succ

  -- For any unit x ∈ W: R_A(x) ≥ λₖ(A)
  have h_RA_lower : ∀ x : EuclideanSpace ℂ n, x ∈ W → ‖x‖ = 1 →
      (@inner ℂ (EuclideanSpace ℂ n) _ (Matrix.toEuclideanLin A x) x).re ≥ hA.eigenvalues₀ k := by
    intro x hx hx_unit
    have hk_pos : (0 : Fin (Fintype.card n + 1)) < k_succ := by
      simp only [Fin.lt_def, Fin.val_zero]
      exact Nat.zero_lt_succ k.val
    exact CourantFischer.rayleigh_ge_on_eigenvectorSpanHead A hA k_succ hk_pos x hx_unit hx

  -- For any unit x: R_B(x) ≥ λₙ₋₁(B)
  have h_RB_lower : ∀ x : EuclideanSpace ℂ n, ‖x‖ = 1 →
      (@inner ℂ (EuclideanSpace ℂ n) _ (Matrix.toEuclideanLin B x) x).re ≥
        hB.eigenvalues₀ minEigenvalueIdx := by
    intro x hx_unit
    exact CourantFischer.rayleigh_ge_eigenvalue_min B hB x hx_unit

  -- Combined: For any unit x ∈ W: R_{A+B}(x) ≥ λₖ(A) + λₙ₋₁(B)
  have h_RAB_lower : ∀ x : EuclideanSpace ℂ n, x ∈ W → ‖x‖ = 1 →
      (@inner ℂ (EuclideanSpace ℂ n) _ (Matrix.toEuclideanLin (A + B) x) x).re ≥
        hA.eigenvalues₀ k + hB.eigenvalues₀ minEigenvalueIdx := by
    intro x hx hx_unit
    rw [rayleigh_add A B hA hB x]
    exact add_le_add (h_RA_lower x hx hx_unit) (h_RB_lower x hx_unit)

  -- W is nonempty (has nonzero vectors)
  have hW_nonempty : ∃ x : W, x.val ≠ 0 := by
    have h_pos : 0 < Module.finrank ℂ W := by rw [h_dim_W]; omega
    exact CourantFischer.exists_nonzero_of_finrank_pos W h_pos
  -- We want: eigenvalue ≥ rayleighInf, which is the same thing!

  -- So by rayleighInf_le_eigenvalue for A+B:
  -- rayleighInf(A+B, W) ≤ λₖ(A+B)
  -- i.e., λₖ(A+B) ≥ rayleighInf(A+B, W)

  -- And we showed: rayleighInf(A+B, W) ≥ λₖ(A) + λₙ₋₁(B)
  -- Therefore: λₖ(A+B) ≥ λₖ(A) + λₙ₋₁(B). QED!

  -- Step 1: λₖ(A+B) ≥ rayleighInf(A+B, W)
  have h_step1 : (hA.add hB).eigenvalues₀ k ≥ CourantFischer.rayleighInf (A + B) (hA.add hB) W := by
    -- rayleighInf_le_eigenvalue says rayleighInf ≤ eigenvalue
    -- We need to flip this to eigenvalue ≥ rayleighInf
    have hk_pos : (0 : Fin (Fintype.card n + 1)) < k_succ := by
      simp only [Fin.lt_def, Fin.val_zero]
      exact Nat.zero_lt_succ k.val
    have h := CourantFischer.rayleighInf_le_eigenvalue (A + B) (hA.add hB) k_succ hk_pos W h_dim_W
    -- h : rayleighInf ≤ eigenvalues₀ ⟨k_succ - 1, _⟩
    -- Note: k_succ = k + 1, so k_succ - 1 = k
    convert h.ge using 1

  -- Step 2: rayleighInf(A+B, W) ≥ λₖ(A) + λₙ₋₁(B)
  have h_step2 : CourantFischer.rayleighInf (A + B) (hA.add hB) W ≥
      hA.eigenvalues₀ k + hB.eigenvalues₀ minEigenvalueIdx := by
    unfold CourantFischer.rayleighInf CourantFischer.rayleighQuotient
    haveI : Nonempty { x : W // x.val ≠ 0 } := by
      obtain ⟨x, hx⟩ := hW_nonempty
      exact ⟨⟨x, hx⟩⟩
    apply le_ciInf
    intro ⟨⟨x, hx_mem⟩, hx_ne⟩
    -- x ∈ W, x ≠ 0, need: (λₖ(A) + λₙ₋₁(B)) ≤ R(x)
    by_cases hx_norm : ‖x‖ = 0
    · -- x = 0, contradiction
      exfalso; exact hx_ne (norm_eq_zero.mp hx_norm)
    · -- Normalize x
      have hx_pos : 0 < ‖x‖ := norm_pos_iff.mpr (fun h => hx_ne h)
      let y := (1 / ‖x‖ : ℂ) • x
      have hy_unit : ‖y‖ = 1 := by
        simp only [y, norm_smul, one_div]
        rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx_pos,
            inv_mul_cancel₀ (ne_of_gt hx_pos)]
      have hy_mem : y ∈ W := Submodule.smul_mem W _ hx_mem

      -- R(x) = R(y) by scaling invariance
      have h_scale : (@inner ℂ (EuclideanSpace ℂ n) _ (Matrix.toEuclideanLin (A + B) x) x).re / ‖x‖^2 =
          (@inner ℂ (EuclideanSpace ℂ n) _ (Matrix.toEuclideanLin (A + B) y) y).re := by
        have hc_ne : (1 / ‖x‖ : ℂ) ≠ 0 := by
          simp only [one_div, ne_eq, inv_eq_zero, Complex.ofReal_eq_zero]
          exact ne_of_gt hx_pos
        have h := CourantFischer.rayleigh_scale_complex (A := A + B) hx_ne (1 / ‖x‖ : ℂ) hc_ne
        simp only [y] at hy_unit ⊢
        rw [hy_unit, one_pow, div_one] at h
        exact h.symm

      calc hA.eigenvalues₀ k + hB.eigenvalues₀ minEigenvalueIdx
          ≤ (@inner ℂ (EuclideanSpace ℂ n) _ (Matrix.toEuclideanLin (A + B) y) y).re := h_RAB_lower y hy_mem hy_unit
        _ = (@inner ℂ (EuclideanSpace ℂ n) _ (Matrix.toEuclideanLin (A + B) x) x).re / ‖x‖^2 := h_scale.symm

  -- Combine steps
  exact le_trans h_step2 h_step1

/-- **Weyl's Upper Bound**: For Hermitian A, B:
    λₖ(A+B) ≤ λₖ(A) + λ₀(B)

where eigenvalues are sorted in descending order (λ₀ is the largest). -/
theorem weyl_eigenvalue_upper_bound (A B : Matrix n n ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (k : Fin (Fintype.card n)) :
    (hA.add hB).eigenvalues₀ k ≤ hA.eigenvalues₀ k + hB.eigenvalues₀ 0 := by
  -- Strategy: Apply the lower bound to -B
  -- λₖ(A+B) = λₖ(A + B)
  -- λₖ(A) = λₖ((A+B) + (-B))
  -- ≥ λₖ(A+B) + λₙ₋₁(-B)   by weyl_eigenvalue_lower_bound
  -- = λₖ(A+B) - λ₀(B)       since eigenvalues of -B are negatives, reversed

  -- So λₖ(A+B) ≤ λₖ(A) + λ₀(B). QED!

  -- First, show that (A + B) + (-B) = A
  have h_sum : A + B + (-B) = A := by simp only [add_neg_cancel_right]

  -- Show -B is Hermitian
  have hNegB : (-B).IsHermitian := by
    unfold IsHermitian
    simp only [conjTranspose_neg]
    rw [hB.eq]

  let k_succ : Fin (Fintype.card n + 1) := ⟨k.val + 1, by omega⟩

  -- For any unit x: R_B(x) ≤ λ₀(B)
  have h_RB_upper : ∀ x : EuclideanSpace ℂ n, ‖x‖ = 1 →
      (@inner ℂ (EuclideanSpace ℂ n) _ (Matrix.toEuclideanLin B x) x).re ≤
        hB.eigenvalues₀ 0 := by
    intro x hx_unit
    exact CourantFischer.rayleigh_le_eigenvalue_max B hB x hx_unit

  -- Take the tail eigenspace of A: span of eigenvectors k, k+1, ..., n-1
  -- This has dimension n - k
  let W := CourantFischer.eigenvectorSpanTail hA k

  have h_dim_W : Module.finrank ℂ W = Fintype.card n - k.val :=
    CourantFischer.finrank_eigenvectorSpanTail A hA k

  -- For unit x ∈ W: R_A(x) ≤ λₖ(A)
  have h_RA_upper : ∀ x : EuclideanSpace ℂ n, x ∈ W → ‖x‖ = 1 →
      (@inner ℂ (EuclideanSpace ℂ n) _ (Matrix.toEuclideanLin A x) x).re ≤ hA.eigenvalues₀ k := by
    intro x hx hx_unit
    exact CourantFischer.rayleigh_le_on_eigenvectorSpanTail A hA k x hx_unit hx

  -- Combined: For unit x ∈ W: R_{A+B}(x) ≤ λₖ(A) + λ₀(B)
  have h_RAB_upper : ∀ x : EuclideanSpace ℂ n, x ∈ W → ‖x‖ = 1 →
      (@inner ℂ (EuclideanSpace ℂ n) _ (Matrix.toEuclideanLin (A + B) x) x).re ≤
        hA.eigenvalues₀ k + hB.eigenvalues₀ 0 := by
    intro x hx hx_unit
    rw [rayleigh_add A B hA hB x]
    exact add_le_add (h_RA_upper x hx hx_unit) (h_RB_upper x hx_unit)

  -- Using Courant-Fischer min-max:
  -- λₖ(A+B) = inf_{dim V = n-k} sup_{x ∈ V} R(x) ≤ sup_{x ∈ W} R_{A+B}(x)

  have h_rayleighSup_bound : CourantFischer.rayleighSup (A + B) (hA.add hB) W ≤
      hA.eigenvalues₀ k + hB.eigenvalues₀ 0 := by
    unfold CourantFischer.rayleighSup CourantFischer.rayleighQuotient
    have hW_nonempty_local : ∃ x : W, x.val ≠ 0 := by
      have h_pos : 0 < Module.finrank ℂ W := by
        rw [h_dim_W]
        exact Nat.sub_pos_of_lt k.isLt
      exact CourantFischer.exists_nonzero_of_finrank_pos W h_pos
    haveI : Nonempty { x : W // x.val ≠ 0 } := by
      obtain ⟨x, hx⟩ := hW_nonempty_local
      exact ⟨⟨x, hx⟩⟩
    apply ciSup_le
    intro ⟨⟨x, hx_mem⟩, hx_ne⟩
    by_cases hx_norm : ‖x‖ = 0
    · exfalso; exact hx_ne (norm_eq_zero.mp hx_norm)
    · have hx_pos : 0 < ‖x‖ := norm_pos_iff.mpr (fun h => hx_ne h)
      let y := (1 / ‖x‖ : ℂ) • x
      have hy_unit : ‖y‖ = 1 := by
        simp only [y, norm_smul, one_div]
        rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx_pos,
            inv_mul_cancel₀ (ne_of_gt hx_pos)]
      have hy_mem : y ∈ W := Submodule.smul_mem W _ hx_mem

      have h_scale : (@inner ℂ (EuclideanSpace ℂ n) _ (Matrix.toEuclideanLin (A + B) x) x).re / ‖x‖^2 =
          (@inner ℂ (EuclideanSpace ℂ n) _ (Matrix.toEuclideanLin (A + B) y) y).re := by
        have hc_ne : (1 / ‖x‖ : ℂ) ≠ 0 := by
          simp only [one_div, ne_eq, inv_eq_zero, Complex.ofReal_eq_zero]
          exact ne_of_gt hx_pos
        have h := CourantFischer.rayleigh_scale_complex (A := A + B) hx_ne (1 / ‖x‖ : ℂ) hc_ne
        simp only [y] at hy_unit ⊢
        rw [hy_unit, one_pow, div_one] at h
        exact h.symm

      rw [h_scale]
      exact h_RAB_upper y hy_mem hy_unit

  -- Now we need: λₖ(A+B) ≤ rayleighSup(A+B, W)
  -- This is the Courant-Fischer min-max direction

  -- The tail eigenspace W of A has dimension n - k
  -- By Courant-Fischer min-max for A+B, λₖ(A+B) = inf_{dim V = n-k} sup R
  -- So λₖ(A+B) ≤ sup R on W (since W has dimension n-k)

  -- But wait, we need to verify the dimension formula.
  -- By Courant-Fischer min-max: λₖ(A+B) ≤ rayleighSup(A+B, W) for dim W = n - k

  have h_step1 : (hA.add hB).eigenvalues₀ k ≤ CourantFischer.rayleighSup (A + B) (hA.add hB) W := by
    have hW_nonempty : ∃ x : W, x.val ≠ 0 := by
      have h_pos : 0 < Module.finrank ℂ W := by
        rw [h_dim_W]
        exact Nat.sub_pos_of_lt k.isLt
      exact CourantFischer.exists_nonzero_of_finrank_pos W h_pos

    have h_dim_adjusted : Module.finrank ℂ W = Fintype.card n - k_succ.val + 1 := by
      rw [h_dim_W]
      have h_eq : k_succ.val = k.val + 1 := rfl
      rw [h_eq]
      have hk : k.val + 1 ≤ Fintype.card n := k.isLt
      have hn_pos : k.val < Fintype.card n := k.isLt
      omega

    have hk_pos : (0 : Fin (Fintype.card n + 1)) < k_succ := by
      simp only [Fin.lt_def, Fin.val_zero]
      exact Nat.zero_lt_succ k.val

    have h := CourantFischer.eigenvalue_le_rayleighSup (A + B) (hA.add hB) k_succ hk_pos W h_dim_adjusted
    convert h using 1

  exact le_trans h_step1 h_rayleighSup_bound

/-- **Weyl's Combined Bounds**: For Hermitian A, B:
    λₖ(A) + λₙ₋₁(B) ≤ λₖ(A+B) ≤ λₖ(A) + λ₀(B) -/
theorem weyl_eigenvalue_bounds (A B : Matrix n n ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (k : Fin (Fintype.card n)) :
    hA.eigenvalues₀ k + hB.eigenvalues₀ minEigenvalueIdx ≤ (hA.add hB).eigenvalues₀ k ∧
    (hA.add hB).eigenvalues₀ k ≤ hA.eigenvalues₀ k + hB.eigenvalues₀ 0 :=
  ⟨weyl_eigenvalue_lower_bound A B hA hB k, weyl_eigenvalue_upper_bound A B hA hB k⟩

end WeylEigenvalue

/-! ## Rank Equality for Aᴴ A

The key lemma `rank(Aᴴ A) = rank(A)` is provided by Mathlib as `Matrix.rank_conjTranspose_mul_self`.
We provide convenience aliases and additional lemmas needed for singular value arguments.

### Key results from Mathlib:
- `Matrix.rank_conjTranspose_mul_self : (Aᴴ * A).rank = A.rank`
- `Matrix.rank_conjTranspose : Aᴴ.rank = A.rank`

### Mathematical note:
The equality `rank(Aᴴ A) = rank(A)` follows from `ker(Aᴴ A) = ker(A)`:
- If Aᴴ Ax = 0, then ⟨Ax, Ax⟩ = xᴴ Aᴴ Ax = 0, so Ax = 0
- By rank-nullity: rank(A) = n - nullity(A) = n - nullity(Aᴴ A) = rank(Aᴴ A)
-/

section RankEquality

variable {m' n' : Type*} [Fintype m'] [Fintype n']

/-- `rank(Aᴴ A) = rank(A)` - alias for Mathlib's `rank_conjTranspose_mul_self`.

This is fundamental for relating singular values to eigenvalues:
- Singular values of A are square roots of eigenvalues of Aᴴ A
- rank(A) = #{i | σᵢ(A) ≠ 0} = #{i | λᵢ(Aᴴ A) ≠ 0} = rank(Aᴴ A) -/
theorem rank_conjTranspose_mul_self_eq (A : Matrix m' n' ℂ) :
    (Aᴴ * A).rank = A.rank :=
  Matrix.rank_conjTranspose_mul_self A

/-- `rank(A Aᴴ) = rank(A)` - the transpose version.

Follows from `rank_conjTranspose_mul_self` applied to Aᴴ. -/
theorem rank_mul_conjTranspose_eq (A : Matrix m' n' ℂ) :
    (A * Aᴴ).rank = A.rank := by
  have h1 : (A * Aᴴ).rank = Aᴴ.rank := by
    rw [← Matrix.rank_conjTranspose_mul_self Aᴴ]
    simp only [conjTranspose_conjTranspose]
  rw [h1, Matrix.rank_conjTranspose]

end RankEquality

/-! ## Singular Values Zero Beyond Rank

For a matrix of rank ≤ k, all singular values at indices ≥ k are zero.
This follows from:
1. `singularValues₀ A k = √(eigenvalues₀ (Aᴴ*A) k)`
2. `rank(Aᴴ*A) = rank(A)` (Rank Equality)
3. Eigenvalues₀ are sorted (descending) and nonnegative for PSD matrices
4. If rank ≤ k, then at most k eigenvalues are nonzero
5. Since eigenvalues₀ is antitone, eigenvalues₀ j = 0 for j ≥ k
6. Therefore singularValues₀ j = √0 = 0

This lemma is essential for Eckart-Young: if C has rank ≤ k, then σⱼ(C) = 0 for j ≥ k.
-/

section SingularValuesBeyondRank

open Matrix.SVD in
/-- For an antitone nonneg function, if at most k values are nonzero, then f(i) = 0 for i ≥ k.

This is a slight generalization of `antitone_nonneg_zeros_after_rank` from SVD.lean,
adapted for the square matrix case where we have a direct rank bound. -/
lemma antitone_nonneg_zeros_from_rank {m : ℕ} (f : Fin m → ℝ)
    (h_anti : Antitone f) (h_nonneg : ∀ i, 0 ≤ f i)
    (k : ℕ) (h_card : Fintype.card {i : Fin m // f i ≠ 0} ≤ k)
    (i : Fin m) (hi : k ≤ i.val) : f i = 0 := by
  by_contra h_ne
  -- If f i ≠ 0, then all f j for j ≤ i are also ≠ 0 (by antitone + nonneg)
  have h_all_nonzero : ∀ j : Fin m, j ≤ i → f j ≠ 0 := by
    intro j hji h_fj_zero
    have h_fi_pos : 0 < f i := (h_nonneg i).lt_of_ne' h_ne
    have h_fj_ge : f j ≥ f i := h_anti hji
    linarith [h_fj_zero.symm ▸ h_fj_ge]
  -- So {j | f j ≠ 0} ⊇ {j | j ≤ i}, which has at least i.val + 1 elements
  have h_count : i.val + 1 ≤ Fintype.card {j : Fin m // f j ≠ 0} := by
    have h_iic : (Finset.Iic i).card = i.val + 1 := by simp [Fin.card_Iic]
    calc i.val + 1 = (Finset.Iic i).card := h_iic.symm
      _ ≤ (Finset.univ.filter (fun j : Fin m => f j ≠ 0)).card := by
          apply Finset.card_le_card
          intro j hj
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact h_all_nonzero j (Finset.mem_Iic.mp hj)
      _ = Fintype.card {j : Fin m // f j ≠ 0} := by rw [Fintype.card_subtype]
  -- But i.val + 1 > k ≥ card {j | f j ≠ 0}, contradiction
  omega

omit [Nonempty n] in
/-- eigenvalues₀ at index ≥ rank are zero for square Hermitian PSD matrices.

For a square n × n positive semidefinite matrix A with rank r:
- eigenvalues₀ is antitone (sorted decreasing)
- eigenvalues₀ is nonneg
- #{i | eigenvalues₀ i ≠ 0} = r

Therefore eigenvalues₀ j = 0 for j.val ≥ r. -/
lemma eigenvalues₀_zero_from_rank_bound {A : Matrix n n ℂ} (hA : A.PosSemidef)
    (j : Fin (Fintype.card n)) (hj : A.rank ≤ j.val) :
    hA.isHermitian.eigenvalues₀ j = 0 := by
  -- eigenvalues₀ is nonneg for PSD
  have h_nonneg : ∀ i, 0 ≤ hA.isHermitian.eigenvalues₀ i :=
    PosSemidef_eigenvalues₀_nonneg hA
  -- eigenvalues₀ is antitone
  have h_anti : Antitone hA.isHermitian.eigenvalues₀ := hA.isHermitian.eigenvalues₀_antitone
  -- rank = card of nonzero eigenvalues
  have h_rank_eq : A.rank = Fintype.card {i : n // hA.isHermitian.eigenvalues i ≠ 0} :=
    hA.isHermitian.rank_eq_card_non_zero_eigs
  -- Transfer to eigenvalues₀
  have h_card_eq : Fintype.card {i : Fin (Fintype.card n) // hA.isHermitian.eigenvalues₀ i ≠ 0} =
      Fintype.card {i : n // hA.isHermitian.eigenvalues i ≠ 0} :=
    Matrix.SVD.Rectangular.card_nonzero_eigenvalues₀_eq_card_nonzero_eigenvalues hA.isHermitian
  have h_card_bound : Fintype.card {i : Fin (Fintype.card n) // hA.isHermitian.eigenvalues₀ i ≠ 0} ≤ j.val := by
    calc Fintype.card {i : Fin (Fintype.card n) // hA.isHermitian.eigenvalues₀ i ≠ 0}
      = Fintype.card {i : n // hA.isHermitian.eigenvalues i ≠ 0} := h_card_eq
      _ = A.rank := h_rank_eq.symm
      _ ≤ j.val := hj
  exact antitone_nonneg_zeros_from_rank hA.isHermitian.eigenvalues₀ h_anti h_nonneg
    j.val h_card_bound j (Nat.le_refl _)

omit [Nonempty n] in
/-- **Singular values are zero beyond matrix rank** (square case).

For a square n × n complex matrix A with rank r:
/-- For rank(A) = r, singular values σⱼ(A) = 0 for j ≥ r. -/
theorem singularValues₀_zero_beyond_rank (A : Matrix n n ℂ)
    (j : Fin (Fintype.card n)) (hj : A.rank ≤ j.val) :
    Matrix.SVD.singularValues₀ A j = 0 := by
  unfold Matrix.SVD.singularValues₀
  -- Need to show √(eigenvalues₀ j) = 0, i.e., eigenvalues₀ j = 0
  let hAHA := posSemidef_conjTranspose_mul_self A
  -- rank(Aᴴ*A) = rank(A)
  have h_rank_eq : (Aᴴ * A).rank = A.rank := Matrix.rank_conjTranspose_mul_self A
  -- eigenvalues₀ j = 0 since j ≥ rank(Aᴴ*A)
  have h_eig_zero : hAHA.isHermitian.eigenvalues₀ j = 0 := by
    apply eigenvalues₀_zero_from_rank_bound hAHA j
    rw [h_rank_eq]
    exact hj
  simp only [h_eig_zero, Real.sqrt_zero]

omit [Nonempty n] in
/-- Convenience form: singular values are zero at indices ≥ k if rank ≤ k. -/
theorem singularValues₀_zero_of_rank_le (A : Matrix n n ℂ) (k : ℕ)
    (hA : A.rank ≤ k) (j : Fin (Fintype.card n)) (hj : k ≤ j.val) :
    Matrix.SVD.singularValues₀ A j = 0 :=
  singularValues₀_zero_beyond_rank A j (Nat.le_trans hA hj)

end SingularValuesBeyondRank

/-! ## Weyl's Singular Value Perturbation

|σₖ(A) - σₖ(B)| ≤ σ₁(A - B). Uses σₖ(A)² = λₖ(Aᴴ A).
-/

section WeylSingularValue

/-- For a unit vector x, ‖Mx‖² ≤ σ₁(M)² = λ₁(MᴴM).

This is the operator norm bound: ‖Mx‖ ≤ ‖M‖·‖x‖ = σ₁(M) for unit x. -/
lemma norm_toEuclideanLin_sq_le_singularValue₀_sq (M : Matrix n n ℂ)
    (x : EuclideanSpace ℂ n) (hx : ‖x‖ = 1) :
    ‖Matrix.toEuclideanLin M x‖^2 ≤ (Matrix.SVD.singularValues₀ M 0)^2 := by
  -- ‖Mx‖² = Re⟨MᴴMx, x⟩ (Rayleigh quotient of MᴴM at x)
  have h_sq := CourantFischer.norm_sq_mul_eq_inner_AHA M x
  rw [h_sq]
  -- For unit x, the Rayleigh quotient equals Re⟨MᴴMx, x⟩
  have hMHM := posSemidef_conjTranspose_mul_self M
  -- Rayleigh quotient ≤ λ₀(MᴴM) for any unit vector
  have h_rayleigh := CourantFischer.rayleigh_le_eigenvalue_max (Mᴴ * M) hMHM.isHermitian x hx
  -- σ₁(M)² = λ₁(MᴴM) = eigenvalues₀ 0
  have h_sigma_sq : (Matrix.SVD.singularValues₀ M 0)^2 = hMHM.isHermitian.eigenvalues₀ 0 :=
    Matrix.SVD.singularValues₀_sq M 0
  rw [h_sigma_sq]
  exact h_rayleigh

/-- For a unit vector x, ‖Mx‖ ≤ σ₁(M). -/
lemma norm_toEuclideanLin_le_singularValue₀ (M : Matrix n n ℂ)
    (x : EuclideanSpace ℂ n) (hx : ‖x‖ = 1) :
    ‖Matrix.toEuclideanLin M x‖ ≤ Matrix.SVD.singularValues₀ M 0 := by
  have h_sq := norm_toEuclideanLin_sq_le_singularValue₀_sq M x hx
  have h_nonneg_l : 0 ≤ ‖Matrix.toEuclideanLin M x‖ := norm_nonneg _
  have h_nonneg_r : 0 ≤ Matrix.SVD.singularValues₀ M 0 := Matrix.SVD.singularValues₀_nonneg M 0
  -- From a² ≤ b² and a, b ≥ 0, we get a ≤ b
  nlinarith [sq_nonneg (‖Matrix.toEuclideanLin M x‖), sq_nonneg (Matrix.SVD.singularValues₀ M 0)]

omit [Nonempty n] in
/-- Triangle inequality for toEuclideanLin: ‖(A-B)x‖ = ‖Ax - Bx‖. -/
lemma toEuclideanLin_sub (A B : Matrix n n ℂ) (x : EuclideanSpace ℂ n) :
    Matrix.toEuclideanLin (A - B) x = Matrix.toEuclideanLin A x - Matrix.toEuclideanLin B x := by
  simp only [Matrix.toEuclideanLin_apply, Matrix.sub_mulVec]
  rfl

/-- For unit x: ‖Ax‖ ≤ ‖Bx‖ + ‖(A-B)x‖ ≤ ‖Bx‖ + σ₁(A-B). -/
lemma norm_toEuclideanLin_le_add_singularValue₀ (A B : Matrix n n ℂ)
    (x : EuclideanSpace ℂ n) (hx : ‖x‖ = 1) :
    ‖Matrix.toEuclideanLin A x‖ ≤ ‖Matrix.toEuclideanLin B x‖ + Matrix.SVD.singularValues₀ (A - B) 0 := by
  -- ‖Ax‖ = ‖Bx + (A-B)x‖ ≤ ‖Bx‖ + ‖(A-B)x‖ ≤ ‖Bx‖ + σ₁(A-B)
  have h_add : Matrix.toEuclideanLin A x =
      Matrix.toEuclideanLin B x + Matrix.toEuclideanLin (A - B) x := by
    calc Matrix.toEuclideanLin A x
        = Matrix.toEuclideanLin (B + (A - B)) x := by simp only [add_sub_cancel]
      _ = Matrix.toEuclideanLin B x + Matrix.toEuclideanLin (A - B) x := toEuclideanLin_add B (A - B) x
  rw [h_add]
  have h_tri : ‖Matrix.toEuclideanLin B x + Matrix.toEuclideanLin (A - B) x‖
      ≤ ‖Matrix.toEuclideanLin B x‖ + ‖Matrix.toEuclideanLin (A - B) x‖ := norm_add_le _ _
  have h_op : ‖Matrix.toEuclideanLin (A - B) x‖ ≤ Matrix.SVD.singularValues₀ (A - B) 0 :=
    norm_toEuclideanLin_le_singularValue₀ (A - B) x hx
  linarith

/-- **Weyl's Singular Value Perturbation** (one direction):
    σₖ(A) ≤ σₖ(B) + σ₁(A - B) -/
theorem weyl_singularValue_upper_aux (A B : Matrix n n ℂ) (k : Fin (Fintype.card n)) :
    Matrix.SVD.singularValues₀ A k ≤ Matrix.SVD.singularValues₀ B k + Matrix.SVD.singularValues₀ (A - B) 0 := by
  -- Key pointwise bound: For any unit x, ‖Ax‖ ≤ ‖Bx‖ + σ₁(A-B)
  have h_pointwise : ∀ x : EuclideanSpace ℂ n, ‖x‖ = 1 →
      ‖Matrix.toEuclideanLin A x‖ ≤ ‖Matrix.toEuclideanLin B x‖ + Matrix.SVD.singularValues₀ (A - B) 0 :=
    fun x hx => norm_toEuclideanLin_le_add_singularValue₀ A B x hx

  -- Strategy: Use Courant-Fischer for BᴴB. The tail eigenspace W of BᴴB has dimension n-k.
  -- For unit x ∈ W: ‖Bx‖² ≤ λₖ(BᴴB) = σₖ(B)², so ‖Bx‖ ≤ σₖ(B).
  -- Combined with h_pointwise: ‖Ax‖ ≤ σₖ(B) + σ₁(A-B) for all unit x ∈ W.
  -- By Courant-Fischer min-max: λₖ(AᴴA) ≤ sup_{x∈W} ‖Ax‖² ≤ (σₖ(B) + σ₁(A-B))².
  -- Taking square roots: σₖ(A) ≤ σₖ(B) + σ₁(A-B).

  -- Step 1: Set up the tail eigenspace of BᴴB
  let hBHB := (posSemidef_conjTranspose_mul_self B).isHermitian
  let W := CourantFischer.eigenvectorSpanTail hBHB k

  have h_dim_W : Module.finrank ℂ W = Fintype.card n - k.val :=
    CourantFischer.finrank_eigenvectorSpanTail (Bᴴ * B) hBHB k

  -- Step 2: For unit x ∈ W, we have ‖Bx‖² ≤ σₖ(B)²
  have h_Bx_bound : ∀ x : EuclideanSpace ℂ n, x ∈ W → ‖x‖ = 1 →
      ‖Matrix.toEuclideanLin B x‖^2 ≤ (Matrix.SVD.singularValues₀ B k)^2 := by
    intro x hx hx_unit
    -- ‖Bx‖² = Re⟨BᴴBx, x⟩ (Rayleigh quotient)
    have h_sq := CourantFischer.norm_sq_mul_eq_inner_AHA B x
    rw [h_sq]
    -- For x ∈ W (tail eigenspace of BᴴB): Re⟨BᴴBx, x⟩ ≤ λₖ(BᴴB)
    have h_rayleigh := CourantFischer.rayleigh_le_on_eigenvectorSpanTail (Bᴴ * B) hBHB k x hx_unit hx
    -- σₖ(B)² = λₖ(BᴴB)
    have h_sigma_sq : (Matrix.SVD.singularValues₀ B k)^2 = hBHB.eigenvalues₀ k :=
      Matrix.SVD.singularValues₀_sq B k
    rw [h_sigma_sq]
    exact h_rayleigh

  -- Step 3: Taking square roots gives ‖Bx‖ ≤ σₖ(B) for unit x ∈ W
  have h_Bx_norm_bound : ∀ x : EuclideanSpace ℂ n, x ∈ W → ‖x‖ = 1 →
      ‖Matrix.toEuclideanLin B x‖ ≤ Matrix.SVD.singularValues₀ B k := by
    intro x hx hx_unit
    have h_sq_ineq := h_Bx_bound x hx hx_unit
    have h_nonneg_l : 0 ≤ ‖Matrix.toEuclideanLin B x‖ := norm_nonneg _
    have h_nonneg_r : 0 ≤ Matrix.SVD.singularValues₀ B k := Matrix.SVD.singularValues₀_nonneg B k
    nlinarith [sq_nonneg (‖Matrix.toEuclideanLin B x‖), sq_nonneg (Matrix.SVD.singularValues₀ B k)]

  -- Step 4: Combined bound: For unit x ∈ W, ‖Ax‖ ≤ σₖ(B) + σ₁(A-B)
  have h_combined : ∀ x : EuclideanSpace ℂ n, x ∈ W → ‖x‖ = 1 →
      ‖Matrix.toEuclideanLin A x‖ ≤
        Matrix.SVD.singularValues₀ B k + Matrix.SVD.singularValues₀ (A - B) 0 := by
    intro x hx hx_unit
    calc ‖Matrix.toEuclideanLin A x‖
        ≤ ‖Matrix.toEuclideanLin B x‖ + Matrix.SVD.singularValues₀ (A - B) 0 := h_pointwise x hx_unit
      _ ≤ Matrix.SVD.singularValues₀ B k + Matrix.SVD.singularValues₀ (A - B) 0 := by
          have hb := h_Bx_norm_bound x hx hx_unit
          linarith

  -- Step 5: Squaring the combined bound gives ‖Ax‖² bound for unit x ∈ W
  have h_combined_sq : ∀ x : EuclideanSpace ℂ n, x ∈ W → ‖x‖ = 1 →
      ‖Matrix.toEuclideanLin A x‖^2 ≤
        (Matrix.SVD.singularValues₀ B k + Matrix.SVD.singularValues₀ (A - B) 0)^2 := by
    intro x hx hx_unit
    have h := h_combined x hx hx_unit
    have h_nonneg_l : 0 ≤ ‖Matrix.toEuclideanLin A x‖ := norm_nonneg _
    have h_nonneg_r : 0 ≤ Matrix.SVD.singularValues₀ B k + Matrix.SVD.singularValues₀ (A - B) 0 := by
      apply add_nonneg
      exact Matrix.SVD.singularValues₀_nonneg B k
      exact Matrix.SVD.singularValues₀_nonneg (A - B) 0
    exact sq_le_sq' (by linarith) h

  -- Step 6: For unit x ∈ W, ‖Ax‖² = Re⟨AᴴAx, x⟩ (Rayleigh quotient of AᴴA)
  have h_rayleigh_AHA : ∀ x : EuclideanSpace ℂ n, ‖x‖ = 1 →
      ‖Matrix.toEuclideanLin A x‖^2 =
        (@inner ℂ (EuclideanSpace ℂ n) _ (Matrix.toEuclideanLin (Aᴴ * A) x) x).re := by
    intro x _hx_unit
    exact CourantFischer.norm_sq_mul_eq_inner_AHA A x

  -- Step 7: By Courant-Fischer, λₖ(AᴴA) ≤ rayleighSup of AᴴA on W
  let hAHA := (posSemidef_conjTranspose_mul_self A).isHermitian
  let k_succ : Fin (Fintype.card n + 1) := ⟨k.val + 1, Nat.add_lt_add_right k.isLt 1⟩

  have h_dim_adjusted : Module.finrank ℂ W = Fintype.card n - k_succ.val + 1 := by
    rw [h_dim_W]
    have h_eq : k_succ.val = k.val + 1 := rfl
    rw [h_eq]
    omega

  have hk_pos : (0 : Fin (Fintype.card n + 1)) < k_succ := by
    simp only [Fin.lt_def, Fin.val_zero]
    exact Nat.zero_lt_succ k.val

  -- Need to show W has a nonzero vector for rayleighSup to be well-defined
  have hW_nonempty : ∃ x : W, x.val ≠ 0 := by
    have h_pos : 0 < Module.finrank ℂ W := by
      rw [h_dim_W]
      exact Nat.sub_pos_of_lt k.isLt
    exact CourantFischer.exists_nonzero_of_finrank_pos W h_pos

  -- Apply Courant-Fischer: λₖ(AᴴA) ≤ rayleighSup(AᴴA, W)
  have h_CF := CourantFischer.eigenvalue_le_rayleighSup (Aᴴ * A) hAHA k_succ hk_pos W h_dim_adjusted

  -- Step 8: Bound rayleighSup(AᴴA, W) by (σₖ(B) + σ₁(A-B))²
  have h_rayleighSup_bound : CourantFischer.rayleighSup (Aᴴ * A) hAHA W ≤
      (Matrix.SVD.singularValues₀ B k + Matrix.SVD.singularValues₀ (A - B) 0)^2 := by
    unfold CourantFischer.rayleighSup CourantFischer.rayleighQuotient
    haveI : Nonempty { x : W // x.val ≠ 0 } := by
      obtain ⟨x, hx⟩ := hW_nonempty
      exact ⟨⟨x, hx⟩⟩
    apply ciSup_le
    intro ⟨⟨x, hx_mem⟩, hx_ne⟩
    by_cases hx_norm : ‖x‖ = 0
    · exfalso; exact hx_ne (norm_eq_zero.mp hx_norm)
    · have hx_pos : 0 < ‖x‖ := norm_pos_iff.mpr (fun h => hx_ne h)
      let y := (1 / ‖x‖ : ℂ) • x
      have hy_unit : ‖y‖ = 1 := by
        simp only [y, norm_smul, one_div]
        rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx_pos,
            inv_mul_cancel₀ (ne_of_gt hx_pos)]
      have hy_mem : y ∈ W := Submodule.smul_mem W _ hx_mem

      -- The Rayleigh quotient R(x)/‖x‖² = R(y) for unit y
      have h_scale : (@inner ℂ (EuclideanSpace ℂ n) _ (Matrix.toEuclideanLin (Aᴴ * A) x) x).re / ‖x‖^2 =
          (@inner ℂ (EuclideanSpace ℂ n) _ (Matrix.toEuclideanLin (Aᴴ * A) y) y).re := by
        have hc_ne : (1 / ‖x‖ : ℂ) ≠ 0 := by
          simp only [one_div, ne_eq, inv_eq_zero, Complex.ofReal_eq_zero]
          exact ne_of_gt hx_pos
        have h := CourantFischer.rayleigh_scale_complex (A := Aᴴ * A) hx_ne (1 / ‖x‖ : ℂ) hc_ne
        simp only [y] at hy_unit ⊢
        rw [hy_unit, one_pow, div_one] at h
        exact h.symm

      rw [h_scale]
      -- Re⟨AᴴAy, y⟩ = ‖Ay‖² for unit y
      rw [← h_rayleigh_AHA y hy_unit]
      -- ‖Ay‖² ≤ (σₖ(B) + σ₁(A-B))²
      exact h_combined_sq y hy_mem hy_unit

  -- Step 9: Combine: σₖ(A)² = λₖ(AᴴA) ≤ rayleighSup ≤ (σₖ(B) + σ₁(A-B))²
  have h_sigma_sq : (Matrix.SVD.singularValues₀ A k)^2 = hAHA.eigenvalues₀ k :=
    Matrix.SVD.singularValues₀_sq A k

  -- The Courant-Fischer bound h_CF gives eigenvalues₀ ⟨k_succ - 1, _⟩ ≤ rayleighSup
  -- We need to show eigenvalues₀ ⟨k_succ - 1, _⟩ = eigenvalues₀ k
  have h_index : (⟨k_succ.val - 1, by omega⟩ : Fin (Fintype.card n)) = k := by
    ext; simp only [k_succ]; omega

  have h_eigenvalue_bound : hAHA.eigenvalues₀ k ≤
      (Matrix.SVD.singularValues₀ B k + Matrix.SVD.singularValues₀ (A - B) 0)^2 := by
    rw [← h_index]
    exact le_trans h_CF h_rayleighSup_bound

  -- Step 10: Take square roots to get σₖ(A) ≤ σₖ(B) + σ₁(A-B)
  have h_sq_ineq : (Matrix.SVD.singularValues₀ A k)^2 ≤
      (Matrix.SVD.singularValues₀ B k + Matrix.SVD.singularValues₀ (A - B) 0)^2 := by
    rw [h_sigma_sq]
    exact h_eigenvalue_bound

  have h_nonneg_l : 0 ≤ Matrix.SVD.singularValues₀ A k := Matrix.SVD.singularValues₀_nonneg A k
  have h_nonneg_r : 0 ≤ Matrix.SVD.singularValues₀ B k + Matrix.SVD.singularValues₀ (A - B) 0 := by
    apply add_nonneg
    exact Matrix.SVD.singularValues₀_nonneg B k
    exact Matrix.SVD.singularValues₀_nonneg (A - B) 0

  nlinarith [sq_nonneg (Matrix.SVD.singularValues₀ A k),
             sq_nonneg (Matrix.SVD.singularValues₀ B k + Matrix.SVD.singularValues₀ (A - B) 0)]

omit [Nonempty n] in
/-- Singular values of -M equal those of M: σₖ(-M) = σₖ(M).

This follows from (-M)ᴴ(-M) = MᴴM. -/
theorem singularValues₀_neg (M : Matrix n n ℂ) (k : Fin (Fintype.card n)) :
    Matrix.SVD.singularValues₀ (-M) k = Matrix.SVD.singularValues₀ M k := by
  unfold Matrix.SVD.singularValues₀
  simp only [conjTranspose_neg, neg_mul, mul_neg, neg_neg]

/-- **Weyl's Singular Value Perturbation Bound**:
    |σₖ(A) - σₖ(B)| ≤ σ₁(A - B)

This is the key inequality needed for Eckart-Young:
- For rank-k matrix C: σⱼ(C) = 0 for j ≥ k (Singular Values Beyond Rank)
- By this theorem: σⱼ(Σ) = |σⱼ(Σ) - σⱼ(C)| ≤ σ₁(Σ - C)

Proof: Apply `weyl_singularValue_upper_aux` both ways:
- σₖ(A) ≤ σₖ(B) + σ₁(A - B)  ⟹  σₖ(A) - σₖ(B) ≤ σ₁(A - B)
- σₖ(B) ≤ σₖ(A) + σ₁(B - A)  ⟹  σₖ(B) - σₖ(A) ≤ σ₁(A - B)

Combined: |σₖ(A) - σₖ(B)| ≤ σ₁(A - B) -/
theorem weyl_singularValue_perturbation (A B : Matrix n n ℂ) (k : Fin (Fintype.card n)) :
    |Matrix.SVD.singularValues₀ A k - Matrix.SVD.singularValues₀ B k| ≤
    Matrix.SVD.singularValues₀ (A - B) 0 := by
  rw [abs_le]
  constructor
  · -- -(σ₁(A-B)) ≤ σₖ(A) - σₖ(B)  ⟺  σₖ(B) - σₖ(A) ≤ σ₁(A-B)
    have h := weyl_singularValue_upper_aux B A k
    -- h : σₖ(B) ≤ σₖ(A) + σ₁(B - A)
    -- Need: σ₁(B - A) = σ₁(A - B)
    have h_symm : Matrix.SVD.singularValues₀ (B - A) 0 = Matrix.SVD.singularValues₀ (A - B) 0 := by
      -- σ(X) = σ(-X) since (−X)ᴴ(−X) = XᴴX
      have h_neg : B - A = -(A - B) := (neg_sub A B).symm
      rw [h_neg]
      exact singularValues₀_neg (A - B) 0
    rw [h_symm] at h
    linarith
  · -- σₖ(A) - σₖ(B) ≤ σ₁(A-B)
    have h := weyl_singularValue_upper_aux A B k
    linarith

/-- Weyl perturbation applied to a zero matrix: σₖ(A) ≤ σ₁(A).

When B = 0, all singular values of B are 0, so σₖ(A) ≤ σₖ(0) + σ₁(A - 0) = σ₁(A). -/
theorem singularValues₀_le_singularValues₀_zero (A : Matrix n n ℂ) (k : Fin (Fintype.card n)) :
    Matrix.SVD.singularValues₀ A k ≤ Matrix.SVD.singularValues₀ A 0 := by
  exact Matrix.SVD.singularValues₀_antitone A (Fin.zero_le k)

/-- For a zero-rank matrix (σⱼ = 0 for all j), perturbation gives: σⱼ(A) ≤ σ₁(A - C).

This is the specific form needed for Eckart-Young when C has rank ≤ k and j ≥ k. -/
theorem singularValue_perturbation_zero_at_j (A C : Matrix n n ℂ)
    (j : Fin (Fintype.card n)) (hC : Matrix.SVD.singularValues₀ C j = 0) :
    Matrix.SVD.singularValues₀ A j ≤ Matrix.SVD.singularValues₀ (A - C) 0 := by
  have h := weyl_singularValue_perturbation A C j
  rw [hC, sub_zero, abs_of_nonneg (Matrix.SVD.singularValues₀_nonneg A j)] at h
  exact h

end WeylSingularValue

/-! ## Thompson's Singular Value Interlacing

Thompson's theorem provides stronger bounds than Weyl perturbation when one matrix
/-! ## Thompson's Singular Value Interlacing

For rank(B) ≤ r: σ_{i+r}(A) ≤ σ_i(A + B).
-/

section ThompsonInterlacing

omit [Nonempty n] in
/-- Helper: On the kernel of B, the linear maps of A and A + B coincide. -/
theorem toEuclideanLin_eq_on_ker (A B : Matrix n n ℂ) (x : EuclideanSpace ℂ n)
    (hx : B.mulVec (WithLp.equiv 2 (n → ℂ) x) = 0) :
    Matrix.toEuclideanLin (A + B) x = Matrix.toEuclideanLin A x := by
  simp only [Matrix.toEuclideanLin_apply, Matrix.add_mulVec]
  -- WithLp.equiv 2 (n → ℂ) x = x.ofLp
  have h : B.mulVec x.ofLp = 0 := hx
  rw [h, add_zero]

omit [Nonempty n] in
/-- Helper: The norm of (A + B)x equals ‖Ax‖ when Bx = 0. -/
theorem norm_add_eq_on_ker (A B : Matrix n n ℂ) (x : EuclideanSpace ℂ n)
    (hx : B.mulVec (WithLp.equiv 2 (n → ℂ) x) = 0) :
    ‖Matrix.toEuclideanLin (A + B) x‖ = ‖Matrix.toEuclideanLin A x‖ := by
  rw [toEuclideanLin_eq_on_ker A B x hx]

omit [Nonempty n] in
/-- The kernel of toEuclideanLin C has dimension at least n - rank(C).
    This is the key dimension bound for Thompson interlacing. -/
lemma finrank_ker_toEuclideanLin_ge' (C : Matrix n n ℂ) :
    Module.finrank ℂ (LinearMap.ker (Matrix.toEuclideanLin C)) ≥ Fintype.card n - C.rank := by
  have h_rn := LinearMap.finrank_range_add_finrank_ker (Matrix.toEuclideanLin C)
  have h_domain : Module.finrank ℂ (EuclideanSpace ℂ n) = Fintype.card n := finrank_euclideanSpace
  rw [h_domain] at h_rn
  have h_rank_eq : C.rank = Module.finrank ℂ (LinearMap.range (Matrix.toEuclideanLin C)) := by
    unfold Matrix.rank
    let e : (n → ℂ) ≃ₗ[ℂ] EuclideanSpace ℂ n := (WithLp.linearEquiv 2 ℂ (n → ℂ)).symm
    have h_range : LinearMap.range (Matrix.toEuclideanLin C) =
        Submodule.map e.toLinearMap (LinearMap.range C.mulVecLin) := by
      ext x
      simp only [LinearMap.mem_range, Submodule.mem_map, LinearEquiv.coe_toLinearMap]
      constructor
      · rintro ⟨v, hv⟩
        use C.mulVecLin (e.symm v)
        refine ⟨⟨e.symm v, rfl⟩, ?_⟩
        simp only [Matrix.toEuclideanLin_apply] at hv
        rw [← hv]
        simp only [Matrix.mulVecLin_apply]
        rfl
      · rintro ⟨y, ⟨w, hw⟩, hy⟩
        use e w
        simp only [Matrix.toEuclideanLin_apply, Matrix.mulVecLin_apply] at hw ⊢
        rw [← hy, ← hw]
        rfl
    rw [h_range]
    exact (Submodule.equivMapOfInjective e.toLinearMap e.injective _).finrank_eq
  omega

/-- **Thompson's Singular Value Interlacing Inequality**

For matrices A, B with rank(B) ≤ r:
  σ_{i+r}(A) ≤ σ_i(A + B)

The proof uses the Courant-Fischer max-min characterization:
  σ_k(M)² = max_{dim V = k+1} min_{x ∈ V, ‖x‖=1} ‖Mx‖²

For the optimal V* achieving σ_{i+r}(A), and any (n-i)-dim W used in σ_i(A+B):
- dim(V*) = i + r + 1
- dim(W) = n - i
- dim(ker B) ≥ n - r
- By Grassmann: dim(V* ∩ W ∩ ker B) ≥ (i+r+1) + (n-i) + (n-r) - 2n = 1

So there exists x ∈ V* ∩ W ∩ ker B with ‖x‖ = 1:
- ‖(A+B)x‖ = ‖Ax‖ (since x ∈ ker B)
- ‖Ax‖ ≥ σ_{i+r}(A) (since x ∈ V* and V* achieves the max-min)
- max_{x ∈ W} ‖(A+B)x‖ ≥ ‖(A+B)x‖ ≥ σ_{i+r}(A)

Taking min over W: σ_i(A+B) ≥ σ_{i+r}(A)
-/
theorem thompson_interlacing (A B : Matrix n n ℂ) (r : ℕ) (hr : B.rank ≤ r)
    (i : Fin (Fintype.card n)) (hi : i.val + r < Fintype.card n) :
    Matrix.SVD.singularValues₀ A ⟨i.val + r, hi⟩ ≤ Matrix.SVD.singularValues₀ (A + B) i := by
  -- The key index: j = i + r
  let j : Fin (Fintype.card n) := ⟨i.val + r, hi⟩

  -- Setup: Work with squared singular values via eigenvalues of A^H A and (A+B)^H(A+B)
  let hAHA := (posSemidef_conjTranspose_mul_self A).isHermitian
  let hApBHA := (posSemidef_conjTranspose_mul_self (A + B)).isHermitian

  -- The (j+1)-dimensional "head" eigenspace V* of A^H A
  -- This is the span of eigenvectors u₀, ..., u_j corresponding to the j+1 largest eigenvalues
  let V_star := CourantFischer.eigenvectorSpanHead hAHA ⟨j.val + 1, Nat.add_lt_add_right j.isLt 1⟩

  have hV_dim : Module.finrank ℂ V_star = j.val + 1 :=
    CourantFischer.finrank_eigenvectorSpanHead (Aᴴ * A) hAHA ⟨j.val + 1, _⟩

  -- The kernel of B has dimension ≥ n - r
  let KerB := LinearMap.ker (Matrix.toEuclideanLin B)

  have hKer_dim : Module.finrank ℂ KerB ≥ Fintype.card n - r := by
    have h := finrank_ker_toEuclideanLin_ge' B
    calc Module.finrank ℂ KerB
      ≥ Fintype.card n - B.rank := h
      _ ≥ Fintype.card n - r := by omega

  -- Strategy: For the min-max formulation of σ_i(A+B)², we need to show:
  -- For ANY (n-i)-dim subspace W, the sup over W of ‖(A+B)x‖² is ≥ σ_j(A)²
  --
  -- We prove this by showing V* ∩ W ∩ ker(B) is nonempty (dimension counting),
  -- and for any unit x in this intersection: ‖(A+B)x‖ = ‖Ax‖ ≥ σ_j(A)

  -- Prove the inequality via squaring (both sides nonneg)
  have h_nonneg_l : 0 ≤ Matrix.SVD.singularValues₀ A j := Matrix.SVD.singularValues₀_nonneg A j
  have h_nonneg_r : 0 ≤ Matrix.SVD.singularValues₀ (A + B) i := Matrix.SVD.singularValues₀_nonneg (A + B) i

  -- It suffices to show the squared inequality
  -- σ_j(A) ≤ σ_i(A+B) ⟺ σ_j(A)² ≤ σ_i(A+B)² (since both are nonneg)
  have h_sq_iff : Matrix.SVD.singularValues₀ A j ≤ Matrix.SVD.singularValues₀ (A + B) i ↔
      (Matrix.SVD.singularValues₀ A j)^2 ≤ (Matrix.SVD.singularValues₀ (A + B) i)^2 := by
    constructor
    · intro h
      exact sq_le_sq' (by linarith) h
    · intro h
      nlinarith [sq_nonneg (Matrix.SVD.singularValues₀ A j),
                 sq_nonneg (Matrix.SVD.singularValues₀ (A + B) i)]

  rw [h_sq_iff]

  -- Convert to eigenvalue inequality via singularValues₀_sq
  have h_sq_A : (Matrix.SVD.singularValues₀ A j)^2 = hAHA.eigenvalues₀ j :=
    Matrix.SVD.singularValues₀_sq A j
  have h_sq_AB : (Matrix.SVD.singularValues₀ (A + B) i)^2 = hApBHA.eigenvalues₀ i :=
    Matrix.SVD.singularValues₀_sq (A + B) i

  rw [h_sq_A, h_sq_AB]

  -- Use min-max for (A+B)^H(A+B): λ_i = inf_{dim W = n-i} sup R_{(A+B)^H(A+B)}(W)
  -- By eigenvalue_le_rayleighSup, λ_i ≤ rayleighSup on any (n-i)-dim subspace

  -- We'll construct a specific subspace where we can bound the rayleighSup from below

  -- The tail eigenspace of (A+B)^H(A+B) of dimension n - i
  let TailAB := CourantFischer.eigenvectorSpanTail hApBHA i

  have hTail_dim : Module.finrank ℂ TailAB = Fintype.card n - i.val :=
    CourantFischer.finrank_eigenvectorSpanTail ((A + B)ᴴ * (A + B)) hApBHA i

  -- Key dimension check for triple intersection
  -- dim(V*) + dim(TailAB) + dim(KerB) = (j+1) + (n-i) + (≥ n-r)
  --                                   = (i+r+1) + (n-i) + (≥ n-r)
  --                                   ≥ 2n + 1

  -- First intersect V* with KerB
  -- dim(V* ∩ KerB) ≥ dim(V*) + dim(KerB) - n = (j+1) + (n-r) - n = i + 1

  have h_sum_VK : Module.finrank ℂ V_star + Module.finrank ℂ KerB > Module.finrank ℂ (EuclideanSpace ℂ n) := by
    rw [hV_dim, finrank_euclideanSpace]
    have hKer_ge := hKer_dim
    calc (j.val + 1) + Module.finrank ℂ KerB
      ≥ (j.val + 1) + (Fintype.card n - r) := Nat.add_le_add_left hKer_ge (j.val + 1)
      _ = (i.val + r + 1) + (Fintype.card n - r) := rfl
      _ > Fintype.card n := by omega

  -- Get intersection V* ∩ KerB
  let V_K := V_star ⊓ KerB

  have hVK_pos : 0 < Module.finrank ℂ V_K := by
    have h := CourantFischer.finrank_inf_ge_of_sum_gt V_star KerB h_sum_VK
    rw [hV_dim, finrank_euclideanSpace] at h
    have hKer_ge := hKer_dim
    -- h : V_K dim ≥ (j.val + 1) + KerB dim - n
    -- hKer_ge : KerB dim ≥ n - r
    -- Goal: 0 < V_K dim
    -- We have: V_K dim ≥ (j+1) + (n-r) - n = j+1-r = i+r+1-r = i+1 > 0
    have h_lb : (j.val + 1) + (Fintype.card n - r) - Fintype.card n ≤
        (j.val + 1) + Module.finrank ℂ KerB - Fintype.card n := by
      apply Nat.sub_le_sub_right
      exact Nat.add_le_add_left hKer_ge (j.val + 1)
    have h_pos : 0 < (j.val + 1) + (Fintype.card n - r) - Fintype.card n := by
      have hj_eq : j.val = i.val + r := rfl
      have hr_le : r ≤ Fintype.card n := by
        have : i.val + r < Fintype.card n := hi
        omega
      -- (j+1) + (n-r) - n = (i+r+1) + (n-r) - n = i + 1 > 0
      have h_simplify : (j.val + 1) + (Fintype.card n - r) - Fintype.card n = i.val + 1 := by
        rw [hj_eq]; omega
      rw [h_simplify]
      omega
    calc 0 < (j.val + 1) + (Fintype.card n - r) - Fintype.card n := h_pos
      _ ≤ (j.val + 1) + Module.finrank ℂ KerB - Fintype.card n := h_lb
      _ ≤ Module.finrank ℂ ↥V_K := h

  -- Now intersect (V* ∩ KerB) with TailAB
  -- Need: dim(V_K) + dim(TailAB) > n

  have h_sum_final : Module.finrank ℂ V_K + Module.finrank ℂ TailAB > Module.finrank ℂ (EuclideanSpace ℂ n) := by
    rw [hTail_dim, finrank_euclideanSpace]
    have h := CourantFischer.finrank_inf_ge_of_sum_gt V_star KerB h_sum_VK
    rw [hV_dim, finrank_euclideanSpace] at h
    have hKer_ge := hKer_dim
    -- h : V_K dim ≥ (j+1) + KerB dim - n
    -- Goal: V_K dim + (n - i) > n
    have h_vk_lb : Module.finrank ℂ V_K ≥ (j.val + 1) + (Fintype.card n - r) - Fintype.card n := by
      have h_lb : (j.val + 1) + (Fintype.card n - r) ≤ (j.val + 1) + Module.finrank ℂ KerB := by
        exact Nat.add_le_add_left hKer_ge (j.val + 1)
      have h_sub_le : (j.val + 1) + (Fintype.card n - r) - Fintype.card n ≤
          (j.val + 1) + Module.finrank ℂ KerB - Fintype.card n := by
        apply Nat.sub_le_sub_right h_lb
      exact le_trans h_sub_le h
    have : j.val = i.val + r := rfl
    -- Compute the lower bound: (i+r+1) + (n-r) - n = i + 1
    have h_simplify : (j.val + 1) + (Fintype.card n - r) - Fintype.card n = i.val + 1 := by
      rw [this]
      have hr_le : r ≤ Fintype.card n := by
        have : i.val + r < Fintype.card n := hi
        omega
      omega
    rw [h_simplify] at h_vk_lb
    -- h_vk_lb : V_K dim ≥ i + 1
    -- Goal: V_K dim + (n - i) > n
    -- (i+1) + (n-i) = n + 1 > n ✓
    have hi_lt : i.val < Fintype.card n := i.isLt
    omega

  -- Get a nonzero vector in the triple intersection
  obtain ⟨x, hx_ne, hx_VK, hx_Tail⟩ := CourantFischer.exists_nonzero_in_intersection V_K TailAB h_sum_final

  -- x is in V*, KerB, and TailAB
  have hx_Vstar : x ∈ V_star := (Submodule.mem_inf.mp hx_VK).1
  have hx_KerB : x ∈ KerB := (Submodule.mem_inf.mp hx_VK).2

  -- Normalize x to get a unit vector
  have hx_pos : 0 < ‖x‖ := norm_pos_iff.mpr hx_ne
  let y := (1 / ‖x‖ : ℂ) • x

  have hy_unit : ‖y‖ = 1 := by
    simp only [y, norm_smul, one_div]
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx_pos,
        inv_mul_cancel₀ (ne_of_gt hx_pos)]

  have hy_Vstar : y ∈ V_star := Submodule.smul_mem V_star _ hx_Vstar
  have hy_KerB : y ∈ KerB := Submodule.smul_mem KerB _ hx_KerB
  have hy_Tail : y ∈ TailAB := Submodule.smul_mem TailAB _ hx_Tail

  -- Key property: On ker(B), ‖(A+B)y‖ = ‖Ay‖
  have h_eq_norm : ‖Matrix.toEuclideanLin (A + B) y‖ = ‖Matrix.toEuclideanLin A y‖ := by
    apply norm_add_eq_on_ker A B y
    -- Need: B · y = 0 in the form B.mulVec (WithLp.equiv 2 (n → ℂ)) y = 0
    have h_mem : y ∈ LinearMap.ker (Matrix.toEuclideanLin B) := hy_KerB
    simp only [LinearMap.mem_ker, Matrix.toEuclideanLin_apply] at h_mem
    -- h_mem : WithLp.toLp 2 (B.mulVec y.ofLp) = 0 (in EuclideanSpace)
    -- Goal: B.mulVec ((WithLp.equiv 2 (n → ℂ)) y) = 0 (in n → ℂ)
    show B.mulVec ((WithLp.equiv 2 (n → ℂ)) y) = 0
    have h_ofLp : (WithLp.equiv 2 (n → ℂ)) y = y.ofLp := rfl
    rw [h_ofLp]
    -- From h_mem : WithLp.toLp 2 (B.mulVec y.ofLp) = 0
    -- Since WithLp.toLp 2 = (WithLp.equiv 2 _).symm, this means
    -- (WithLp.equiv 2 _).symm (B.mulVec y.ofLp) = 0
    -- Applying (WithLp.equiv 2 _) to both sides:
    -- B.mulVec y.ofLp = (WithLp.equiv 2 _) 0 = 0
    have h_eq : WithLp.toLp 2 (B.mulVec y.ofLp) = WithLp.toLp 2 (0 : n → ℂ) := by
      rw [h_mem]; rfl
    have h_inj : Function.Injective (WithLp.toLp 2 : (n → ℂ) → WithLp 2 (n → ℂ)) :=
      (WithLp.equiv 2 (n → ℂ)).symm.injective
    exact h_inj h_eq

  -- For y ∈ V* (head eigenspace of A^H A) with ‖y‖ = 1:
  -- The Rayleigh quotient R_{A^H A}(y) ≥ λ_j(A^H A) = σ_j(A)²
  -- And R_{A^H A}(y) = ‖Ay‖²

  have h_rayleigh_lower : ‖Matrix.toEuclideanLin A y‖^2 ≥ hAHA.eigenvalues₀ j := by
    -- ‖Ay‖² = Re⟨A^H A y, y⟩
    have h_eq := CourantFischer.norm_sq_mul_eq_inner_AHA A y
    rw [h_eq]
    -- y ∈ eigenvectorSpanHead means R(y) ≥ λ_j
    have hj_bound : j.val + 1 < Fintype.card n + 1 := Nat.add_lt_add_right j.isLt 1
    have hk : (0 : Fin (Fintype.card n + 1)) < ⟨j.val + 1, hj_bound⟩ := by
      simp only [Fin.lt_def, Fin.val_zero]
      omega
    have h_ge := CourantFischer.rayleigh_ge_on_eigenvectorSpanHead (Aᴴ * A) hAHA
      ⟨j.val + 1, hj_bound⟩ hk y hy_unit hy_Vstar
    -- The index in rayleigh_ge_on_eigenvectorSpanHead is k-1 = (j+1)-1 = j
    -- h_ge : R(y) ≥ eigenvalues₀ ⟨(j+1) - 1, _⟩ = eigenvalues₀ j
    convert h_ge using 2

  -- For y ∈ TailAB (tail eigenspace of (A+B)^H(A+B)) with ‖y‖ = 1:
  -- The Rayleigh quotient R_{(A+B)^H(A+B)}(y) ≤ λ_i((A+B)^H(A+B)) = σ_i(A+B)²
  -- And R_{(A+B)^H(A+B)}(y) = ‖(A+B)y‖²

  have h_rayleigh_upper : ‖Matrix.toEuclideanLin (A + B) y‖^2 ≤ hApBHA.eigenvalues₀ i := by
    -- ‖(A+B)y‖² = Re⟨(A+B)^H(A+B) y, y⟩
    have h_eq := CourantFischer.norm_sq_mul_eq_inner_AHA (A + B) y
    rw [h_eq]
    -- y ∈ eigenvectorSpanTail means R(y) ≤ λ_i
    exact CourantFischer.rayleigh_le_on_eigenvectorSpanTail ((A + B)ᴴ * (A + B)) hApBHA i y hy_unit hy_Tail

  -- Chain: σ_j(A)² = hAHA.eigenvalues₀ j ≤ ‖Ay‖² = ‖(A+B)y‖² ≤ hApBHA.eigenvalues₀ i = σ_i(A+B)²
  calc hAHA.eigenvalues₀ j
      ≤ ‖Matrix.toEuclideanLin A y‖^2 := h_rayleigh_lower
    _ = ‖Matrix.toEuclideanLin (A + B) y‖^2 := by rw [h_eq_norm]
    _ ≤ hApBHA.eigenvalues₀ i := h_rayleigh_upper

/-- **Thompson Interlacing for Low-Rank Subtraction**

For matrices A, C with rank(C) ≤ k:
  σⱼ(A) ≤ σⱼ₋ₖ(A - C)  for j ≥ k

This is the form needed for Eckart-Young: the tail singular values of A
are bounded by the leading singular values of A - C.

Proof: Apply thompson_interlacing with M = A, N = -C:
  σ_{i+k}(A) ≤ σᵢ(A + (-C)) = σᵢ(A - C) when rank(-C) = rank(C) ≤ k
  With j = i + k (so i = j - k): σⱼ(A) ≤ σⱼ₋ₖ(A - C) ✓
-/
theorem interlacing_low_rank_subtraction (A C : Matrix n n ℂ) (k : ℕ)
    (hC : C.rank ≤ k) (j : Fin (Fintype.card n)) (hj : k ≤ j.val) :
    Matrix.SVD.singularValues₀ A j ≤
    Matrix.SVD.singularValues₀ (A - C) ⟨j.val - k, by omega⟩ := by
  -- (-C).rank = C.rank because negation is a bijection
  have h_neg_rank : (-C).rank ≤ k := by
    have h : (-C).rank = C.rank := by
      unfold Matrix.rank
      -- Use that mulVecLin (-C) = -mulVecLin C and range(-f) = range(f)
      have hmulvec : (-C).mulVecLin = -C.mulVecLin := by
        apply LinearMap.ext
        intro v
        simp only [Matrix.mulVecLin_apply, Matrix.neg_mulVec, LinearMap.neg_apply]
      rw [hmulvec, LinearMap.range_neg]
    rw [h]
    exact hC

  let i : Fin (Fintype.card n) := ⟨j.val - k, by omega⟩

  have h_i_plus_k : i.val + k = j.val := Nat.sub_add_cancel hj

  have hi : i.val + k < Fintype.card n := h_i_plus_k ▸ j.isLt

  have h_idx_eq : (⟨i.val + k, hi⟩ : Fin (Fintype.card n)) = j := Fin.ext h_i_plus_k

  calc Matrix.SVD.singularValues₀ A j
      = Matrix.SVD.singularValues₀ A ⟨i.val + k, hi⟩ := by rw [h_idx_eq]
    _ ≤ Matrix.SVD.singularValues₀ (A + (-C)) i := thompson_interlacing A (-C) k h_neg_rank i hi
    _ = Matrix.SVD.singularValues₀ (A - C) i := by rw [sub_eq_add_neg]

/-- Variant of interlacing with explicit index bounds for Eckart-Young applications. -/
theorem interlacing_for_eckart_young (A C : Matrix n n ℂ) (k : ℕ)
    (hC : C.rank ≤ k) (j : ℕ) (hj_ge : k ≤ j) (hj_lt : j < Fintype.card n) :
    Matrix.SVD.singularValues₀ A ⟨j, hj_lt⟩ ≤
    Matrix.SVD.singularValues₀ (A - C) ⟨j - k, by omega⟩ :=
  interlacing_low_rank_subtraction A C k hC ⟨j, hj_lt⟩ hj_ge

end ThompsonInterlacing

end Matrix.WeylInequality
