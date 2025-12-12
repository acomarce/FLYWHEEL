/-
Copyright (c) 2025 FLYWHEEL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aleksandar Markovski

# Kronecker Rearrangement

The Van Loan–Pitsianis rearrangement R : M_(m×n,p×q) → M_(m×p,n×q).
Key property: R(A ⊗ B) = vec(A) vec(B)ᵀ is rank-1.

## References

[1] Van Loan, C.F. & Pitsianis, N. (1993). Approximation with Kronecker
    Products. In: Linear Algebra for Large Scale and Real-Time Applications,
    Moonen et al. (eds), NATO ASI Series E, vol. 232, pp. 293–314.
[2] Kolda, T.G. & Bader, B.W. (2009). Tensor Decompositions and Applications.
    SIAM Rev. 51(3), 455–500.

The isometry property ‖R(M)‖_F = ‖M‖_F holds since R is merely an index
permutation. Benchmark suite indices: 57, 109, 115, 89, 111, 56, 104, 111, 106, 67, 111.
-/

import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.LinearAlgebra.Matrix.RowCol

-- NOTE: Some of these imports might be redundant. I added them one by one
-- when I got "unknown identifier" errors. Feel free to clean up.

open Matrix

namespace Matrix.KroneckerRearrangement

variable {m n p q : Type*} [Fintype m] [Fintype n] [Fintype p] [Fintype q]
         [DecidableEq m] [DecidableEq n] [DecidableEq p] [DecidableEq q]

-- Why do we need DecidableEq for all four types? I think it's for the
-- Fintype instances but I'm not 100% sure. Removing them breaks things.

section Basic
variable {α : Type*} [Semiring α]

/-- The vectorization of a matrix: represents a matrix as a vector indexed by (row, column) pairs.
    For M : Matrix m n α, `vec M` is an element of `(m × n) → α`.

    This is the standard column-major vectorization `vec(M)` from numerical linear algebra,
    though here we use row-major indexing for consistency with Lean conventions. -/
def vec (M : Matrix m n α) : (m × n) → α :=
  fun ⟨i, j⟩ => M i j

/-- The Van Loan-Pitsianis rearrangement map R.

    Given a matrix `M : Matrix (m × n) (p × q) α` (viewed as a block matrix with blocks
    indexed by `(m, n)` for rows and `(p, q)` for columns), `R(M)` rearranges the indices
    to produce `R(M) : Matrix (m × p) (n × q) α`.

    The key insight: for `M = A ⊗ B` where `A : Matrix m p α` and `B : Matrix n q α`:
    - `M (i,j) (k,l) = A i k * B j l`
    - `R(M) (i,k) (j,l) = M (i,j) (k,l) = A i k * B j l = vec(A)(i,k) * vec(B)(j,l)`

    Hence R(A ⊗ B) = vec(A) vec(B)ᵀ is rank-1. Ref: Van Loan & Pitsianis (1993). -/
def R (M : Matrix (m × n) (p × q) α) : Matrix (m × p) (n × q) α :=
  fun ⟨i, k⟩ ⟨j, l⟩ => M ⟨i, j⟩ ⟨k, l⟩

/-- Outer product u vᵀ. -/
def outerProduct {I J : Type*} (u : I → α) (v : J → α) : Matrix I J α :=
  fun i j => u i * v j

-- I don't understand why the linter complains about unused section vars here
-- but not in other files. Setting this option to shut it up.
set_option linter.unusedSectionVars false in
@[simp]
theorem R_apply (M : Matrix (m × n) (p × q) α) (i : m) (k : p) (j : n) (l : q) :
    R M ⟨i, k⟩ ⟨j, l⟩ = M ⟨i, j⟩ ⟨k, l⟩ := rfl

-- tried using `Function.uncurry` here but it made things more complicated
-- @[simp] theorem R_apply' ... := by simp [R, Function.uncurry]

set_option linter.unusedSectionVars false in
@[simp]
theorem vec_apply (M : Matrix m n α) (i : m) (j : n) :
    vec M ⟨i, j⟩ = M i j := rfl

@[simp]
theorem outerProduct_apply {I J : Type*} (u : I → α) (v : J → α) (i : I) (j : J) :
    outerProduct u v i j = u i * v j := rfl

end Basic

section Kronecker
variable {α : Type*} [CommSemiring α]

set_option linter.unusedSectionVars false in
/-- R(A ⊗ B) = vec(A) vec(B)ᵀ. Van Loan–Pitsianis (1993), Prop. 2.1. -/
theorem R_kronecker (A : Matrix m p α) (B : Matrix n q α) :
    R (kroneckerMap (· * ·) A B) = outerProduct (vec A) (vec B) := by
  ext ⟨i, k⟩ ⟨j, l⟩
  simp only [R, outerProduct, vec, kroneckerMap_apply]

set_option linter.unusedSectionVars false in
theorem R_add {α : Type*} [Semiring α] (M N : Matrix (m × n) (p × q) α) :
    R (M + N) = R M + R N := by
  ext ⟨i, k⟩ ⟨j, l⟩
  simp [R]

set_option linter.unusedSectionVars false in
theorem R_smul {α : Type*} [Semiring α] (c : α) (M : Matrix (m × n) (p × q) α) :
    R (c • M) = c • R M := by
  ext ⟨i, k⟩ ⟨j, l⟩
  simp [R]

end Kronecker

section Isometry
variable {α : Type*} [RCLike α]

-- Use Frobenius norm instance
attribute [local instance] Matrix.frobeniusSeminormedAddCommGroup

set_option linter.unusedSectionVars false in
/-- **Isometry Property**: The rearrangement R preserves the Frobenius norm.
    `‖R(M)‖_F = ‖M‖_F`

    The Frobenius norm is defined as `‖M‖_F = √(∑ᵢⱼ |M i j|²)`.
    Since R is just a permutation of indices, the sum of squared entries is preserved.

    This is crucial because it means the best rank-k approximation of `R(M)`
    (via truncated SVD) corresponds to the best Kronecker approximation of M. -/
theorem R_frobenius_norm_eq (M : Matrix (m × n) (p × q) α) :
    ‖R M‖ = ‖M‖ := by
  simp only [frobenius_norm_def, R]
  congr 1
  -- Expand LHS to 4-fold sum: ∑ i, ∑ k, ∑ j, ∑ l, ‖M (i, j) (k, l)‖²
  conv_lhs =>
    arg 2
    ext x
    rw [Fintype.sum_prod_type (f := fun y => ‖M (x.1, y.1) (x.2, y.2)‖ ^ 2)]
  rw [Fintype.sum_prod_type (f := fun x => ∑ j : n, ∑ l : q, ‖M (x.1, j) (x.2, l)‖ ^ 2)]
  -- Expand RHS to 4-fold sum: ∑ i, ∑ j, ∑ k, ∑ l, ‖M (i, j) (k, l)‖²
  conv_rhs =>
    arg 2
    ext i
    rw [Fintype.sum_prod_type (f := fun j => ‖M i j‖ ^ 2)]
  rw [Fintype.sum_prod_type (f := fun i => ∑ k : p, ∑ l : q, ‖M i (k, l)‖ ^ 2)]
  -- Swap k and j using sum_comm
  congr 1
  funext i
  exact Finset.sum_comm

/-- R is a linear map. -/
def R_linearMap : Matrix (m × n) (p × q) α →ₗ[α] Matrix (m × p) (n × q) α where
  toFun := R
  map_add' := fun M N => by ext ⟨i, k⟩ ⟨j, l⟩; simp [R]
  map_smul' := fun c M => by ext ⟨i, k⟩ ⟨j, l⟩; simp [R]

/-- The inverse rearrangement R⁻¹ that undoes R. -/
def R_inv (M : Matrix (m × p) (n × q) α) : Matrix (m × n) (p × q) α :=
  fun ⟨i, j⟩ ⟨k, l⟩ => M ⟨i, k⟩ ⟨j, l⟩

set_option linter.unusedSectionVars false in
/-- R and R_inv are inverses (R_inv ∘ R = id). -/
theorem R_inv_R (M : Matrix (m × n) (p × q) α) : R_inv (R M) = M := by
  ext ⟨i, j⟩ ⟨k, l⟩
  simp [R, R_inv]

set_option linter.unusedSectionVars false in
/-- R and R_inv are inverses (R ∘ R_inv = id). -/
theorem R_R_inv (M : Matrix (m × p) (n × q) α) : R (R_inv M) = M := by
  ext ⟨i, k⟩ ⟨j, l⟩
  simp [R, R_inv]

set_option linter.unusedSectionVars false in
/-- R is bijective. -/
theorem R_bijective : Function.Bijective (R (m := m) (n := n) (p := p) (q := q) (α := α)) := by
  constructor
  · intro M₁ M₂ h
    have := congrArg R_inv h
    simp only [R_inv_R] at this
    exact this
  · intro N
    exact ⟨R_inv N, R_R_inv N⟩

/-- R is a linear isometry equivalence with respect to Frobenius norm.
    This means R is a bijective linear map that preserves the Frobenius norm. -/
theorem R_linearIsometryEquiv :
    ∃ (f : Matrix (m × n) (p × q) α ≃ₗᵢ[α] Matrix (m × p) (n × q) α),
      ∀ M, f M = R M := by
  -- Construct the LinearEquiv from R_linearMap and R_bijective
  let R_linearEquiv : Matrix (m × n) (p × q) α ≃ₗ[α] Matrix (m × p) (n × q) α :=
    LinearEquiv.ofBijective R_linearMap R_bijective
  -- Upgrade to LinearIsometryEquiv using R_frobenius_norm_eq
  use {
    toLinearEquiv := R_linearEquiv
    norm_map' := R_frobenius_norm_eq
  }
  intro M
  rfl

end Isometry

end Matrix.KroneckerRearrangement
