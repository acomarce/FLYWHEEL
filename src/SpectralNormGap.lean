/-
Copyright (c) 2025 FLYWHEEL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aleksandar Markovski
-/
module

public import MatrixNormRelations

/-!
# Spectral Norm Bounds for Kronecker Approximation

`R⁻¹` is a Frobenius isometry (`R_inv_frobenius_norm_eq`) but not a spectral one, so spectral
errors transfer through it only as upper bounds:
- `R_inv_spectral_le_frobenius`: ‖R⁻¹ M‖₂ ≤ ‖M‖_F;
- `spectral_error_bound_via_R`: ‖C - R⁻¹ M‖₂ ≤ ‖R C - M‖_F;
- `R_inv_outerProduct_spectral_bound`: ‖R⁻¹(u vᵀ)‖₂ ≤ ‖u‖·‖v‖.

The first bound is attained when R⁻¹ M has rank one
(`Matrix.Coherence.R_inv_spectral_eq_frobenius_R_outerProduct`), and it is not tight in general:
for M = R(1), ‖R⁻¹ M‖₂ = 1 < √(#m · #n) = ‖M‖_F (`R_inv_spectral_lt_frobenius_R_one`). With
m = n = Fin 2 this is R⁻¹(vec I₂ (vec I₂)ᵀ) = I₄.

## References

[1] Van Loan & Pitsianis (1993). NATO ASI Series E vol 232.
[2] Golub & Van Loan (2013). Matrix Computations, 4th ed.
-/

public section

open scoped ComplexOrder Matrix
open Matrix

namespace Matrix.Kronecker.SpectralBounds

variable {m n p q : Type*}
variable [Fintype m] [Fintype n] [Fintype p] [Fintype q]
variable [DecidableEq m] [DecidableEq n] [DecidableEq p] [DecidableEq q]

/-! ## Part A: Outer Product Norms

We establish the basic facts about norms of rank-1 matrices (outer products).
-/

section OuterProductNorms

-- Use Frobenius norm instance for matrices
attribute [local instance] Matrix.frobeniusSeminormedAddCommGroup

omit [DecidableEq m] [DecidableEq n] in
/-- The Frobenius norm squared of an outer product of EuclideanSpace vectors.
    ‖u vᵀ‖_F² = (Σᵢ Σⱼ |u(i)v(j)|²) = (Σᵢ |u(i)|²)(Σⱼ |v(j)|²) = ‖u‖² ‖v‖²

    **Proof:** Use NNReal/nnnorm approach to avoid Real rpow issues. -/
lemma outerProduct_frobenius_norm_sq' (u : EuclideanSpace ℂ m) (v : EuclideanSpace ℂ n) :
    ‖KroneckerRearrangement.outerProduct u v‖ ^ 2 = ‖u‖ ^ 2 * ‖v‖ ^ 2 := by
  -- Use nnnorm version to avoid Real.rpow issues
  have h : ‖KroneckerRearrangement.outerProduct u v‖₊ ^ 2 = ‖u‖₊ ^ 2 * ‖v‖₊ ^ 2 := by
    rw [frobenius_nnnorm_def]
    simp only [NNReal.rpow_two, KroneckerRearrangement.outerProduct]
    -- Convert rpow (1/2) to sqrt
    rw [← NNReal.sqrt_eq_rpow, NNReal.sq_sqrt]
    simp_rw [nnnorm_mul, mul_pow]
    rw [← Fintype.sum_mul_sum]
    congr 1 <;> rw [EuclideanSpace.nnnorm_eq, NNReal.sq_sqrt]
  -- Convert NNReal to Real
  have h1 : (‖KroneckerRearrangement.outerProduct u v‖₊ : ℝ) ^ 2 = (‖u‖₊ : ℝ) ^ 2 * (‖v‖₊ : ℝ) ^ 2 := by
    simp only [← NNReal.coe_pow, ← NNReal.coe_mul, h]
  simp only [coe_nnnorm] at h1
  exact h1

omit [DecidableEq m] [DecidableEq n] in
/-- The Frobenius norm of an outer product equals the product of Euclidean vector norms.
    ‖u vᵀ‖_F = ‖u‖ · ‖v‖ -/
lemma outerProduct_frobenius_norm' (u : EuclideanSpace ℂ m) (v : EuclideanSpace ℂ n) :
    ‖KroneckerRearrangement.outerProduct u v‖ = ‖u‖ * ‖v‖ := by
  have h := outerProduct_frobenius_norm_sq' u v
  have h_nonneg_lhs : 0 ≤ ‖KroneckerRearrangement.outerProduct u v‖ := norm_nonneg _
  have h_nonneg_rhs : 0 ≤ ‖u‖ * ‖v‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  -- HACK: nlinarith is magic here. I don't fully understand why it works but it does.
  -- I think it's doing: (a - b)^2 >= 0 and (a + b)^2 >= 0 implies a = b when a^2 = b^2
  -- and both are nonneg. But there should be a cleaner way...
  nlinarith [sq_nonneg (‖KroneckerRearrangement.outerProduct u v‖ - ‖u‖ * ‖v‖),
             sq_nonneg (‖KroneckerRearrangement.outerProduct u v‖ + ‖u‖ * ‖v‖)]

end OuterProductNorms

/-! ## Part B: R⁻¹ Frobenius Isometry

We prove that R_inv also preserves Frobenius norm (by composing with R).
-/

section RInvIsometry

attribute [local instance] Matrix.frobeniusSeminormedAddCommGroup

/-- R_inv is a Frobenius isometry: ‖R_inv M‖_F = ‖M‖_F -/
lemma R_inv_frobenius_norm_eq (M : Matrix (m × p) (n × q) ℂ) :
    ‖KroneckerRearrangement.R_inv M‖ = ‖M‖ := by
  -- Use R ∘ R_inv = id and R is an isometry
  have h : KroneckerRearrangement.R (KroneckerRearrangement.R_inv M) = M :=
    KroneckerRearrangement.R_R_inv M
  calc ‖KroneckerRearrangement.R_inv M‖
      = ‖KroneckerRearrangement.R (KroneckerRearrangement.R_inv M)‖ := by
          rw [KroneckerRearrangement.R_frobenius_norm_eq]
    _ = ‖M‖ := by rw [h]

end RInvIsometry

/-! ## Part C: Rank-1 Spectral Bound (THE CRUX)

This is the key result: when R⁻¹ acts on a rank-1 matrix (outer product),
the spectral norm is bounded using the Frobenius isometry property.

**The Key Mathematical Insight:**
‖R⁻¹(u vᵀ)‖₂ ≤ ‖R⁻¹(u vᵀ)‖_F = ‖u vᵀ‖_F = ‖u‖·‖v‖

For unit vectors u, v this gives ‖R⁻¹(u vᵀ)‖₂ ≤ 1. The bound is an upper bound only; see
`R_inv_spectral_lt_frobenius_R_one` for an example where it is not attained.
-/

section Rank1SpectralBound

-- We need both norm instances available
-- L2 operator norm (spectral norm) uses Matrix.instL2OpNormedAddCommGroup
-- Frobenius norm uses Matrix.frobeniusSeminormedAddCommGroup

/-! ### Spectral norm ≤ Frobenius norm -/

/-- **L2 operator norm is bounded by Frobenius norm** for any matrix: ‖A‖₂ ≤ ‖A‖_F.
    This is `spectral_le_frobenius_rect` (SVD.lean) with the Frobenius norm written through
    `Matrix.frobeniusSeminormedAddCommGroup`. -/
private theorem l2_opNorm_le_frobenius {m' n' : Type*}
    [Fintype m'] [Fintype n'] [DecidableEq n']
    (A : Matrix m' n' ℂ) :
    @Norm.norm _ Matrix.instL2OpNormedAddCommGroup.toNorm A ≤
      @Norm.norm _ Matrix.frobeniusSeminormedAddCommGroup.toNorm A := by
  classical
  exact spectral_le_frobenius_rect A

/-! ### Main theorems -/

/-- **Main theorem**: spectral norm of R⁻¹ on matrices is bounded by Frobenius norm.
    Since R is a Frobenius isometry and spectral ≤ Frobenius, we get:
    ‖R⁻¹(M)‖₂ ≤ ‖M‖_F

    The proof uses:
    1. ‖R⁻¹(M)‖₂ ≤ ‖R⁻¹(M)‖_F (spectral ≤ Frobenius)
    2. ‖R⁻¹(M)‖_F = ‖M‖_F (R isometry) -/
theorem R_inv_spectral_le_frobenius
    (M : Matrix (m × p) (n × q) ℂ) :
    @Norm.norm _ Matrix.instL2OpNormedAddCommGroup.toNorm (KroneckerRearrangement.R_inv M) ≤
    @Norm.norm _ Matrix.frobeniusSeminormedAddCommGroup.toNorm M := by
  -- Step 1: spectral norm ≤ Frobenius norm
  have h1 : @Norm.norm _ Matrix.instL2OpNormedAddCommGroup.toNorm (KroneckerRearrangement.R_inv M) ≤
            @Norm.norm _ Matrix.frobeniusSeminormedAddCommGroup.toNorm (KroneckerRearrangement.R_inv M) :=
    l2_opNorm_le_frobenius _
  -- Step 2: R_inv is a Frobenius isometry
  have h2 : @Norm.norm _ Matrix.frobeniusSeminormedAddCommGroup.toNorm (KroneckerRearrangement.R_inv M) =
            @Norm.norm _ Matrix.frobeniusSeminormedAddCommGroup.toNorm M :=
    R_inv_frobenius_norm_eq M
  calc @Norm.norm _ Matrix.instL2OpNormedAddCommGroup.toNorm (KroneckerRearrangement.R_inv M)
      ≤ @Norm.norm _ Matrix.frobeniusSeminormedAddCommGroup.toNorm (KroneckerRearrangement.R_inv M) := h1
    _ = @Norm.norm _ Matrix.frobeniusSeminormedAddCommGroup.toNorm M := h2

/-- **Main theorem for outer products**: spectral norm of R⁻¹(u vᵀ) is bounded by ‖u‖·‖v‖.
    ‖R⁻¹(u vᵀ)‖₂ ≤ ‖u vᵀ‖_F = ‖u‖·‖v‖

    NOTE: Uses EuclideanSpace (L2 norm) on vectors, which is required for the identity
    ‖u vᵀ‖_F = ‖u‖·‖v‖ to hold. -/
theorem R_inv_outerProduct_spectral_bound
    (u : EuclideanSpace ℂ (m × p)) (v : EuclideanSpace ℂ (n × q)) :
    @Norm.norm _ Matrix.instL2OpNormedAddCommGroup.toNorm
      (KroneckerRearrangement.R_inv (KroneckerRearrangement.outerProduct u v)) ≤
    ‖u‖ * ‖v‖ := by
  -- Use the general bound
  have h := R_inv_spectral_le_frobenius (KroneckerRearrangement.outerProduct u v)
  -- The Frobenius norm of outer product = product of norms
  have h_frob : @Norm.norm _ Matrix.frobeniusSeminormedAddCommGroup.toNorm
      (KroneckerRearrangement.outerProduct u v) = ‖u‖ * ‖v‖ :=
    outerProduct_frobenius_norm' u v
  calc @Norm.norm _ Matrix.instL2OpNormedAddCommGroup.toNorm
        (KroneckerRearrangement.R_inv (KroneckerRearrangement.outerProduct u v))
      ≤ @Norm.norm _ Matrix.frobeniusSeminormedAddCommGroup.toNorm
          (KroneckerRearrangement.outerProduct u v) := h
    _ = ‖u‖ * ‖v‖ := h_frob

/-- Corollary: For unit vectors in EuclideanSpace, ‖R⁻¹(u vᵀ)‖₂ ≤ 1 -/
theorem R_inv_outerProduct_spectral_bound_unit
    (u : EuclideanSpace ℂ (m × p)) (v : EuclideanSpace ℂ (n × q))
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    @Norm.norm _ Matrix.instL2OpNormedAddCommGroup.toNorm
      (KroneckerRearrangement.R_inv (KroneckerRearrangement.outerProduct u v)) ≤ 1 := by
  have h := R_inv_outerProduct_spectral_bound u v
  rw [hu, hv, mul_one] at h
  exact h

end Rank1SpectralBound

/-! ## Upper Bound for Spectral Norm of Kronecker Approximation Error

‖C - R⁻¹ M‖₂ ≤ ‖R C - M‖_F for every M. For M the rank-1 truncated SVD of R(C), the right
side is √(Σᵢ≥₁ σᵢ²) over the singular values σᵢ of R(C), 0-indexed
(`Matrix.TightBounds.kroneckerApprox_error_sq`).
-/

section UpperBound

/-! ### R linearity lemmas -/

omit [Fintype m] [Fintype n] [Fintype p] [Fintype q]
  [DecidableEq m] [DecidableEq n] [DecidableEq p] [DecidableEq q] in
/-- R distributes over subtraction. -/
lemma R_sub (M N : Matrix (m × n) (p × q) ℂ) :
    KroneckerRearrangement.R (M - N) = KroneckerRearrangement.R M - KroneckerRearrangement.R N := by
  ext ⟨i, k⟩ ⟨j, l⟩
  simp only [KroneckerRearrangement.R, sub_apply]

omit [Fintype m] [Fintype n] [Fintype p] [Fintype q]
  [DecidableEq m] [DecidableEq n] [DecidableEq p] [DecidableEq q] in
/-- R_inv distributes over subtraction. -/
lemma R_inv_sub (M N : Matrix (m × p) (n × q) ℂ) :
    KroneckerRearrangement.R_inv (M - N) =
    KroneckerRearrangement.R_inv M - KroneckerRearrangement.R_inv N := by
  ext ⟨i, j⟩ ⟨k, l⟩
  simp only [KroneckerRearrangement.R_inv, sub_apply]

attribute [local instance] Matrix.frobeniusSeminormedAddCommGroup

/-! ### Main Upper Bound Theorem -/

/-- **Main Upper Bound Theorem:**
    For a matrix C and any matrix M in the rearranged space, the spectral norm
    of C - R⁻¹(M) is bounded by the Frobenius norm of R(C) - M.

    This is the core inequality that connects:
    - Spectral norm approximation quality of Kronecker decomposition
    - Frobenius norm error in the rearranged SVD space

    In particular, for M = truncatedSVD_rect (R C) 1 (the rank-1 truncated SVD of R(C)),
    C - R⁻¹ M is the error of the Frobenius-optimal Kronecker approximation
    (`Matrix.TightBounds.kroneckerApprox`).

    Proof:
    ‖C - R⁻¹(M)‖₂ = ‖R⁻¹(R(C)) - R⁻¹(M)‖₂      [R⁻¹ ∘ R = id]
                  = ‖R⁻¹(R(C) - M)‖₂            [R⁻¹ is linear]
                  ≤ ‖R(C) - M‖_F                [bound] -/
theorem spectral_error_bound_via_R
    (C : Matrix (m × n) (p × q) ℂ) (M : Matrix (m × p) (n × q) ℂ) :
    @Norm.norm _ Matrix.instL2OpNormedAddCommGroup.toNorm (C - KroneckerRearrangement.R_inv M) ≤
    @Norm.norm _ Matrix.frobeniusSeminormedAddCommGroup.toNorm (KroneckerRearrangement.R C - M) := by
  -- Step 1: C = R⁻¹(R(C)), so C - R⁻¹(M) = R⁻¹(R(C)) - R⁻¹(M)
  have h_R_inv_R : KroneckerRearrangement.R_inv (KroneckerRearrangement.R C) = C :=
    KroneckerRearrangement.R_inv_R C
  -- Step 2: R⁻¹(R(C)) - R⁻¹(M) = R⁻¹(R(C) - M) by linearity
  have h_linear : KroneckerRearrangement.R_inv (KroneckerRearrangement.R C) -
                  KroneckerRearrangement.R_inv M =
                  KroneckerRearrangement.R_inv (KroneckerRearrangement.R C - M) := by
    rw [← R_inv_sub]
  -- Step 3: Apply bound
  calc @Norm.norm _ Matrix.instL2OpNormedAddCommGroup.toNorm (C - KroneckerRearrangement.R_inv M)
      = @Norm.norm _ Matrix.instL2OpNormedAddCommGroup.toNorm
          (KroneckerRearrangement.R_inv (KroneckerRearrangement.R C) - KroneckerRearrangement.R_inv M) := by
        rw [h_R_inv_R]
    _ = @Norm.norm _ Matrix.instL2OpNormedAddCommGroup.toNorm
          (KroneckerRearrangement.R_inv (KroneckerRearrangement.R C - M)) := by
        rw [h_linear]
    _ ≤ @Norm.norm _ Matrix.frobeniusSeminormedAddCommGroup.toNorm (KroneckerRearrangement.R C - M) :=
        R_inv_spectral_le_frobenius _

end UpperBound

/-! ## Square Matrix Specialization

For a square matrix A, the spectral error of the rank-k truncated SVD is at most its Frobenius
error √(Σᵢ≥ₖ σᵢ²). It is in fact exactly σₖ
(`Matrix.SVD.spectral_error_truncatedSVD`).
-/

section SquareCase

variable {n' : Type*} [Fintype n'] [DecidableEq n']

attribute [local instance] Matrix.frobeniusSeminormedAddCommGroup

/-- **Combined Spectral-Frobenius Bound:**
    The spectral norm of the truncated SVD error is bounded by the square root of
    the sum of squared tail singular values.

    ‖A - truncatedSVD A k‖₂ ≤ √(Σᵢ≥ₖ σᵢ²) -/
theorem spectral_error_le_sqrt_sum_tail_sq (A : Matrix n' n' ℂ) (k : ℕ) :
    @Norm.norm _ Matrix.instL2OpNormedAddCommGroup.toNorm (A - Matrix.SVD.truncatedSVD A k) ≤
    Real.sqrt (∑ i : n', (Matrix.SVD.truncatedSingularValues_tail A k i) ^ 2) := by
  -- ‖A - Aₖ‖₂ ≤ ‖A - Aₖ‖_F = √(Σ tail²)
  have h_spectral_le_frob := l2_opNorm_le_frobenius (A - Matrix.SVD.truncatedSVD A k)
  have h_frob_sq := FrobeniusNorm.frobenius_error_truncatedSVD A k
  -- ‖A - Aₖ‖_F = √(‖A - Aₖ‖_F²) = √(Σ tail²)
  have h_frob_eq : @Norm.norm _ Matrix.frobeniusSeminormedAddCommGroup.toNorm
      (A - Matrix.SVD.truncatedSVD A k) =
      Real.sqrt (∑ i : n', (Matrix.SVD.truncatedSingularValues_tail A k i) ^ 2) := by
    have h_nonneg : 0 ≤ @Norm.norm _ Matrix.frobeniusSeminormedAddCommGroup.toNorm
        (A - Matrix.SVD.truncatedSVD A k) := norm_nonneg _
    rw [← Real.sqrt_sq h_nonneg, h_frob_sq]
  calc @Norm.norm _ Matrix.instL2OpNormedAddCommGroup.toNorm (A - Matrix.SVD.truncatedSVD A k)
      ≤ @Norm.norm _ Matrix.frobeniusSeminormedAddCommGroup.toNorm (A - Matrix.SVD.truncatedSVD A k) :=
        h_spectral_le_frob
    _ = Real.sqrt (∑ i : n', (Matrix.SVD.truncatedSingularValues_tail A k i) ^ 2) := h_frob_eq

end SquareCase

/-! ## Outer Product Bounds

Bounds for outer products u v* and for R⁻¹ applied to them. The R⁻¹ bound
‖R⁻¹(u vᵀ)‖₂ ≤ ‖u vᵀ‖_F = ‖u‖·‖v‖ is not tight in general: write u = vec A and v = vec B, so
R⁻¹(outerProduct u v) = A ⊗ B (by `R_kronecker`), whose spectral norm ‖A‖₂·‖B‖₂ is less than
‖A‖_F·‖B‖_F = ‖u‖·‖v‖ unless A or B is 0 or both have rank 1.
`R_inv_spectral_lt_frobenius_R_one` formalizes the case A = B = 1.
-/

section OuterProductBounds

/-! ### Part A: Rank-1 Matrix Norm Bounds

For rank-1 matrices M = u vᵀ, the spectral norm is bounded by the Frobenius norm:
‖u vᵀ‖₂ ≤ ‖u vᵀ‖_F = ‖u‖·‖v‖. Only this upper bound is proved here. The equality
‖u vᵀ‖₂ = ‖u‖·‖v‖ is proved later, in CoherenceCharacterization
(`Matrix.Coherence.outerProduct_spectral_norm_eq`).
-/

attribute [local instance] Matrix.frobeniusSeminormedAddCommGroup

omit [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] in
/-- Helper: outerProduct of zero vector is zero matrix. -/
lemma outerProduct_zero_left (v : EuclideanSpace ℂ n) :
    KroneckerRearrangement.outerProduct (0 : EuclideanSpace ℂ m) v = 0 := by
  ext i j; simp [KroneckerRearrangement.outerProduct]

omit [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] in
/-- Helper: outerProduct with zero vector on right is zero matrix. -/
lemma outerProduct_zero_right (u : EuclideanSpace ℂ m) :
    KroneckerRearrangement.outerProduct u (0 : EuclideanSpace ℂ n) = 0 := by
  ext i j; simp [KroneckerRearrangement.outerProduct]

omit [DecidableEq m] in
/-- The spectral norm of an outer product is bounded above by the product of vector norms.
    Upper bound: ‖u vᵀ‖₂ ≤ ‖u‖ · ‖v‖ -/
theorem outerProduct_spectral_norm_le (u : EuclideanSpace ℂ m) (v : EuclideanSpace ℂ n) :
    @Norm.norm _ Matrix.instL2OpNormedAddCommGroup.toNorm
      (KroneckerRearrangement.outerProduct u v) ≤ ‖u‖ * ‖v‖ := by
  calc @Norm.norm _ Matrix.instL2OpNormedAddCommGroup.toNorm
        (KroneckerRearrangement.outerProduct u v)
      ≤ @Norm.norm _ Matrix.frobeniusSeminormedAddCommGroup.toNorm
          (KroneckerRearrangement.outerProduct u v) := l2_opNorm_le_frobenius _
    _ = ‖u‖ * ‖v‖ := outerProduct_frobenius_norm' u v

/-! ### Part B: R⁻¹ Bounds for Outer Products

An example where ‖R⁻¹ M‖₂ ≤ ‖M‖_F is strict. The upper bound for outer products is
`R_inv_outerProduct_spectral_bound` above; equality cases are in CoherenceCharacterization
(`Matrix.Coherence.R_inv_spectral_eq_frobenius_R_outerProduct`).
-/

/-- **The bound ‖R⁻¹ M‖₂ ≤ ‖M‖_F is not tight in general.** For M = R(1), with 1 the identity
    of Matrix (m × n) (m × n) ℂ and #m · #n ≥ 2:
    ‖R⁻¹ M‖₂ = ‖1‖₂ = 1 < √(#m · #n) = ‖1‖_F = ‖M‖_F.
    For m = n = Fin 2 this is R⁻¹(vec I₂ (vec I₂)ᵀ) = I₄. -/
theorem R_inv_spectral_lt_frobenius_R_one [Nonempty m] [Nonempty n]
    (h : 1 < Fintype.card (m × n)) :
    @Norm.norm _ Matrix.instL2OpNormedAddCommGroup.toNorm
      (KroneckerRearrangement.R_inv (KroneckerRearrangement.R (1 : Matrix (m × n) (m × n) ℂ))) <
    @Norm.norm _ Matrix.frobeniusSeminormedAddCommGroup.toNorm
      (KroneckerRearrangement.R (1 : Matrix (m × n) (m × n) ℂ)) := by
  rw [KroneckerRearrangement.R_inv_R]
  -- ‖1‖₂ = 1, the C*-norm of the identity
  have h_one : @Norm.norm _ Matrix.instL2OpNormedAddCommGroup.toNorm
      (1 : Matrix (m × n) (m × n) ℂ) = 1 := CStarRing.norm_one
  -- ‖R 1‖_F² = ‖1‖_F² = #m · #n
  have h_frob_sq : @Norm.norm _ Matrix.frobeniusSeminormedAddCommGroup.toNorm
      (KroneckerRearrangement.R (1 : Matrix (m × n) (m × n) ℂ)) ^ 2 = Fintype.card (m × n) := by
    rw [KroneckerRearrangement.R_frobenius_norm_eq, ← Matrix.diagonal_one,
      FrobeniusNorm.frobenius_norm_sq_diagonal]
    simp
  have h_card : (1 : ℝ) < Fintype.card (m × n) := by exact_mod_cast h
  have h_nonneg : 0 ≤ @Norm.norm _ Matrix.frobeniusSeminormedAddCommGroup.toNorm
      (KroneckerRearrangement.R (1 : Matrix (m × n) (m × n) ℂ)) := norm_nonneg _
  rw [h_one]
  nlinarith

/-! ### Part C: The Frobenius-to-spectral ratio

For A ≠ 0 the ratio ‖A‖_F / ‖A‖₂ = √(Σᵢ σᵢ²) / σ₀ (0-indexed, σ₀ largest) is the square root of
the stable rank. (It is unrelated to `Matrix.Coherence.spectralGap`, which is σ₀ - σ₁.)

The ratio is always ≥ 1 (`frobenius_spectral_ratio_ge_one`) and at most √rank(A)
(`Matrix.Coherence.coherenceFactor_le_one`). It equals 1 exactly when rank A ≤ 1
(`Matrix.Coherence.norm_eq_frobeniusNorm'_iff_rank_le_one`, square matrices).
-/

/-- The ratio ‖A‖_F / ‖A‖₂ is at least 1 for nonzero A. It is the square root of the stable
    rank; equality holds exactly for rank one
    (`Matrix.Coherence.norm_eq_frobeniusNorm'_iff_rank_le_one`). -/
theorem frobenius_spectral_ratio_ge_one {n' : Type*} [Fintype n'] [DecidableEq n']
    (A : Matrix n' n' ℂ) (hA : A ≠ 0) :
    @Norm.norm _ Matrix.frobeniusSeminormedAddCommGroup.toNorm A /
    @Norm.norm _ Matrix.instL2OpNormedAddCommGroup.toNorm A ≥ 1 := by
  have h_spectral_pos : 0 < @Norm.norm _ Matrix.instL2OpNormedAddCommGroup.toNorm A := by
    rw [norm_pos_iff]
    exact hA
  have h_le : @Norm.norm _ Matrix.instL2OpNormedAddCommGroup.toNorm A ≤
              @Norm.norm _ Matrix.frobeniusSeminormedAddCommGroup.toNorm A :=
    l2_opNorm_le_frobenius A
  rw [ge_iff_le, one_le_div h_spectral_pos]
  exact h_le

end OuterProductBounds

/-! ## Rank and Frobenius Identities

`R(A ⊗ B)` has rank at most 1 (`rank_R_kronecker_le_one`), and the Frobenius norm squared is
the sum of the squared singular values (`frobenius_norm_sq_eq_sum_singularValues_sq`).

The Frobenius-optimal Kronecker approximation (Van Loan–Pitsianis, `Matrix.TightBounds.kroneckerApprox`)
need not minimize the spectral error ‖C - A ⊗ B‖₂, because R does not preserve the spectral
norm. In the rearranged space there is no such gap: the rank-1 truncated SVD of R(C) is
optimal in both norms (`Matrix.TightBounds.eckart_young_frobenius_rect`,
`Matrix.TightBounds.eckart_young_spectral_rect`).
-/

section RankBounds

/-- Rank of an outer product is ≤ 1. -/
lemma rank_outerProduct_le_one {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (u : I → ℂ) (v : J → ℂ) :
    (KroneckerRearrangement.outerProduct u v).rank ≤ 1 := by
  -- KroneckerRearrangement.outerProduct is essentially vecMulVec
  -- Convert to Matrix.vecMulVec and use the existing Mathlib theorem
  have h_eq : KroneckerRearrangement.outerProduct u v = Matrix.vecMulVec u v := by
    ext i j
    simp [KroneckerRearrangement.outerProduct, Matrix.vecMulVec]
  rw [h_eq]
  exact Matrix.rank_vecMulVec_le u v

/-- The rank of R(A ⊗ B) is at most 1.
    This follows from R_kronecker: R(A ⊗ B) = outerProduct (vec A) (vec B). -/
theorem rank_R_kronecker_le_one (A : Matrix m p ℂ) (B : Matrix n q ℂ) :
    (KroneckerRearrangement.R (kroneckerMap (· * ·) A B)).rank ≤ 1 := by
  rw [KroneckerRearrangement.R_kronecker]
  exact rank_outerProduct_le_one _ _

end RankBounds

/-! ### Part B: Frobenius Norm and Singular Values -/

section FrobeniusSingularValues

attribute [local instance] Matrix.frobeniusSeminormedAddCommGroup

/-- The Frobenius norm squared equals the sum of squared singular values.
    This is a fundamental identity connecting norms and singular values. -/
theorem frobenius_norm_sq_eq_sum_singularValues_sq {n' : Type*} [Fintype n'] [DecidableEq n']
    (A : Matrix n' n' ℂ) :
    @Norm.norm _ Matrix.frobeniusSeminormedAddCommGroup.toNorm A ^ 2 =
    ∑ i, SVD.singularValues A i ^ 2 := by
  -- The proof connects:
  -- 1. Frobenius norm² = ∑ᵢⱼ |Aᵢⱼ|² (by frobenius_norm_def)
  -- 2. trace(AᴴA) = ∑ᵢ σᵢ² (by sum_sq_singularValues_eq_trace)
  -- 3. ∑ᵢⱼ |Aᵢⱼ|² = trace(AᴴA)
  rw [SVD.sum_sq_singularValues_eq_trace]
  -- Goal: ‖A‖² = Complex.re (trace (Aᴴ * A))
  -- Frobenius norm squared from definition
  have h_frob := @Matrix.frobenius_norm_def n' n' ℂ _ _ _ A
  -- ‖A‖ = (∑ᵢⱼ ‖Aᵢⱼ‖²)^(1/2), so ‖A‖² = ∑ᵢⱼ ‖Aᵢⱼ‖² = ∑ᵢⱼ Complex.normSq (Aᵢⱼ)
  have h_norm_sq : @Norm.norm _ Matrix.frobeniusSeminormedAddCommGroup.toNorm A ^ 2 =
      ∑ i, ∑ j, Complex.normSq (A i j) := by
    rw [h_frob]
    have h_nonneg : (0 : ℝ) ≤ ∑ i, ∑ j, ‖A i j‖ ^ (2 : ℝ) := by
      apply Finset.sum_nonneg; intro i _
      apply Finset.sum_nonneg; intro j _
      positivity
    rw [← Real.rpow_natCast, ← Real.rpow_mul h_nonneg]
    norm_num
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    rw [← Complex.normSq_eq_norm_sq]
  rw [h_norm_sq]
  -- Now show: ∑ᵢⱼ Complex.normSq (A i j) = Complex.re (trace (Aᴴ * A))
  simp only [trace, diag_apply, mul_apply, conjTranspose_apply]
  rw [Finset.sum_comm]
  simp only [Complex.re_sum]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  -- Goal: Complex.normSq (A j i) = (star (A j i) * A j i).re
  -- Use: normSq z = (conj z * z).re = (star z * z).re for complex z
  rw [Complex.normSq_apply]
  simp only [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

end FrobeniusSingularValues

end Matrix.Kronecker.SpectralBounds
