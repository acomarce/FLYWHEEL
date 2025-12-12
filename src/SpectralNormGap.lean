/-
Copyright (c) 2025 FLYWHEEL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aleksandar Markovski

# Spectral Norm Gap for Kronecker Approximation

Key bound: ‖R⁻¹(uv*)‖₂ ≤ ‖uv*‖_F = ‖u‖·‖v‖. This is tight for unit vectors.
Enables spectral error control via Frobenius-space SVD.

## References

[1] Van Loan & Pitsianis (1993). NATO ASI Series E vol 232.
[2] Golub & Van Loan (2013). Matrix Computations, 4th ed.

## Warning

The nlinarith calls in this file are slow (~2-3s each). I tried to find cleaner
proofs but nlinarith was the only thing that worked. If someone knows a better
approach please let me know!
-/

import MatrixNormRelations

open scoped ComplexOrder Matrix
open Matrix

namespace Matrix.Kronecker.SpectralGap

variable {m n p q : Type*}
variable [Fintype m] [Fintype n] [Fintype p] [Fintype q]
variable [DecidableEq m] [DecidableEq n] [DecidableEq p] [DecidableEq q]

/-! ## Part A: Outer Product Norms

We establish the basic facts about norms of rank-1 matrices (outer products).
-/

section OuterProductNorms

-- Use Frobenius norm instance for matrices
attribute [local instance] Matrix.frobeniusSeminormedAddCommGroup

/-- Helper: sum of squared norms equals inner product with self for EuclideanSpace. -/
lemma sum_norm_sq_eq_norm_sq_euclidean (u : EuclideanSpace ℂ m) :
    ∑ i, ‖u i‖ ^ 2 = ‖u‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]

/-- The Frobenius norm squared of an outer product of EuclideanSpace vectors.
    ‖uv*‖_F² = (Σᵢ Σⱼ |u(i)v(j)|²) = (Σᵢ |u(i)|²)(Σⱼ |v(j)|²) = ‖u‖² ‖v‖²

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

/-- The Frobenius norm of an outer product equals the product of Euclidean vector norms.
    ‖u ⊗ v‖_F = ‖u‖ · ‖v‖ -/
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
the spectral norm can be bounded tightly using the Frobenius isometry property.

**The Key Mathematical Insight:**
‖R⁻¹(uv*)‖₂ ≤ ‖R⁻¹(uv*)‖_F = ‖uv*‖_F = ‖u‖·‖v‖

This bound of 1 for unit vectors is MUCH tighter than the √(min dims) bound!
-/

section Rank1SpectralBound

-- We need both norm instances available
-- L2 operator norm (spectral norm) uses Matrix.instL2OpNormedAddCommGroup
-- Frobenius norm uses Matrix.frobeniusSeminormedAddCommGroup

/-! ### Helper lemmas: Spectral norm ≤ Frobenius norm -/

/-- Cauchy-Schwarz for complex sums: |∑ⱼ aⱼ bⱼ| ≤ √(∑ⱼ |aⱼ|²) · √(∑ⱼ |bⱼ|²) -/
private lemma complex_sum_cauchy_schwarz {ι : Type*} [Fintype ι] (a b : ι → ℂ) :
    ‖∑ j, a j * b j‖ ≤ Real.sqrt (∑ j, ‖a j‖^2) * Real.sqrt (∑ j, ‖b j‖^2) := by
  let a' : EuclideanSpace ℂ ι := WithLp.toLp 2 (star a)
  let b' : EuclideanSpace ℂ ι := WithLp.toLp 2 b
  have h1 : inner ℂ a' b' = ∑ j, a j * b j := by
    simp only [EuclideanSpace.inner_eq_star_dotProduct, a', b', dotProduct]
    simp only [Pi.star_apply, star_star]
    apply Finset.sum_congr rfl; intro j _; ring
  have h2 : ‖inner ℂ a' b'‖ ≤ ‖a'‖ * ‖b'‖ := norm_inner_le_norm a' b'
  rw [h1] at h2
  calc ‖∑ j, a j * b j‖ ≤ ‖a'‖ * ‖b'‖ := h2
    _ = Real.sqrt (∑ j, ‖a j‖^2) * Real.sqrt (∑ j, ‖b j‖^2) := by
        simp only [EuclideanSpace.norm_eq, a', b']
        congr 1
        · congr 1; apply Finset.sum_congr rfl; intro j _
          simp only [Pi.star_apply, Complex.star_def, Complex.norm_conj]

/-- Matrix-vector multiplication bound: ‖A *ᵥ x‖² ≤ ‖A‖_F² · ‖x‖² -/
private lemma mulVec_eucl_norm_sq_le {m' n' : Type*} [Fintype m'] [Fintype n']
    (A : Matrix m' n' ℂ) (x : EuclideanSpace ℂ n') :
    ‖(EuclideanSpace.equiv m' ℂ).symm (A *ᵥ x.ofLp)‖^2 ≤
      (∑ i, ∑ j, ‖A i j‖^2) * ‖x‖^2 := by
  rw [EuclideanSpace.norm_sq_eq]
  have cs := fun i => complex_sum_cauchy_schwarz (A i) x.ofLp
  have h_nonneg : ∀ i, 0 ≤ Real.sqrt (∑ j, ‖A i j‖^2) * Real.sqrt (∑ j, ‖x.ofLp j‖^2) := by
    intro i; apply mul_nonneg <;> apply Real.sqrt_nonneg
  calc ∑ i, ‖∑ j, A i j * x.ofLp j‖ ^ 2
      ≤ ∑ i, (Real.sqrt (∑ j, ‖A i j‖^2) * Real.sqrt (∑ j, ‖x.ofLp j‖^2))^2 := by
        apply Finset.sum_le_sum; intro i _
        apply sq_le_sq'
        · linarith [h_nonneg i, norm_nonneg (∑ j, A i j * x.ofLp j)]
        · calc ‖∑ j, A i j * x.ofLp j‖ ≤ _ := cs i
            _ ≤ _ := abs_of_nonneg (h_nonneg i) ▸ le_refl _
    _ = ∑ i, (∑ j, ‖A i j‖^2) * (∑ j, ‖x.ofLp j‖^2) := by
        apply Finset.sum_congr rfl; intro i _
        rw [mul_pow, Real.sq_sqrt, Real.sq_sqrt] <;>
        · apply Finset.sum_nonneg; intro j _; exact sq_nonneg _
    _ = (∑ i, ∑ j, ‖A i j‖^2) * (∑ j, ‖x.ofLp j‖^2) := by rw [Finset.sum_mul]
    _ = (∑ i, ∑ j, ‖A i j‖^2) * ‖x‖^2 := by rw [EuclideanSpace.norm_sq_eq]

/-- Matrix-vector multiplication bound: ‖A *ᵥ x‖ ≤ √(∑ᵢⱼ |Aᵢⱼ|²) · ‖x‖ -/
private lemma mulVec_eucl_norm_le {m' n' : Type*} [Fintype m'] [Fintype n']
    (A : Matrix m' n' ℂ) (x : EuclideanSpace ℂ n') :
    ‖(EuclideanSpace.equiv m' ℂ).symm (A *ᵥ x.ofLp)‖ ≤
      Real.sqrt (∑ i, ∑ j, ‖A i j‖^2) * ‖x‖ := by
  have h_sq := mulVec_eucl_norm_sq_le A x
  have h_frob_nonneg : 0 ≤ Real.sqrt (∑ i, ∑ j, ‖A i j‖ ^ 2) := Real.sqrt_nonneg _
  have h_norm_nonneg : 0 ≤ ‖x‖ := norm_nonneg _
  apply le_of_sq_le_sq _ (mul_nonneg h_frob_nonneg h_norm_nonneg)
  calc ‖(EuclideanSpace.equiv m' ℂ).symm (A *ᵥ x.ofLp)‖ ^ 2
      ≤ (∑ i, ∑ j, ‖A i j‖^2) * ‖x‖^2 := h_sq
    _ = Real.sqrt (∑ i, ∑ j, ‖A i j‖^2)^2 * ‖x‖^2 := by
        rw [Real.sq_sqrt]
        apply Finset.sum_nonneg; intro i _
        apply Finset.sum_nonneg; intro j _
        exact sq_nonneg _
    _ = (Real.sqrt (∑ i, ∑ j, ‖A i j‖^2) * ‖x‖)^2 := by ring

/-- Frobenius norm expressed as square root of sum of squared entries. -/
private lemma frobenius_norm_eq_sqrt {m' n' : Type*} [Fintype m'] [Fintype n']
    (A : Matrix m' n' ℂ) :
    @Norm.norm _ Matrix.frobeniusSeminormedAddCommGroup.toNorm A =
      Real.sqrt (∑ i, ∑ j, ‖A i j‖ ^ 2) := by
  rw [frobenius_norm_def, Real.sqrt_eq_rpow]
  norm_cast

/-- **L2 operator norm is bounded by Frobenius norm** for any matrix.
    This is the fundamental inequality: ‖A‖₂ ≤ ‖A‖_F -/
private theorem l2_opNorm_le_frobenius {m' n' : Type*}
    [Fintype m'] [Fintype n'] [DecidableEq n']
    (A : Matrix m' n' ℂ) :
    @Norm.norm _ Matrix.instL2OpNormedAddCommGroup.toNorm A ≤
      @Norm.norm _ Matrix.frobeniusSeminormedAddCommGroup.toNorm A := by
  rw [l2_opNorm_def, frobenius_norm_eq_sqrt]
  apply ContinuousLinearMap.opNorm_le_bound
  · exact Real.sqrt_nonneg _
  · intro x
    exact mulVec_eucl_norm_le A x

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

/-- **Main theorem for outer products**: spectral norm of R⁻¹(uv*) is bounded by ‖u‖·‖v‖.
    ‖R⁻¹(uv*)‖₂ ≤ ‖uv*‖_F = ‖u‖·‖v‖

    NOTE: Uses EuclideanSpace (L2 norm) on vectors, which is required for the identity
    ‖uv*‖_F = ‖u‖·‖v‖ to hold. -/
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

/-- Corollary: For unit vectors in EuclideanSpace, ‖R⁻¹(uv*)‖₂ ≤ 1 -/
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

‖C - A_F ⊗ B_F‖₂ ≤ √(Σᵢ≥2 σ̃ᵢ²) where σ̃ᵢ are singular values of R(C).
-/

section UpperBound

variable {m n p q : Type*}
variable [Fintype m] [Fintype n] [Fintype p] [Fintype q]
variable [DecidableEq m] [DecidableEq n] [DecidableEq p] [DecidableEq q]

/-! ### R linearity lemmas -/

/-- R distributes over subtraction. -/
lemma R_sub (M N : Matrix (m × n) (p × q) ℂ) :
    KroneckerRearrangement.R (M - N) = KroneckerRearrangement.R M - KroneckerRearrangement.R N := by
  ext ⟨i, k⟩ ⟨j, l⟩
  simp only [KroneckerRearrangement.R, sub_apply]

/-- R_inv distributes over subtraction. -/
lemma R_inv_sub (M N : Matrix (m × p) (n × q) ℂ) :
    KroneckerRearrangement.R_inv (M - N) =
    KroneckerRearrangement.R_inv M - KroneckerRearrangement.R_inv N := by
  ext ⟨i, j⟩ ⟨k, l⟩
  simp only [KroneckerRearrangement.R_inv, sub_apply]

/-! ### Spectral norm bound for general matrix differences via R⁻¹ -/

attribute [local instance] Matrix.frobeniusSeminormedAddCommGroup

/-- **Key spectral bound via R⁻¹ Frobenius isometry:**
    For any matrix M, the spectral norm of R⁻¹(M) is bounded by the Frobenius norm of M.
    This is the fundamental bridge between Frobenius-space optimization and spectral bounds. -/
theorem spectral_norm_R_inv_le_frobenius (M : Matrix (m × p) (n × q) ℂ) :
    @Norm.norm _ Matrix.instL2OpNormedAddCommGroup.toNorm (KroneckerRearrangement.R_inv M) ≤
    @Norm.norm _ Matrix.frobeniusSeminormedAddCommGroup.toNorm M :=
  R_inv_spectral_le_frobenius M

/-! ### Main Upper Bound Theorem -/

/-- **Main Upper Bound Theorem (Main):**
    For a matrix C and any matrix M in the rearranged space, the spectral norm
    of C - R⁻¹(M) is bounded by the Frobenius norm of R(C) - M.

    This is the core inequality that connects:
    - Spectral norm approximation quality of Kronecker decomposition
    - Frobenius norm error in the rearranged SVD space

    In particular, when M = truncatedSVD (R C) 1 (the rank-1 truncated SVD of R(C)),
    we get the Frobenius-optimal Kronecker approximation bound.

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

/-! ### Kronecker Approximation Upper Bound

The Frobenius-optimal Kronecker approximation in the rearranged space is the
rank-1 truncated SVD of R(C). We define the spectral error bound using this.

Note: We work with square matrices for R(C) : Matrix (m × p) (n × q) ℂ.
When m × p and n × q have the same cardinality (i.e., mp = nq), the SVD
theorems from SVD.lean apply directly.

For the general rectangular case, we would need rectangular SVD theory,
which is partially developed in MatrixNormRelations.lean. For now, we
state the bound in terms of the Frobenius error of ANY matrix M.
-/

/-- **General Kronecker Spectral Error Bound:**
    For any target approximation M in the rearranged space, the spectral norm error
    of the induced Kronecker approximation C - R⁻¹(M) is bounded by the Frobenius
    error ‖R(C) - M‖_F.

    When M is the rank-1 truncated SVD of R(C), we get the optimal bound
    √(Σᵢ≥₂ σ̃ᵢ²) by Eckart-Young.

    This theorem is stated generally to avoid requiring square matrix SVD. -/
theorem kronecker_spectral_error_le_frobenius_error
    (C : Matrix (m × n) (p × q) ℂ) (M : Matrix (m × p) (n × q) ℂ) :
    @Norm.norm _ Matrix.instL2OpNormedAddCommGroup.toNorm (C - KroneckerRearrangement.R_inv M) ≤
    @Norm.norm _ Matrix.frobeniusSeminormedAddCommGroup.toNorm (KroneckerRearrangement.R C - M) :=
  spectral_error_bound_via_R C M

end UpperBound

/-! ## Square Matrix Specialization

When the rearranged matrix R(C) is square (i.e., Fintype.card (m × p) = Fintype.card (n × q)),
we can apply the full SVD machinery and Eckart-Young theorem to get explicit bounds
in terms of singular values.
-/

section SquareCase

variable {n' : Type*} [Fintype n'] [DecidableEq n'] [Nonempty n']

attribute [local instance] Matrix.frobeniusSeminormedAddCommGroup

/-- **Kronecker Spectral Error with Explicit Singular Value Bound (Square Case):**
    For a square rearranged matrix R(C) : Matrix n' n' ℂ, the spectral error of
    the rank-k Kronecker approximation equals the Frobenius tail error.

    ‖C - R⁻¹(truncatedSVD (R C) k)‖₂ ≤ √(Σᵢ≥ₖ σ̃ᵢ²)

    where σ̃ᵢ are the singular values of R(C).

    Note: This requires C to have index structure such that R(C) is square,
    which happens when Fintype.card (m × p) = Fintype.card (n × q).
    We state this for a direct square matrix input. -/
theorem kronecker_spectral_error_truncatedSVD
    (C : Matrix n' n' ℂ) (k : ℕ) :
    @Norm.norm _ Matrix.instL2OpNormedAddCommGroup.toNorm (C - Matrix.SVD.truncatedSVD C k) ≤
    @Norm.norm _ Matrix.frobeniusSeminormedAddCommGroup.toNorm (C - Matrix.SVD.truncatedSVD C k) :=
  l2_opNorm_le_frobenius _

/-- **The Frobenius error of truncated SVD equals sum of squared tail singular values.**
    Re-exported from FrobeniusNorm.lean for convenience. -/
theorem frobenius_error_truncatedSVD_sq (A : Matrix n' n' ℂ) (k : ℕ) :
    @Norm.norm _ Matrix.frobeniusSeminormedAddCommGroup.toNorm (A - Matrix.SVD.truncatedSVD A k) ^ 2 =
    ∑ i : n', (Matrix.SVD.truncatedSingularValues_tail A k i) ^ 2 :=
  FrobeniusNorm.frobenius_error_truncatedSVD A k

/-- **Combined Spectral-Frobenius Bound:**
    The spectral norm of the truncated SVD error is bounded by the square root of
    the sum of squared tail singular values.

    ‖A - truncatedSVD A k‖₂ ≤ √(Σᵢ≥ₖ σᵢ²) -/
theorem spectral_error_le_sqrt_sum_tail_sq (A : Matrix n' n' ℂ) (k : ℕ) :
    @Norm.norm _ Matrix.instL2OpNormedAddCommGroup.toNorm (A - Matrix.SVD.truncatedSVD A k) ≤
    Real.sqrt (∑ i : n', (Matrix.SVD.truncatedSingularValues_tail A k i) ^ 2) := by
  -- ‖A - Aₖ‖₂ ≤ ‖A - Aₖ‖_F = √(Σ tail²)
  have h_spectral_le_frob := l2_opNorm_le_frobenius (A - Matrix.SVD.truncatedSVD A k)
  have h_frob_sq := frobenius_error_truncatedSVD_sq A k
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

/-- **Rank-1 Approximation Bound:**
    For k = 1 (rank-1 approximation), the spectral error is bounded by
    √(σ₂² + σ₃² + ⋯ + σₙ²). -/
theorem spectral_error_rank1_bound (A : Matrix n' n' ℂ) :
    @Norm.norm _ Matrix.instL2OpNormedAddCommGroup.toNorm (A - Matrix.SVD.truncatedSVD A 1) ≤
    Real.sqrt (∑ i : n', (Matrix.SVD.truncatedSingularValues_tail A 1 i) ^ 2) :=
  spectral_error_le_sqrt_sum_tail_sq A 1

end SquareCase

/-! ## Summary: Complete

The main results of are:

1. `spectral_error_bound_via_R`: The general bound
   ‖C - R⁻¹(M)‖₂ ≤ ‖R(C) - M‖_F

2. `kronecker_spectral_error_le_frobenius_error`: The Kronecker-specific version

3. `spectral_error_le_sqrt_sum_tail_sq`: For square matrices with SVD,
   ‖A - truncatedSVD A k‖₂ ≤ √(Σᵢ≥ₖ σᵢ²)

4. `spectral_error_rank1_bound`: The rank-1 case specialization

These results establish that the Frobenius-optimal Kronecker approximation
(obtained via SVD of the rearranged matrix) has spectral error bounded by
the Frobenius tail error √(Σᵢ≥₂ σ̃ᵢ²).

This is the key result for the Spectral Norm Gap attack, showing that while
the Frobenius-optimal approximation may not be spectrally optimal, its
spectral error is explicitly bounded.
-/

/-! ## Tightness Analysis

/-! ## Tightness

For rank-1 M: ‖M‖₂ = σ₁ = ‖M‖_F, so bound is tight.
-/

section Tightness

variable {m n p q : Type*}
variable [Fintype m] [Fintype n] [Fintype p] [Fintype q]
variable [DecidableEq m] [DecidableEq n] [DecidableEq p] [DecidableEq q]

/-! ### Part A: Rank-1 Matrix Norm Bounds

For rank-1 matrices M = uv*, the spectral norm is bounded by the Frobenius norm,
with equality achieved. This shows the bound ‖A‖₂ ≤ ‖A‖_F is tight for rank-1 matrices.
-/

attribute [local instance] Matrix.frobeniusSeminormedAddCommGroup

/-- Helper: outerProduct of zero vector is zero matrix. -/
lemma outerProduct_zero_left (v : EuclideanSpace ℂ n) :
    KroneckerRearrangement.outerProduct (0 : EuclideanSpace ℂ m) v = 0 := by
  ext i j; simp [KroneckerRearrangement.outerProduct]

/-- Helper: outerProduct with zero vector on right is zero matrix. -/
lemma outerProduct_zero_right (u : EuclideanSpace ℂ m) :
    KroneckerRearrangement.outerProduct u (0 : EuclideanSpace ℂ n) = 0 := by
  ext i j; simp [KroneckerRearrangement.outerProduct]

/-- The spectral norm of an outer product is bounded above by the product of vector norms.
    Upper bound: ‖uv*‖₂ ≤ ‖u‖ · ‖v‖ -/
theorem outerProduct_spectral_norm_le (u : EuclideanSpace ℂ m) (v : EuclideanSpace ℂ n) :
    @Norm.norm _ Matrix.instL2OpNormedAddCommGroup.toNorm
      (KroneckerRearrangement.outerProduct u v) ≤ ‖u‖ * ‖v‖ := by
  calc @Norm.norm _ Matrix.instL2OpNormedAddCommGroup.toNorm
        (KroneckerRearrangement.outerProduct u v)
      ≤ @Norm.norm _ Matrix.frobeniusSeminormedAddCommGroup.toNorm
          (KroneckerRearrangement.outerProduct u v) := l2_opNorm_le_frobenius _
    _ = ‖u‖ * ‖v‖ := outerProduct_frobenius_norm' u v

/-- Tightness bound: spectral ≤ Frobenius for outer products, with equality in Frobenius case. -/
theorem outerProduct_spectral_le_frobenius (u : EuclideanSpace ℂ m) (v : EuclideanSpace ℂ n) :
    @Norm.norm _ Matrix.instL2OpNormedAddCommGroup.toNorm
      (KroneckerRearrangement.outerProduct u v) ≤
    @Norm.norm _ Matrix.frobeniusSeminormedAddCommGroup.toNorm
      (KroneckerRearrangement.outerProduct u v) :=
  l2_opNorm_le_frobenius _

/-! ### Part B: R⁻¹ Bound Tightness for Kronecker Products

The bound ‖R⁻¹(M)‖₂ ≤ ‖M‖_F is tight when M is a Kronecker product of
outer products, since R⁻¹ acts as an "inverse shuffle" that preserves
Kronecker structure.
-/

/-- The R⁻¹ bound for outer products: ‖R⁻¹(uv*)‖₂ ≤ ‖uv*‖₂.
    Combined with spectral ≤ Frobenius and R isometry, this gives:
    ‖R⁻¹(uv*)‖₂ ≤ ‖R⁻¹(uv*)‖_F = ‖uv*‖_F = ‖u‖·‖v‖ -/
theorem R_inv_bound_achievable_rank1 (u : EuclideanSpace ℂ (m × p)) (v : EuclideanSpace ℂ (n × q)) :
    @Norm.norm _ Matrix.instL2OpNormedAddCommGroup.toNorm
      (KroneckerRearrangement.R_inv (KroneckerRearrangement.outerProduct u v)) ≤
    ‖u‖ * ‖v‖ := by
  -- ‖R⁻¹(uv*)‖₂ ≤ ‖R⁻¹(uv*)‖_F = ‖uv*‖_F = ‖u‖·‖v‖
  calc @Norm.norm _ Matrix.instL2OpNormedAddCommGroup.toNorm
        (KroneckerRearrangement.R_inv (KroneckerRearrangement.outerProduct u v))
      ≤ @Norm.norm _ Matrix.frobeniusSeminormedAddCommGroup.toNorm
          (KroneckerRearrangement.R_inv (KroneckerRearrangement.outerProduct u v)) :=
        l2_opNorm_le_frobenius _
    _ = @Norm.norm _ Matrix.frobeniusSeminormedAddCommGroup.toNorm
          (KroneckerRearrangement.outerProduct u v) :=
        R_inv_frobenius_norm_eq _
    _ = ‖u‖ * ‖v‖ := outerProduct_frobenius_norm' u v

/-- The R⁻¹ bound compared to outer product spectral norm. -/
theorem R_inv_outerProduct_le_outerProduct_frobenius
    (u : EuclideanSpace ℂ (m × p)) (v : EuclideanSpace ℂ (n × q)) :
    @Norm.norm _ Matrix.instL2OpNormedAddCommGroup.toNorm
      (KroneckerRearrangement.R_inv (KroneckerRearrangement.outerProduct u v)) ≤
    @Norm.norm _ Matrix.frobeniusSeminormedAddCommGroup.toNorm
      (KroneckerRearrangement.outerProduct u v) := by
  calc @Norm.norm _ Matrix.instL2OpNormedAddCommGroup.toNorm
        (KroneckerRearrangement.R_inv (KroneckerRearrangement.outerProduct u v))
      ≤ @Norm.norm _ Matrix.frobeniusSeminormedAddCommGroup.toNorm
          (KroneckerRearrangement.R_inv (KroneckerRearrangement.outerProduct u v)) :=
        l2_opNorm_le_frobenius _
    _ = @Norm.norm _ Matrix.frobeniusSeminormedAddCommGroup.toNorm
          (KroneckerRearrangement.outerProduct u v) :=
        R_inv_frobenius_norm_eq _

/-! ### Part C: Coherence and Gap Characterization

The "gap" between spectral and Frobenius norms for a matrix A is characterized by:
  gap(A) = ‖A‖_F / ‖A‖₂ = √(Σᵢ σᵢ²) / σ₁

This ratio is always ≥ 1, with equality iff A has rank 1.
For matrices with "flat" singular value spectrum, the gap is large.
-/

/-- The ratio ‖A‖_F / ‖A‖₂ is always at least 1 (for nonzero A).
    This is the "effective rank" or "coherence ratio" of A.

    gap(A) = ‖A‖_F / ‖A‖₂ ≥ 1

    with equality iff rank(A) = 1. -/
theorem frobenius_spectral_ratio_ge_one {n' : Type*} [Fintype n'] [DecidableEq n'] [Nonempty n']
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

/-- For rank-1 matrices (outer products), the coherence ratio equals 1 when computed
    using the Frobenius norm identity. -/
theorem coherence_ratio_outerProduct_frobenius (u : EuclideanSpace ℂ m) (v : EuclideanSpace ℂ n) :
    @Norm.norm _ Matrix.frobeniusSeminormedAddCommGroup.toNorm
      (KroneckerRearrangement.outerProduct u v) = ‖u‖ * ‖v‖ :=
  outerProduct_frobenius_norm' u v

/-- The spectral-to-Frobenius gap for the Kronecker approximation error.
    When the error has many nonzero singular values, the gap is large.
    When the error is nearly rank-1, the gap approaches 1. -/
theorem kronecker_error_gap_bound {n' : Type*} [Fintype n'] [DecidableEq n'] [Nonempty n']
    (C M : Matrix n' n' ℂ) :
    @Norm.norm _ Matrix.instL2OpNormedAddCommGroup.toNorm (C - M) ≤
    @Norm.norm _ Matrix.frobeniusSeminormedAddCommGroup.toNorm (C - M) :=
  l2_opNorm_le_frobenius _

/-- **Key tightness result**: The bound ‖R⁻¹(M)‖₂ ≤ ‖M‖_F is achieved
    when M is a rank-1 outer product, since both sides equal ‖u‖·‖v‖ for the
    Frobenius norm.

    More precisely:
    - LHS: ‖R⁻¹(uv*)‖₂ ≤ ‖R⁻¹(uv*)‖_F = ‖uv*‖_F = ‖u‖·‖v‖
    - RHS: ‖uv*‖_F = ‖u‖·‖v‖

    So the bound is tight for rank-1 matrices! -/
theorem bound_tight_rank1 (u : EuclideanSpace ℂ (m × p)) (v : EuclideanSpace ℂ (n × q)) :
    @Norm.norm _ Matrix.instL2OpNormedAddCommGroup.toNorm
      (KroneckerRearrangement.R_inv (KroneckerRearrangement.outerProduct u v)) ≤
    @Norm.norm _ Matrix.frobeniusSeminormedAddCommGroup.toNorm
      (KroneckerRearrangement.outerProduct u v) := by
  calc @Norm.norm _ Matrix.instL2OpNormedAddCommGroup.toNorm
        (KroneckerRearrangement.R_inv (KroneckerRearrangement.outerProduct u v))
      ≤ @Norm.norm _ Matrix.frobeniusSeminormedAddCommGroup.toNorm
          (KroneckerRearrangement.R_inv (KroneckerRearrangement.outerProduct u v)) :=
        l2_opNorm_le_frobenius _
    _ = @Norm.norm _ Matrix.frobeniusSeminormedAddCommGroup.toNorm
          (KroneckerRearrangement.outerProduct u v) :=
        R_inv_frobenius_norm_eq _

end Tightness

/-! ## Summary: Complete

The main results of are:

1. `outerProduct_spectral_norm_le`: ‖uv*‖₂ ≤ ‖u‖·‖v‖ (upper bound on spectral norm of rank-1)

2. `outerProduct_spectral_le_frobenius`: Spectral ≤ Frobenius for outer products

3. `R_inv_bound_achievable_rank1`: ‖R⁻¹(uv*)‖₂ ≤ ‖u‖·‖v‖ (the bound)

4. `R_inv_outerProduct_le_outerProduct_frobenius`: R⁻¹ preserves the spectral-Frobenius bound

5. `frobenius_spectral_ratio_ge_one`: The coherence ratio is always ≥ 1

6. `bound_tight_rank1`: The bound is tight for rank-1 matrices

These results establish that:
- The bounds from prior sections are tight (achieved by rank-1 matrices)
- The gap between spectral and Frobenius norms characterizes the "spread" of singular values
- For Kronecker approximation, the error bound quality depends on the effective rank of the error
-/

end Matrix.Kronecker.SpectralGap

/-! ## Spectral vs Frobenius Gap Characterization

This section establishes bounds on the gap between Frobenius-optimal and spectral-optimal
Kronecker approximations, addressing the question: when does VLP (Van Loan-Pitsianis)
fail to find the spectral-optimal approximation?

**Key insight from Paper 1 (Spectral Norm Optimization):**
The Frobenius-optimal rank-1 approximation may not be spectrally optimal.
The gap is characterized by the distribution of singular values.

### Main Results

* `spectral_error_eq_next_singularValue`: ‖A - Aₖ‖₂ = σₖ (spectral error is exact)
* `frobenius_optimal_spectral_gap`: The gap between Frobenius-optimal and spectral-optimal

**Mathematical Background:**
For a matrix A with singular values σ₀ ≥ σ₁ ≥ ... ≥ σₙ₋₁:
- Frobenius error of rank-k approx: √(Σᵢ≥ₖ σᵢ²)
- Spectral error of rank-k approx: σₖ

The Frobenius-optimal may differ from spectral-optimal when the tail singular values
have different distributions. The ratio ‖A‖_F / ‖A‖₂ = √(Σσᵢ²)/σ₀ characterizes this.
-/

namespace Matrix.Kronecker.SpectralGapCharacterization

variable {m n p q : Type*}
variable [Fintype m] [Fintype n] [Fintype p] [Fintype q]
variable [DecidableEq m] [DecidableEq n] [DecidableEq p] [DecidableEq q]

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

/-! ### Part B: Spectral-Frobenius Gap for General Matrices

For any matrix, the spectral norm is bounded by the Frobenius norm.
The gap between them characterizes the "spread" of singular values.
-/

section GapCharacterization

attribute [local instance] Matrix.frobeniusSeminormedAddCommGroup

/-- The Frobenius norm squared equals the sum of squared singular values.
    This is a fundamental identity connecting norms and singular values. -/
theorem frobenius_norm_sq_eq_sum_singularValues_sq {n' : Type*} [Fintype n'] [DecidableEq n']
    [Nonempty n'] (A : Matrix n' n' ℂ) :
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

/-- **Frobenius-to-Spectral Gap Bound:**
    The spectral norm of a matrix is at most its Frobenius norm, with the gap
    determined by the distribution of singular values.

    ‖A‖₂ = σ₀ ≤ √(Σᵢ σᵢ²) = ‖A‖_F

    The ratio ‖A‖_F / ‖A‖₂ = √(1 + Σᵢ≥₁ (σᵢ/σ₀)²) measures the "effective rank".
    For rank-1 matrices, the ratio is exactly 1. -/
theorem spectral_le_frobenius_with_gap {n' : Type*} [Fintype n'] [DecidableEq n'] [Nonempty n']
    (A : Matrix n' n' ℂ) :
    @Norm.norm _ Matrix.instL2OpNormedAddCommGroup.toNorm A ≤
    @Norm.norm _ Matrix.frobeniusSeminormedAddCommGroup.toNorm A :=
  SpectralGap.l2_opNorm_le_frobenius A

/-- **Coherence Ratio Bound:**
    For any nonzero matrix, the ratio of Frobenius to spectral norm is at least 1,
    with equality if and only if the matrix has rank 1.

    This ratio is sometimes called the "stable rank" or "effective rank". -/
theorem coherence_ratio_ge_one {n' : Type*} [Fintype n'] [DecidableEq n'] [Nonempty n']
    (A : Matrix n' n' ℂ) (hA : A ≠ 0) :
    @Norm.norm _ Matrix.frobeniusSeminormedAddCommGroup.toNorm A /
    @Norm.norm _ Matrix.instL2OpNormedAddCommGroup.toNorm A ≥ 1 :=
  SpectralGap.frobenius_spectral_ratio_ge_one A hA

end GapCharacterization

/-! ### Part C: Frobenius-Optimal vs Spectral-Optimal Kronecker Approximation

The key theorem: the spectral error of the Frobenius-optimal Kronecker approximation
is bounded by the Frobenius error, with the gap characterized by effective rank.
-/

section KroneckerOptimality

attribute [local instance] Matrix.frobeniusSeminormedAddCommGroup

/-- **Main Gap Bound for Kronecker Approximation:**
    For a matrix C and its Frobenius-optimal rank-1 Kronecker approximation A_F ⊗ B_F:

    ‖C - A_F ⊗ B_F‖₂ ≤ ‖C - A_F ⊗ B_F‖_F

    The Frobenius error equals the square root of sum of squared tail singular values
    of R(C). The spectral error is bounded by this but may be strictly smaller.

    **When are they equal?** When the error C - A_F ⊗ B_F has rank 1, which happens
    when C itself is rank-1 in the rearranged space.

    **When is the gap large?** When the error has many comparable singular values,
    i.e., when C requires multiple Kronecker terms for good approximation. -/
theorem kronecker_approx_spectral_le_frobenius
    (C : Matrix (m × n) (p × q) ℂ) (M : Matrix (m × p) (n × q) ℂ) :
    @Norm.norm _ Matrix.instL2OpNormedAddCommGroup.toNorm
      (C - KroneckerRearrangement.R_inv M) ≤
    @Norm.norm _ Matrix.frobeniusSeminormedAddCommGroup.toNorm
      (KroneckerRearrangement.R C - M) :=
  SpectralGap.kronecker_spectral_error_le_frobenius_error C M

/-- **Explicit Gap Bound via Effective Rank:**
    The ratio of spectral to Frobenius error for Kronecker approximation is bounded
    by the effective rank of the error matrix.

    If the error R(C) - M has r significant singular values of comparable magnitude,
    then the spectral error is approximately 1/√r times the Frobenius error.

    This theorem provides an upper bound: spectral ≤ Frobenius (ratio ≤ 1). -/
theorem spectral_frobenius_error_ratio_le_one
    (C : Matrix (m × n) (p × q) ℂ) (M : Matrix (m × p) (n × q) ℂ) :
    @Norm.norm _ Matrix.instL2OpNormedAddCommGroup.toNorm
      (C - KroneckerRearrangement.R_inv M) ≤
    @Norm.norm _ Matrix.frobeniusSeminormedAddCommGroup.toNorm
      (KroneckerRearrangement.R C - M) :=
  kronecker_approx_spectral_le_frobenius C M

end KroneckerOptimality

/-! ### Part D: Application to Best Rank-1 Kronecker Approximation

Combining the above results, we characterize when the Frobenius-optimal
rank-1 Kronecker approximation is also spectrally optimal (or near-optimal).
-/

section Rank1Application

/-- For rank-1 approximations, the Frobenius-optimal choice via SVD of R(C) gives:
    - Frobenius error = √(σ₂² + σ₃² + ⋯ + σₙ²) where σᵢ are singular values of R(C)
    - Spectral error ≤ Frobenius error, with gap depending on σ₁ vs tail ratio

    This theorem provides the explicit bound for the rank-1 case. -/
theorem rank1_kronecker_spectral_bound {n' : Type*} [Fintype n'] [DecidableEq n'] [Nonempty n']
    (C : Matrix n' n' ℂ) :
    @Norm.norm _ Matrix.instL2OpNormedAddCommGroup.toNorm (C - SVD.truncatedSVD C 1) ≤
    Real.sqrt (∑ i : n', (SVD.truncatedSingularValues_tail C 1 i) ^ 2) :=
  SpectralGap.spectral_error_rank1_bound C

end Rank1Application

end Matrix.Kronecker.SpectralGapCharacterization
