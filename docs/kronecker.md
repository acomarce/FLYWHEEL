# Kronecker rearrangement `R` / `R_inv`

The Van Loan–Pitsianis setup. `C ≈ A ⊗ B` is best in Frobenius norm when `vec A (vec B)ᵀ` is the
best rank-1 approximation of `R C`.

## Definitions (`src/KroneckerRearrangement.lean`, `Matrix.KroneckerRearrangement`)

- `vec (M : Matrix m n α) : m × n → α` maps `⟨i, j⟩ ↦ M i j`. The docstring calls this both
  "column-major" and "row-major"; the definition above is the truth.
- `outerProduct u v i j = u i * v j`, with no conjugation.
- `R (M : Matrix (m × n) (p × q) α) : Matrix (m × p) (n × q) α`, where `R M ⟨i, k⟩ ⟨j, l⟩ = M ⟨i,
  j⟩ ⟨k, l⟩`. It needs only `[Semiring α]`.
- `R_inv`, its inverse, is defined in the `Isometry` section under `[RCLike α]`.
  - Lemmas: `R_inv_R` and `R_R_inv` (not `@[simp]`), and `R_bijective`.
- `R_kronecker`: `R (kroneckerMap (· * ·) A B) = outerProduct (vec A) (vec B)` for `A : Matrix m
  p α`, `B : Matrix n q α`. So `R` of a Kronecker product has rank ≤ 1.
- **Frobenius isometry:** `R_frobenius_norm_eq : ‖R M‖ = ‖M‖`, under Mathlib's
  `frobeniusSeminormedAddCommGroup` as a local instance. Related:
  - `R_inv_frobenius_norm_eq` (in SpectralNormGap);
  - `R_linearIsometryEquiv`, which only states that such an equivalence *exists*; there is no
    named `≃ₗᵢ` def.
- `@[simp]` lemmas: `R_apply`, `vec_apply`, `outerProduct_apply` (all `rfl`).

## R does not preserve the spectral norm

`R` is a Frobenius isometry only. Spectral facts transfer through `R` as **upper bounds** via
`‖·‖₂ ≤ ‖·‖_F`, never as equalities. Two counterexamples:

- **Anti-diagonal permutation (TightBounds, Part 4 note).** For `m = n = p = q = Fin 2`, the 4×4
  anti-diagonal permutation is `J₂ ⊗ J₂`. So `‖M‖₂ = 1`, while `R M = vec J₂ (vec J₂)ᵀ` has
  `‖R M‖₂ = ‖vec J₂‖² = 2`.
- **Removed coherence claim (TightBounds, Part 5).** A previous draft claimed that `μ(E') ≥ 0.9`
  for the rearranged error `E' = R C − truncatedSVD_rect (R C) 1` forces `‖E‖₂ ≥ 0.9 ‖E‖_F` for
  `E = R_inv E'`. That claim is false:
  - High coherence bounds the spectral norm from *above* relative to Frobenius:
    `‖E'‖_F / ‖E'‖₂ = √rank · μ(E')` (`frobenius_spectral_ratio_eq_sqrt_rank_mul_coherence_rect`).
  - `R` preserves the Frobenius norm but not the spectral norm.
  - **Counterexample** with `m = n = p = q = Fin 2`:
    - Take `R C = vec I₂ (vec I₂)ᵀ + 3 e eᵀ`, with `e` the basis vector at index `(0, 1)`.
      Since `e ⟂ vec I₂`, the singular values are `3 > 2`.
    - The rank-1 truncation is `3 e eᵀ`, so `E' = vec I₂ (vec I₂)ᵀ`, which has rank 1 and
      `μ(E') = 1`.
    - But `E = R_inv E' = I₂ ⊗ I₂ = I₄`, so `‖E‖₂ = 1 < 0.9 · 2 = 0.9 ‖E‖_F`.
  - The Part 5 comment in TightBounds records this.

## Bounds that are proved

**MatrixNormRelations, `Matrix.KroneckerRearrangement`:**
- `kronecker_approx_frobenius_error : ‖C - A ⊗ B‖ = ‖R C - outerProduct (vec A) (vec B)‖`
  (Frobenius).
- `kronecker_approx_spectral_bound` (spectral ≤ Frobenius).
- `l2_opNorm_kronecker : ‖A ⊗ B‖ = ‖A‖ * ‖B‖` (L2).

**MatrixNormRelations, `Matrix.KroneckerPerturbation`:**
- `kronecker_sub_spectral_norm_bound : ‖B⊗C − B'⊗C'‖ ≤ ‖B−B'‖‖C‖ + ‖B'‖‖C−C'‖`.
- `kronecker_singularValue_perturbation` restates it; no singular values appear.
- `kronecker_relative_perturbation` is not actually in relative form.

**SpectralNormGap, `Matrix.Kronecker.SpectralGap`.** Note the namespace is `Kronecker`, not
`KroneckerRearrangement`.
- `R_inv_spectral_le_frobenius : ‖R_inv M‖₂ ≤ ‖M‖_F`.
- `spectral_error_bound_via_R : ‖C − R_inv M‖₂ ≤ ‖R C − M‖_F`. The main usable bound; restated as
  `kronecker_spectral_error_le_frobenius_error`.
- `R_inv_outerProduct_spectral_bound : ‖R_inv (outerProduct u v)‖₂ ≤ ‖u‖‖v‖`.

**TightBounds, `Matrix.TightBounds`:**
- `frobenius_error_via_R_isometry : ‖C − R_inv X‖ = ‖R C − X‖` (Frobenius).
- `spectral_error_le_frobenius_error` for `X = truncatedSVD_rect (R C) 1`. The Frobenius error
  equals `√(σ₂² + σ₃² + …)` of `R C`, not `σ₂`, despite the TightBounds header.

**CoherenceCharacterization, `Matrix.Coherence`:**
- `kroneckerCoherence C := coherenceFactorRect (R C)`.
- `kronecker_approximation_coherence_characterization` combines `spectral_error_bound_via_R` with
  the coherence identity `‖E‖₂ = ‖E‖_F / (√rank · μ)`.

## Claims in comments that are not proved

- **SpectralNormGap header, "tight for unit vectors", and the `Tightness` section.**
  `bound_tight_rank1` proves only `≤` and duplicates
  `R_inv_outerProduct_le_outerProduct_frobenius`. Equality fails in general:
  `R_inv (vec A (vec B)ᵀ) = A ⊗ B` has spectral norm `‖A‖₂‖B‖₂`, which is `< ‖vec A‖‖vec B‖`
  unless `A` and `B` have rank ≤ 1. For example, `A = B = I₂` gives `1 < 2`.
- **Docstrings that promise more than the statement:**
  - `R_inv_bound_achievable_rank1` says `≤ ‖uv*‖₂`, but the statement is `≤ ‖u‖‖v‖`.
  - `frobenius_spectral_ratio_ge_one` mentions "equality iff rank 1", but only `≥ 1` is proved.
- **A "√(min dims) bound" mentioned in SpectralNormGap.** No such bound exists anywhere in the
  repo. The only `R_inv` spectral bound is `‖R_inv X‖₂ ≤ ‖X‖_F`.
