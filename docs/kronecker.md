# Kronecker rearrangement `R` / `R_inv`

The Van Loan–Pitsianis setup. `C ≈ A ⊗ B` is best in Frobenius norm when `vec A (vec B)ᵀ` is the
best rank-1 approximation of `R C`.

## Definitions (`src/KroneckerRearrangement.lean`, `Matrix.KroneckerRearrangement`)

- `vec (M : Matrix m n α) : m × n → α` maps `⟨i, j⟩ ↦ M i j`. Entries stay indexed by the pair,
  so no row- or column-major order is chosen.
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

## The Van Loan–Pitsianis theorem (`src/TightBounds.lean`, `Matrix.TightBounds`)

- `kroneckerApprox C := R_inv (truncatedSVD_rect (R C) 1)`.
- `kroneckerApprox_isKronecker`: `kroneckerApprox C = A ⊗ B` for some `A : Matrix m p ℂ`,
  `B : Matrix n q ℂ`. The proof uses `exists_outerProduct_of_rank_le_one` (a rank ≤ 1 matrix
  is `u vᵀ`) and `R_kronecker`.
- `kroneckerApprox_optimal`: `‖C - kroneckerApprox C‖_F ≤ ‖C - A ⊗ B‖_F` for all `A`, `B`.
  This is rectangular Eckart–Young (`eckart_young_frobenius_rect`) for `R C` with `k = 1`,
  transported by the isometry `R` and `R (A ⊗ B) = vec A (vec B)ᵀ`.
- `kroneckerApprox_error_sq`: `‖C - kroneckerApprox C‖_F² = Σᵢ (truncatedSingularValues_rect_tail
  (R C) 1 i)²`, i.e. the sum of `σᵢ(R C)²` over `i ≥ 1` (0-indexed).
- `Matrix.FrobeniusUniqueness.kroneckerApprox_unique`: if `σ₁(R C) < σ₀(R C)` and
  `‖C - A ⊗ B‖_F ≤ ‖C - kroneckerApprox C‖_F`, then `A ⊗ B = kroneckerApprox C`. This is
  rectangular Frobenius uniqueness (`eckart_young_frobenius_rect_unique`) for `R C` with `k = 1`,
  transported by `R`; see `docs/eckart-young.md`. Only the product is unique: `(c A) ⊗ (c⁻¹ B)`
  is the same matrix for every `c ≠ 0`.
- Not formalized: non-uniqueness when `σ₀(R C) = σ₁(R C) > 0`, and anything about the
  spectral-norm-optimal Kronecker approximation in the original space.

## Bounds that are proved

**MatrixNormRelations, `Matrix.KroneckerRearrangement`:**
- `kronecker_approx_frobenius_error : ‖C - A ⊗ B‖ = ‖R C - outerProduct (vec A) (vec B)‖`
  (Frobenius).
- `l2_opNorm_kronecker : ‖A ⊗ B‖ = ‖A‖ * ‖B‖` (L2).

**MatrixNormRelations, `Matrix.KroneckerPerturbation`:**
- `kronecker_sub_spectral_norm_bound : ‖B⊗C − B'⊗C'‖ ≤ ‖B−B'‖‖C‖ + ‖B'‖‖C−C'‖`, and
  `kronecker_sub_spectral_norm_bound_cross` with `‖B‖` in place of `‖B'‖` plus a cross term.
- `kronecker_relative_perturbation`: for `B, C ≠ 0`,
  `‖B⊗C − B'⊗C'‖ / ‖B⊗C‖ ≤ εB + εC + εB εC` with `εB = ‖B−B'‖/‖B‖`, `εC = ‖C−C'‖/‖C‖`.
- `kronecker_singularValue_perturbation`: for square factors,
  `|σₖ(B⊗C) − σₖ(B'⊗C')| ≤ ‖B−B'‖‖C‖ + ‖B'‖‖C−C'‖` (Weyl plus the bound above).
- `kronecker_perturbation_single_factor_B/C`: equality when one factor is unchanged.

**SpectralNormGap, `Matrix.Kronecker.SpectralBounds`.** Note the namespace is `Kronecker`, not
`KroneckerRearrangement`.
- `R_inv_spectral_le_frobenius : ‖R_inv M‖₂ ≤ ‖M‖_F`.
- `spectral_error_bound_via_R : ‖C − R_inv M‖₂ ≤ ‖R C − M‖_F`. The main usable bound.
- `R_inv_outerProduct_spectral_bound : ‖R_inv (outerProduct u v)‖₂ ≤ ‖u‖‖v‖`.
- `R_inv_spectral_lt_frobenius_R_one`: the bound is strict for `M = R 1` when
  `#m · #n ≥ 2` (`‖1‖₂ = 1 < √(#m · #n) = ‖R 1‖_F`).
- `Matrix.Coherence.R_inv_spectral_eq_frobenius_R_outerProduct`: the bound is an equality for
  `M = R (u vᵀ)`, so its constant cannot be improved;
  `Matrix.Coherence.R_inv_spectral_eq_frobenius_iff_rank_le_one`: equality holds exactly when
  `rank (R⁻¹ M) ≤ 1`.

**TightBounds, `Matrix.TightBounds`:**
- `frobenius_error_via_R_isometry : ‖C − R_inv X‖ = ‖R C − X‖` (Frobenius).
- Spectral error of `kroneckerApprox C`: `spectral_error_bound_via_R` with
  `M = truncatedSVD_rect (R C) 1` bounds it by `‖R C − M‖_F`, which `kroneckerApprox_error_sq`
  evaluates as `√(σ₁² + σ₂² + …)` of `R C` (0-indexed).

**CoherenceCharacterization, `Matrix.Coherence`:**
- `kroneckerCoherence C := coherenceFactorRect (R C)`.
- `coherenceFactorRect_eq_coherenceFactor`: the rectangular and square coherence factors agree
  on square matrices.
- `spectral_norm_eq_frobenius_div_coherence_rect` (SVD.lean): `‖E‖₂ = ‖E‖_F / (√rank · μ)` for
  `E ≠ 0`. Applied to `E = R C − M` it describes the R-space error only; R does not preserve
  `‖·‖₂`, so it says nothing about when `spectral_error_bound_via_R` is tight.
- Convention: `μ ≈ 1` is *incoherent* (flat spectrum), `μ ≈ 1/√rank` is *coherent*.
  - `nearly_coherent_iff`, `nearly_coherent_bound`, `nearly_coherent_spectral_lower_bound`: for
    `E ≠ 0` and `ε < 1`, `μ(E) ≤ 1/((1 − ε)√rank E) ↔ (1 − ε)‖E‖_F ≤ ‖E‖₂`.
  - `incoherent_improved_bound`: `α ≤ μ(E)` gives `‖E‖₂ ≤ ‖E‖_F / (α √rank E)`.
- Equality cases (square `E ≠ 0`): `coherenceFactor_eq_one_iff` (μ(E) = 1 iff every nonzero
  σᵢ equals ‖E‖₂) and `norm_eq_frobeniusNorm'_iff_rank_le_one` (‖E‖₂ = ‖E‖_F iff rank E ≤ 1,
  for all E). `stableRank_le_effectiveRank`: (‖E‖_F/‖E‖₂)² ≤ effectiveRank E.
- Solution distance, for `A_F = truncatedSVD A 1` and any `M` with `‖A − M‖₂ ≤ ‖A − A_F‖₂`
  (every spectral minimizer; `norm_sub_spectralOptimalRank1_le` gives it for the chosen
  `A_* = spectralOptimalRank1 A`):
  - `spectral_error_truncatedSVD_one_eq_spectralOptimalRank1`: `‖A − A_F‖₂ = ‖A − A_*‖₂`;
  - `frobenius_spectral_solution_distance`: `‖A_F − M‖₂ ≤ 2‖A − A_F‖₂`;
  - `frobenius_spectral_distance_with_gap`: `‖A_F − M‖₂ ≤ 2(‖A‖₂ − spectralGap A)`;
  - `decision_criterion`: `spectralGap A ≥ (1 − δ/2)‖A‖₂` gives `‖A_F − M‖₂ ≤ δ‖A‖₂`.
  - Singular vectors: `Matrix.DavisKahan.top_right_singular_vector_perturbation_of_spectralGap`
    bounds how far the top right singular vector of a square A moves, by η / (γ − η) with
    η = ‖Ã − A‖₂ (‖Ã‖₂ + ‖A‖₂) and γ = spectralGap A · ‖A‖₂, through the Gram matrix
    (`docs/davis-kahan.md`). Wedin's theorem itself is not formalized.
