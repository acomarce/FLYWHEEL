# SVD construction (`src/SVD.lean`)

This note describes how the decomposition is built and where the traps are. For locations, grep
`docs/INDEX.md`. Indexing rules (`eigenvalues` vs `eigenvalues₀`, `eigenvaluesBijection`) are
in `CLAUDE.md`.

## Square complex case: `Matrix.SVD`

**Singular values.**
- `singularValues A : n → ℝ` is `√` of `IsHermitian.eigenvalues` of `Aᴴ * A`. It is indexed by
  `n` and not sorted.
- `singularValues₀ A : Fin (card n) → ℝ` is `√ eigenvalues₀`. It is sorted, with index 0 the
  largest (`singularValues₀_antitone`).
- `singularValues_eq_singularValues₀` relates the two through Mathlib's `equivOfCardEq`
  bijection, by `rfl`.

**Construction**, which goes through the Gram matrix rather than a polar decomposition:
1. `V := rightUnitary A`, the `eigenvectorUnitary` of `Aᴴ * A`.
2. `svd_action` gives `Vᴴ (Aᴴ A) V = diagonal eigenvalues` (from Mathlib's `spectral_theorem`).
   So the columns of `A * V` are orthogonal, and column `i` has squared norm `σᵢ²`.
3. For `σᵢ ≠ 0`, `leftSingularVectorNonzero A i = σᵢ⁻¹ • (A V)[:, i]`. These vectors are
   orthonormal. For `σᵢ = 0`, the column of `A V` is zero.
4. Move to `EuclideanSpace`: `leftSingularVectorEuclidean` and `leftSingularVectorExtended`
   (zero when `σᵢ = 0`). They are orthonormal on `nonzeroSingularIndices`.
5. `extendedONB` extends them to an orthonormal basis (`.choose` of
   `exists_orthonormalBasis_extension_of_card_eq`). `onbToMatrix` then gives `constructedU`,
   which is unitary, and its column `j` is `uⱼ` whenever `σⱼ ≠ 0`.
6. `AV_eq_constructedU_mul_sigma`: `A * V = U * diagonal σ`.
7. `svd_decomposition`: `∃ U V : unitaryGroup n ℂ, ∃ σ ≥ 0, A = U * diagonal σ * star V`.

**Defined but not used by the construction:**
- `leftUnitary` (eigenvectors of `A Aᴴ`).
- `singularDiagonal`.
- `sqrtConjTransposeMulSelf` (`CFC.sqrt (Aᴴ A)`).

The file header's "via polar decomposition (CFC.sqrt)" is out of date.

**Other facts:**
- `prod_singularValues_eq_abs_det`.
- `sum_sq_singularValues_eq_trace`.
- `singularValues_conjTranspose`.
- `singularValues_hermitian_multiset`. For Hermitian `A`, singular values equal `|eigenvalues|`
  only *as multisets*, not pointwise.

**Truncation** (section `TruncatedSVD`):
- `truncatedSingularValues A k` keeps `σ` at sorted positions `< k`.
- `truncatedSVD A k = constructedU A * diagonal … * star (rightUnitary A)`.
- `truncatedSVD_rank_le`.
- `truncatedSVD_tail`, with `truncatedSVD_add_tail : A = truncatedSVD A k + truncatedSVD_tail A
  k`.

## Real case: `Matrix.SVD.Real`

- This is a parallel copy of the construction over `ℝ` with `orthogonalGroup`, not a reduction to
  the complex case:
  - `rightOrthogonal` comes from `Aᵀ A`;
  - `realAV`, `extendedONB_real`, `constructedU_real`;
  - `realAV_eq_constructedU_real_mul_sigma`.
- Main result: `Matrix.SVD.Real.svd_decomposition`.
- `Real.singularValues` is defined through the complex `singularValues (A.map ofReal)`. Nothing
  links it to `realSingularValues`.
- Nothing outside SVD.lean uses this namespace.

## Rectangular case: `Matrix.SVD.Rectangular`

**Gram matrix.** It always uses `Aᴴ * A` (n×n), even when `m < n`:
`rightUnitary A = eigenvectorUnitary (Aᴴ A)`. The design-choice docstring on `singularValues`
explains why: it stays consistent with `rightUnitary`, and it avoids the `equivFin` vs
`equivOfCardEq` mismatch. The module header's "smaller Gram matrix" does not describe the code.

**Singular values.**
- `singularValues A : Fin (min #m #n) → ℝ` is `√ eigenvalues₀ (Fin.castLE _ k)` of `Aᴴ A`, so it
  is sorted.
- `singularValueFromEigenvalue` is the `n`-indexed form, linked to it by a lemma.

**Index plumbing:**
- `eigenvaluesBijection`.
- `embedMinToM`, `embedMinToN : Fin (min …) → m / n`.
- `finMinOfAbstract`, which goes the other way.
- `correspondingN`, which pairs `m`-indices with `n`-indices.

**`S`.** `singularDiagonal A : Matrix m n ℂ` holds `σ` at `(i, j)` when
`eigenvaluesBijection m i` and `eigenvaluesBijection n j` are equal and `< min`; it is 0
elsewhere.

**`U`.**
- `extendedONB_rectangular_v2` extends the `m`-indexed `leftSingularVectorByM`. This gives
  `constructedU_rectangular` and `constructedU_rectangular_column_spec`.
- The older `extendedONB_rectangular` reindexes through an arbitrary `equivOfCardEq`, which loses
  the column/diagonal alignment. It is kept "for compatibility" and is unused.

**Results:**
- `AV_eq_US_rectangular : A * rightUnitary A = constructedU_rectangular A * singularDiagonal A`.
  This is the usable form of the theorem.
- **`svd_decomposition_rectangular` is vacuous as stated.** It says `∃ U V S, A = U * S * star V`
  with no constraint on `S` (take `U = V = 1`, `S = A`). Cite `AV_eq_US_rectangular` together
  with `singularDiagonal` instead.
- Rank and trace facts: `rank_eq_card_nonzero_singularValues_rect`, `singularValues_sq_rect`,
  `sum_sq_singularValues_rect_eq_trace`.

## Root-level sections at the end of SVD.lean

These sit outside any namespace:

- **`FrobeniusNormRectangular`** (Frobenius local instance). Declares fully qualified
  `Matrix.SVD.Rectangular.frobeniusNorm_sq_eq_sum_singularValues_sq_rect`, …
- **`SpectralNormRectangular`** (L2 instances plus `instCStarRing`, local notation `‖A‖₂`, a
  private root-level `instCStarAlgebraMatrixLocal`).
  - Declares `Matrix.SVD.Rectangular.maxSingularValue`, `spectral_norm_eq_max_singularValue_rect`
    and `spectral_norm_le_frobenius_norm_rect`.
  - Most of these take `h : 0 < min #m #n`.
- **`RectangularCoherenceFactor`** (L2 instances, local `‖A‖₂`; Frobenius through the explicit
  `frobeniusNormRect`). It is genuinely root-namespace:
  - `coherenceFactorRect E = ‖E‖_F / (√rank E · ‖E‖₂)`, defined as 1 for `E = 0`;
  - `coherenceFactorRect_le_one` and `coherenceFactorRect_bounds`;
  - `frobenius_spectral_ratio_eq_sqrt_rank_mul_coherence_rect`.

  The section docstring cites `coherenceFactorRect_eq_square_case`, which does not exist. The
  nearest lemma is `coherenceFactorRect_eq_formula`, which only unfolds the definition.

## Rectangular truncation lives in TightBounds

`Matrix.TightBounds` defines:
- `singularValues₀_rect`, an alias of the rectangular `singularValues`;
- `truncatedSVD_rect A k = constructedU_rectangular A * Sₖ * star (rightUnitary A)`.

It proves `truncatedSVD_rect_rank_le` and `spectral_error_truncatedSVD_rect`. See
`docs/eckart-young.md`.
