# Eckart–Young

The truncated SVD is a best rank-k approximation in both Frobenius and spectral norm, for square
and for rectangular complex matrices. All four optimality theorems rest on Thompson interlacing.

| Result | Name | Norm |
|---|---|---|
| Frobenius EY (square) | `Matrix.FrobeniusNorm.eckart_young_frobenius` | Frobenius (local instance) |
| Spectral error `‖A - Aₖ‖ = σₖ` (square) | `Matrix.SVD.spectral_error_truncatedSVD` | L2 (local instances) |
| Spectral EY (square) | `Matrix.SVD.eckart_young_spectral` | L2 (local instances) |
| Frobenius error `‖A - Aₖ‖² = Σᵢ≥ₖ σᵢ²` (rectangular) | `Matrix.TightBounds.frobenius_error_truncatedSVD_rect` | Frobenius |
| Spectral error (rectangular) | `Matrix.TightBounds.spectral_error_truncatedSVD_rect` | L2 |
| Frobenius EY (rectangular) | `Matrix.TightBounds.eckart_young_frobenius_rect` | Frobenius |
| Spectral EY (rectangular) | `Matrix.TightBounds.eckart_young_spectral_rect` | L2 |
| Rank bound (rectangular) | `Matrix.TightBounds.truncatedSVD_rect_rank_le` | — |

The square spectral results live in `Matrix.SVD` (MatrixNormRelations.lean), next to the square
`Matrix.SVD.truncatedSVD`.

## Key lemma: Thompson interlacing (`src/WeylInequality.lean`)

**`thompson_interlacing_eigenvalues`**: for `A B : Matrix m n ℂ` with `B.rank ≤ r` and
`i + r < card n`, `λ_{i+r}(AᴴA) ≤ λᵢ((A+B)ᴴ(A+B))` (sorted eigenvalues). The row type `m` is
arbitrary because the proof only uses the `n × n` Gram matrices:
- Intersect three subspaces of `ℂⁿ`: the head eigenspan of `Aᴴ A` (dimension `i + r + 1`),
  `ker B` (dimension `≥ n - r`, `finrank_ker_toEuclideanLin_ge'`), and a tail eigenspan of
  `(A+B)ᴴ(A+B)` (dimension `n - i`).
- The dimension count is `CourantFischer.finrank_inf_ge_of_sum_gt`.
- A unit vector in the intersection, together with the Rayleigh-quotient bounds from
  CourantFischer and `‖Ax‖² = Re⟨AᴴAx, x⟩` (`CourantFischer.norm_sq_mul_eq_inner_AHA`),
  finishes the proof.

Singular-value forms:
- `thompson_interlacing` (square): `σ_{i+r}(A) ≤ σᵢ(A + B)` for `singularValues₀`.
- `thompson_interlacing_rect`: the same for `Matrix.SVD.Rectangular.singularValues`, with
  `i + r < min(#m, #n)`.
- `interlacing_low_rank_subtraction(_rect)`: `C.rank ≤ k`, `k ≤ j` gives
  `σⱼ(A) ≤ σ_{j-k}(A - C)`.
- `interlacing_for_eckart_young`: the square statement with ℕ indices.

## Frobenius version (square, `src/FrobeniusNorm.lean`)

`eckart_young_frobenius (A) (k) (B) (hB : B.rank ≤ k) : ‖A - truncatedSVD A k‖ ≤ ‖A - B‖`. No
`Nonempty` is needed, because the empty case is handled inside the proof. The steps:

1. Rotate into the SVD basis. Set `C = Uᴴ B V`, so `rank C ≤ k`. Then `‖A - B‖ = ‖Σ - C‖` by
   unitary invariance (`frobenius_error_in_svd_basis`, `frobenius_norm_unitary_mul` /
   `frobenius_norm_mul_unitary`; both now take rectangular matrices).
2. `‖A - Aₖ‖² = Σ_{j ≥ k} σⱼ²` (`frobenius_error_truncatedSVD`).
3. `‖Σ - C‖²` is the sum of the squared singular values of `Σ - C`. The singular values of `Σ`
   equal those of `A`, shown by comparing characteristic polynomials.
4. Term by term, `σⱼ(A)² ≤ σ_{j-k}(Σ - C)²` for `j ≥ k` (`interlacing_low_rank_subtraction`).
   The shift `j ↦ j - k` is injective, so the tail sum is at most the full sum.

The rotation in step 1 is not needed; the rectangular proof below skips it.

## Spectral version (square, `src/MatrixNormRelations.lean`, section `EckartYoungSpectral`)

In this section, bare `‖·‖` is the L2 operator norm via local instances.

**`spectral_error_truncatedSVD [Nonempty n] (A) (k) (hk : k < card n) : ‖A - truncatedSVD A k‖ =
singularValues₀ A ⟨k, hk⟩`.** The proof:
- `A - Aₖ` is the SVD tail (`truncatedSVD_add_tail`).
- Unitary invariance (C*-ring lemmas) reduces it to a diagonal matrix.
- `‖·‖` equals the largest singular value, which for a diagonal matrix is its largest entry.
- The largest tail entry is `σₖ`.

**`eckart_young_spectral [Nonempty n] (A) (k) (B) (hB : B.rank ≤ k)`.** The proof:
- If `k < card n`: the error is `σₖ(A)`, which is at most `σ₀(A - B)` by
  `interlacing_for_eckart_young`, and `σ₀(A - B) = ‖A - B‖`.
- Otherwise `truncatedSVD_full` makes the error 0.

Downstream use: `Matrix.Coherence.exists_spectral_minimizer_rank1` and
`spectral_error_truncatedSVD_one_eq_spectralOptimalRank1`.

## Rectangular (`src/TightBounds.lean`)

- `truncatedSVD_rect A k = constructedU_rectangular A * truncatedSingularDiagonal_rect A k * star
  (rightUnitary A)`.
- `truncatedSVD_rect_rank_le` has no hypotheses. The unitary factors don't change the rank. For
  `k < min`, write `D = D * P`, where `P` is the 0/1 diagonal projection onto columns whose
  `eigenvaluesBijection` index is `< k`.
- `spectral_error_truncatedSVD_rect (hk : k < min #m #n) : ‖A - truncatedSVD_rect A k‖ =
  singularValues₀_rect A ⟨k, hk⟩`.
- `frobenius_error_truncatedSVD_rect`: the error is `U D V*` with `D` the tail diagonal
  (`truncatedSVD_rect_tail_eq_USV`), `‖U D V*‖_F = ‖D‖_F` (`frobenius_norm_unitary_conj_rect`),
  and `‖D‖_F² = Re tr(DᴴD)` is summed with `DtD_diagonal_entry`, then reindexed from `n` to
  `Fin (min #m #n)`.
- `sum_sq_tail_le_sum_sq_singularValues_sub`: for `rank B ≤ k`,
  `Σᵢ (tail σᵢ(A))² ≤ Σᵢ σᵢ(A - B)²`, by `interlacing_low_rank_subtraction_rect` and the
  injective shift `j ↦ j - k`.
- `eckart_young_frobenius_rect`: the previous two lemmas plus
  `Matrix.SVD.Rectangular.frobeniusNorm_sq_eq_sum_singularValues_sq_rect`.
- `eckart_young_spectral_rect`: `σₖ(A) ≤ σ₀(A - B) ≤ ‖A - B‖₂`, via
  `spectral_norm_eq_max_singularValue_rect`.
- The Van Loan–Pitsianis theorem (`kroneckerApprox_optimal`) is rectangular Frobenius EY with
  `k = 1`; see `docs/kronecker.md`.
