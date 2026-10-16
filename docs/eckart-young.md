# Eckart–Young

Both optimality theorems are for **square** complex matrices `Matrix n n ℂ`. Both rest on Thompson
interlacing. For rectangular matrices the repo has the spectral error formula and the rank bound
for `truncatedSVD_rect`, but **no optimality theorem**.

| Result | Name | Norm |
|---|---|---|
| Frobenius EY | `Matrix.FrobeniusNorm.eckart_young_frobenius` | Frobenius (local instance) |
| Frobenius EY, re-export with `[Nonempty n]` | `Matrix.SVD.Rectangular.eckart_young_frobenius` | explicit Frobenius `@Norm.norm` |
| Spectral error `‖A - Aₖ‖ = σₖ` | `Matrix.SVD.Rectangular.spectral_error_truncatedSVD` | L2 (local instances) |
| Spectral EY | `Matrix.SVD.Rectangular.eckart_young_spectral` | L2 (local instances) |
| Rectangular spectral error | `Matrix.TightBounds.spectral_error_truncatedSVD_rect` | L2 |
| Rectangular rank bound | `Matrix.TightBounds.truncatedSVD_rect_rank_le` | — |

The `Rectangular` namespace on the second to fourth rows is misleading: those results are square.
`Matrix.SVD.Rectangular.truncatedSVD` is an `abbrev` for the square `Matrix.SVD.truncatedSVD`.

## Key lemma: Thompson interlacing (`src/WeylInequality.lean`)

**`thompson_interlacing`**: if `B.rank ≤ r` and `i + r < card n`, then `σ_{i+r}(A) ≤ σᵢ(A + B)`.
The proof:
- Intersect three subspaces: the head eigenspan of `Aᴴ A` (dimension `i + r + 1`), `ker B`, and a
  tail eigenspan of `(A+B)ᴴ(A+B)`.
- The dimension count is `CourantFischer.finrank_inf_ge_of_sum_gt`.
- A unit vector in the intersection, together with the Rayleigh-quotient bounds from
  CourantFischer, finishes the proof.

Derived forms:
- `interlacing_low_rank_subtraction`: `C.rank ≤ k`, `k ≤ j` gives `σⱼ(A) ≤ σ_{j-k}(A - C)`.
- `interlacing_for_eckart_young`: the same statement with ℕ indices.

## Frobenius version

`eckart_young_frobenius (A) (k) (B) (hB : B.rank ≤ k) : ‖A - truncatedSVD A k‖ ≤ ‖A - B‖`. No
`Nonempty` is needed, because the empty case is handled inside the proof. The steps:

1. Rotate into the SVD basis. Set `C = Uᴴ B V`, so `rank C ≤ k`. Then `‖A - B‖ = ‖Σ - C‖` by
   unitary invariance (`frobenius_error_in_svd_basis`, `frobenius_norm_unitary_mul` /
   `frobenius_norm_mul_unitary`).
2. `‖A - Aₖ‖² = Σ_{j ≥ k} σⱼ²` (`frobenius_error_truncatedSVD`).
3. `‖Σ - C‖²` is the sum of the squared singular values of `Σ - C`. The singular values of `Σ`
   equal those of `A`, shown by comparing characteristic polynomials.
4. Term by term, `σⱼ(A)² ≤ σ_{j-k}(Σ - C)²` for `j ≥ k` (`interlacing_low_rank_subtraction`).
   The shift `j ↦ j - k` is injective, so the tail sum is at most the full sum.

Notes:
- The docstring still mentions "projection optimality". The proof actually uses interlacing.
- The diagonal/off-diagonal split in the proof is expanded and then folded back; it is not
  essential.
- The `EckartYoungBridge` section of CourantFischer opens with a note on why an earlier
  diagonal-only core lemma was false. Of its lemmas, only `norm_sq_mul_eq_inner_AHA` is used
  elsewhere.

## Spectral version (`src/MatrixNormRelations.lean`, section `EckartYoungSpectral`)

In this section, bare `‖·‖` is the L2 operator norm via local instances.

**`spectral_error_truncatedSVD [Nonempty n] (A) (k) (hk : k < card n) : ‖A - truncatedSVD A k‖ =
singularValues₀ A ⟨k, hk⟩`.** The proof:
- `A - Aₖ` is the SVD tail (`truncatedSVD_add_tail`).
- Unitary invariance (C*-ring lemmas) reduces it to a diagonal matrix.
- `‖·‖` equals the largest singular value, which for a diagonal matrix is its largest entry.
- The largest tail entry is `σₖ`.

**`eckart_young_spectral [Nonempty n] (A B) (k) (hB : B.rank ≤ k)`.** The proof:
- If `k < card n`: the error is `σₖ(A)`, which is at most `σ₀(A - B)` by
  `interlacing_for_eckart_young`, and `σ₀(A - B) = ‖A - B‖`.
- Otherwise `truncatedSVD_full` makes the error 0.

`eckart_young_spectral` has one downstream use: `Matrix.Coherence.exists_spectral_minimizer_rank1`.
It is called with its full name because no file opens `Matrix.SVD.Rectangular`.

## Rectangular (`src/TightBounds.lean`)

- `truncatedSVD_rect A k = constructedU_rectangular A * truncatedSingularDiagonal_rect A k * star
  (rightUnitary A)`.
- `truncatedSVD_rect_rank_le` has no hypotheses. The unitary factors don't change the rank. For
  `k < min`, write `D = D * P`, where `P` is the 0/1 diagonal projection onto columns whose
  `eigenvaluesBijection` index is `< k`.
- `spectral_error_truncatedSVD_rect (hk : k < min #m #n) : ‖A - truncatedSVD_rect A k‖ =
  singularValues₀_rect A ⟨k, hk⟩`.
- Missing: rectangular optimality (Frobenius or spectral) and a rectangular Frobenius error
  formula. A rectangular EY would most likely need a rectangular Thompson interlacing first;
  WeylInequality is square-only.
