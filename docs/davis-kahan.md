# Davis–Kahan

`src/DavisKahan.lean`, namespace `Matrix.DavisKahan`. Bare `‖·‖` on square matrices is the L2
operator norm (the global CStar instance from MatrixNormRelations), and on `EuclideanSpace ℂ n`
the Euclidean norm. Eigenvalues are sorted and 0-indexed: λ₀ ≥ λ₁ ≥ ⋯.

| Result | Name |
|---|---|
| (μ − λ₁) ‖v − ⟨u₀, v⟩u₀‖ ≤ ‖E‖₂ ‖v‖ when (A + E) v = μ v, μ > λ₁ | `davis_kahan_top` |
| Gap form: ‖v − ⟨u₀, v⟩u₀‖ ≤ ‖E‖₂ / (λ₀ − λ₁ − ‖E‖₂) | `davis_kahan_top_of_norm_lt_gap`, `davis_kahan_top_eigenvector` |
| Top-k, one vector: (μ − λₖ) ‖v − P v‖ ≤ ‖E‖₂ ‖v‖ when μ > λₖ | `davis_kahan_topIndices` |
| Top-k gap form: ‖v − P v‖ ≤ ‖E‖₂ / (λₖ₋₁ − λₖ − ‖E‖₂) | `davis_kahan_topIndices_of_norm_lt_gap` |
| ‖sin Θ‖_F² = Σⱼ ‖ũⱼ − P ũⱼ‖² ≤ k (‖E‖₂ / (λₖ₋₁ − λₖ − ‖E‖₂))² | `davis_kahan_sin_theta` |
| Top right singular vector via Aᴴ A, gap σ₀² − σ₁² | `top_right_singular_vector_perturbation` |
| The same in ‖Ã − A‖₂ and `spectralGap A` | `top_right_singular_vector_perturbation_of_spectralGap` |

Here u₀ is `hA.eigenvectorBasis (topIndex h2)`, P v = Σ_{i ∈ topIndices k} ⟨uᵢ, v⟩ uᵢ is the
orthogonal projection onto the span of the eigenvectors for λ₀, …, λₖ₋₁, and ũⱼ is
`(hA.add hE).eigenvectorBasis j` for j ∈ `topIndices k`.

## Indexing

- `topIndex h2 : n` is `Fintype.equivOfCardEq (Fintype.card_fin _) ⟨0, _⟩`, the preimage of sorted
  index 0 under Mathlib's eigenvalue bijection. `eigenvalues_topIndex` gives
  `hA.eigenvalues (topIndex h2) = hA.eigenvalues₀ 0` by `CourantFischer.eigenvalues_eq_eigenvalues₀_comp`.
- `topIndices k hk : Finset n` is the image of `Finset.Iio ⟨k, hk⟩` under the same bijection, so
  it is the same set for every Hermitian matrix on `n`. That is what lets the sin Θ theorem sum
  over the top-k eigenvectors of A + E and project onto those of A with one index set.
  `card_topIndices`, `mem_topIndices`, `eigenvalues_le_of_not_mem_topIndices` (λᵢ ≤ λₖ off the
  set) and `le_eigenvalues_of_mem_topIndices` (λₖ₋₁ ≤ λᵢ on it) are the API.

## Proof

1. `norm_sq_perturbation_eq_sum`: if (A + E) v = μ v then E v = μ v − A v, so in A's eigenbasis
   ⟨uᵢ, E v⟩ = (μ − λᵢ) ⟨uᵢ, v⟩, and Parseval
   (`OrthonormalBasis.sum_sq_norm_inner_right`) gives ‖E v‖² = Σᵢ (μ − λᵢ)² |⟨uᵢ, v⟩|². E need not
   be Hermitian.
2. The residual w = v − P v has coefficient 0 on the head indices and ⟨uᵢ, v⟩ elsewhere, so
   ‖w‖² = Σ_{i off the head} |⟨uᵢ, v⟩|².
3. Off the head λᵢ ≤ λₖ (λ₁ for the top vector), so (μ − λₖ)² ‖w‖² ≤ ‖E v‖² ≤ ‖E‖₂² ‖v‖²
   (`Matrix.l2_opNorm_mulVec`).
4. Gap form: Weyl's lower bound for one eigenvalue (`eigenvalues₀_sub_norm_le_add`, from
   `weyl_eigenvalue_lower_bound` and |λ(E)| ≤ ‖E‖₂, `abs_eigenvalues₀_le_norm`) gives
   μ ≥ λₖ₋₁(A) − ‖E‖₂ for each top-k eigenvalue μ of A + E, hence μ − λₖ ≥ δ − ‖E‖₂ > 0.
5. sin Θ: apply 4 to each ũⱼ (a unit vector), square, and sum over the k indices.
6. Singular vectors: apply the gap form to G = Aᴴ A and F = Ãᴴ Ã − Aᴴ A, with
   λᵢ(G) = σᵢ(A)² (`SVD.singularValues₀_sq`). `norm_gram_sub_le` bounds ‖F‖₂ by
   ‖Ã − A‖₂ (‖Ã‖₂ + ‖A‖₂), and `spectralGap_mul_norm_le_sq_sub_sq` bounds the gap σ₀² − σ₁² below by
   `spectralGap A * ‖A‖₂` = (σ₀ − σ₁) σ₀.

## Wedin's theorem (`src/Wedin.lean`)

Namespace `Matrix.Wedin`. Matrices are m × n, Ã = A + E, and singular values are 0-indexed and
sorted, σᵢ = √λᵢ(Aᴴ A).

| Result | Name |
|---|---|
| (μ − c)² (‖x − P_U x‖² + ‖y − P_V y‖²) ≤ ‖μ x − T y‖² + ‖μ y − S x‖² for μ ≥ c | `wedin_residual` |
| Σⱼ (‖xⱼ − P_U xⱼ‖² + ‖yⱼ − P_V yⱼ‖²) ≤ Σⱼ (‖μⱼ xⱼ − T yⱼ‖² + ‖μⱼ yⱼ − S xⱼ‖²) / δ² for μⱼ ≥ c + δ | `wedin_sin_theta_residual` |
| ‖sin Θ_U‖_F² + ‖sin Θ_V‖_F² ≤ Σⱼ (‖E ṽⱼ‖² + ‖Eᴴ ũⱼ‖²) / δ², δ = σₖ₋₁(Ã) − σₖ(A) | `wedin_sin_theta` |
| The same bounded by 2k ‖E‖₂² / δ² | `wedin_sin_theta_l2` |

The first two rows hold for any linear maps T, S between complex inner product spaces with
⟨x, T y⟩ = ⟨S x, y⟩, pairs (uᵢ, vᵢ) orthonormal on an index set with T vᵢ = σᵢ uᵢ and
S uᵢ = σᵢ vᵢ, and ‖T y‖ ≤ c ‖y‖ for y orthogonal to every vᵢ. For matrices, T = A, S = Aᴴ and
c = σₖ(A).

- **Singular triples.** `rightSingularVector A i` is the i-th vector of the eigenvector basis of
  Aᴴ A, σᵢ is `SVD.Rectangular.singularValueFromEigenvalue A i`, and `leftSingularVector A i` is
  σᵢ⁻¹ A vᵢ. The left vectors are orthonormal wherever λᵢ > 0 (`inner_leftSingularVector`). The
  top-k index set is `DavisKahan.topIndices k`, the same set for A and Ã.
- **Hypotheses.** `wedin_sin_theta` needs k < n, so that σₖ exists, and λₖ₋₁(Aᴴ A) > 0, i.e.
  rank A ≥ k. Without the rank condition the top-k left singular vectors are not of the form
  σᵢ⁻¹ A vᵢ.
- **No factor k.** The Frobenius form is a sum over columns, and each column (ũⱼ, ṽⱼ) satisfies
  the one-vector bound with the same gap.

Proof of `wedin_residual`, with x₂ = x − P_U x and y₂ = y − P_V y:
1. T maps span {vᵢ} into span {uᵢ} and S maps span {uᵢ} into span {vᵢ}, so T y₂ ⊥ uᵢ and
   S x₂ ⊥ vᵢ. By Pythagoras, splitting off the spans does not increase either residual
   (`norm_sq_residual_proj_le`).
2. ‖T y₂‖ ≤ c ‖y₂‖ by hypothesis. Then ‖S x₂‖² = ⟨x₂, T S x₂⟩ ≤ ‖x₂‖ c ‖S x₂‖ gives
   ‖S x₂‖ ≤ c ‖x₂‖. For matrices the hypothesis is `norm_toEuclideanLin_le_of_orthogonal`:
   ‖A y‖² ≤ ‖Aᴴ A y‖ ‖y‖ ≤ λₖ ‖y‖², by Parseval in the eigenbasis.
3. The triangle inequality gives ‖μ x₂ − T y₂‖ ≥ μ ‖x₂‖ − c ‖y₂‖ and ‖μ y₂ − S x₂‖ ≥ μ ‖y₂‖ − c ‖x₂‖.
   `sq_sub_mul_add_sq_le` turns these into (μ − c)² (‖x₂‖² + ‖y₂‖²): multiplying the first by
   ‖x₂‖ and the second by ‖y₂‖ gives (μ − c)(‖x₂‖² + ‖y₂‖²) ≤ P ‖x₂‖ + Q ‖y₂‖, and then
   Cauchy–Schwarz in ℝ² finishes it.

## What is not proved

- The operator-norm sin Θ ‖(I − P) P̃‖₂ ≤ ‖E‖₂ / δ for k > 1. The vector-by-vector argument
  above only reaches the Frobenius form with the factor k; the operator-norm version needs the
  Sylvester-equation bound ‖X Λ̃ − Λ X‖ ≥ δ ‖X‖.
- The Gram-matrix singular-vector results above are square-only, and their bound for small
  ‖Ã − A‖₂ is about 2 ‖Ã − A‖₂ / (σ₀ − σ₁), twice Wedin's. Wedin's theorem itself, below, covers
  both singular subspaces of rectangular matrices.
- Wedin in operator-norm form, max(‖sin Θ_U‖₂, ‖sin Θ_V‖₂) ≤ max(‖E Ṽ‖₂, ‖Eᴴ Ũ‖₂) / δ, and
  Wedin with A's own gap σₖ₋₁(A) − σₖ(A) − ‖E‖₂ in place of δ. The latter needs Weyl's bound
  σₖ₋₁(Ã) ≥ σₖ₋₁(A) − ‖E‖₂ for rectangular singular values; only the square one is proved.
- The top vector u₀ is the specific vector of Mathlib's eigenvector basis. When λ₀ > λ₁ any other
  unit top eigenvector differs from it by a phase, and ‖v − ⟨u₀, v⟩u₀‖ does not depend on the
  phase, but no lemma states this.
