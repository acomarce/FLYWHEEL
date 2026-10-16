<div align="center">

# FLYWHEEL

**Formalized Linear Algebra in Lean 4**

Machine-checked matrix analysis on Mathlib: the SVD, Courant–Fischer, Weyl and Thompson
interlacing, Eckart–Young, and Kronecker (Van Loan–Pitsianis) approximation.

[![Lean build](https://github.com/acomarce/FLYWHEEL/actions/workflows/lean.yml/badge.svg?branch=main)](https://github.com/acomarce/FLYWHEEL/actions/workflows/lean.yml)
[![sorry-free](https://img.shields.io/badge/proofs-sorry--free-brightgreen)](.github/workflows/lean.yml)
[![Lean](https://img.shields.io/badge/Lean-v4.26.0--rc2-blue)](lean-toolchain)
[![Mathlib](https://img.shields.io/badge/Mathlib-dc19f2a-blue)](https://github.com/leanprover-community/mathlib4/tree/dc19f2a67ff55a2078ba23a4c1740a5eb0d50e41)
[![License](https://img.shields.io/github/license/acomarce/FLYWHEEL)](LICENSE)

</div>

## Main results

Matrices are complex and square unless stated otherwise. Singular values σ₀ ≥ σ₁ ≥ ⋯ and
eigenvalues λ₀ ≥ λ₁ ≥ ⋯ are sorted and 0-indexed, as in the code. Aₖ is the rank-k truncated SVD.

| Result | Statement |
|---|---|
| **SVD**<br>`svd_decomposition`<br>`svd_decomposition_rectangular`<br>`Real.svd_decomposition` | A = UΣVᴴ with U, V unitary and Σ diagonal, σᵢ ≥ 0. Also for m × n matrices (Σ rectangular diagonal, σ sorted) and for real matrices (U, V orthogonal). |
| **Norms from σ** (m × n)<br>`spectral_norm_eq_max_singularValue_rect`<br>`frobeniusNorm_sq_eq_sum_singularValues_sq_rect` | ‖A‖₂ = σ₀ and ‖A‖<sub>F</sub>² = Σᵢ σᵢ² |
| **Courant–Fischer**<br>`courantFischer_maxMin_bounds`<br>`courantFischer_minMax_bounds` | For Hermitian A with Rayleigh quotient R: λₖ = max<sub>dim W = k+1</sub> min<sub>0 ≠ x ∈ W</sub> R(x) = min<sub>dim W = n−k</sub> max<sub>0 ≠ x ∈ W</sub> R(x) |
| **Weyl**<br>`weyl_eigenvalue_bounds`<br>`weyl_singularValue_perturbation` | For Hermitian A, B: λₖ(A) + λₙ₋₁(B) ≤ λₖ(A + B) ≤ λₖ(A) + λ₀(B). For any A, B: \|σₖ(A) − σₖ(B)\| ≤ σ₀(A − B) |
| **Thompson interlacing**<br>`thompson_interlacing` | rank B ≤ r ⇒ σᵢ₊ᵣ(A) ≤ σᵢ(A + B) |
| **Eckart–Young** (Frobenius)<br>`FrobeniusNorm.eckart_young_frobenius` | rank B ≤ k ⇒ ‖A − Aₖ‖<sub>F</sub> ≤ ‖A − B‖<sub>F</sub> |
| **Eckart–Young** (spectral)<br>`eckart_young_spectral`<br>`spectral_error_truncatedSVD` | rank B ≤ k ⇒ ‖A − Aₖ‖₂ ≤ ‖A − B‖₂, and ‖A − Aₖ‖₂ = σₖ |
| **Truncated SVD** (m × n)<br>`spectral_error_truncatedSVD_rect`<br>`truncatedSVD_rect_rank_le` | ‖A − Aₖ‖₂ = σₖ and rank Aₖ ≤ k |
| **Van Loan–Pitsianis**<br>`R_kronecker`<br>`R_frobenius_norm_eq` | R(A ⊗ B) = vec(A) vec(B)ᵀ and ‖R(M)‖<sub>F</sub> = ‖M‖<sub>F</sub> |
| **Kronecker approximation**<br>`kronecker_approx_frobenius_error`<br>`kronecker_spectral_error_le_frobenius_error` | ‖C − A ⊗ B‖<sub>F</sub> = ‖R(C) − vec(A) vec(B)ᵀ‖<sub>F</sub> and ‖C − R⁻¹(M)‖₂ ≤ ‖R(C) − M‖<sub>F</sub> |
| **Kronecker norm**<br>`l2_opNorm_kronecker` | ‖A ⊗ B‖₂ = ‖A‖₂ ‖B‖₂ for rectangular A, B |
| **Coherence**<br>`coherenceFactorRect_ge_inv_sqrt_rank`<br>`coherenceFactorRect_le_one` | μ(E) = ‖E‖<sub>F</sub> / (√rank E · ‖E‖₂) lies in [1/√rank E, 1] for E ≠ 0 |

Names are abbreviated. [`docs/INDEX.md`](docs/INDEX.md) lists every declaration with its full name,
file, line and summary.

> [!NOTE]
> Eckart–Young optimality is proved for square matrices only; for m × n matrices the repo has the
> error formula and rank bound above. A few names claim more than their statements:
> `R_inv_bound_achievable_rank1` and `bound_tight_rank1` (SpectralNormGap) prove only an upper
> bound, and `nearly_coherent_bound`, `nearly_coherent_spectral_lower_bound`,
> `frobenius_spectral_distance_with_gap` and `decision_criterion` (CoherenceCharacterization) take
> no coherence or gap hypothesis. Their docstrings say what is proved.

## Layout

| File | Contents |
|---|---|
| [`SVD`](src/SVD.lean) | Singular values; square, real and rectangular SVD; norms via σ; rectangular coherence factor |
| [`KroneckerRearrangement`](src/KroneckerRearrangement.lean) | `vec`, the rearrangement `R` and its inverse, Frobenius isometry |
| [`CourantFischer`](src/CourantFischer.lean) | Rayleigh quotients and the min-max theorem |
| [`TruncatedSVDRank1`](src/TruncatedSVDRank1.lean) | rank A ≤ 1 ⇒ A₁ = A |
| [`WeylInequality`](src/WeylInequality.lean) | Weyl eigenvalue and singular-value bounds, Thompson interlacing |
| [`FrobeniusNorm`](src/FrobeniusNorm.lean) | Trace formula, unitary invariance, ‖A − Aₖ‖<sub>F</sub>² = Σ<sub>i≥k</sub> σᵢ², Eckart–Young (Frobenius) |
| [`MatrixNormRelations`](src/MatrixNormRelations.lean) | ‖A‖₂ = σ₀, Eckart–Young (spectral), ‖A ⊗ B‖₂, Kronecker perturbation bounds |
| [`SpectralNormGap`](src/SpectralNormGap.lean) | Spectral-norm bounds for Kronecker approximation through R⁻¹ |
| [`CoherenceCharacterization`](src/CoherenceCharacterization.lean) | Coherence of the approximation error; Frobenius- vs spectral-optimal rank-1 solutions |
| [`TightBounds`](src/TightBounds.lean) | Rectangular truncated SVD: spectral error and rank bound |

<details>
<summary>Import graph (an arrow points to the file that imports)</summary>

```mermaid
graph TD
  SVD --> CourantFischer
  SVD --> TruncatedSVDRank1
  SVD --> WeylInequality
  CourantFischer --> WeylInequality
  SVD --> FrobeniusNorm
  WeylInequality --> FrobeniusNorm
  FrobeniusNorm --> MatrixNormRelations
  KroneckerRearrangement --> MatrixNormRelations
  MatrixNormRelations --> SpectralNormGap
  MatrixNormRelations --> CoherenceCharacterization
  SpectralNormGap --> CoherenceCharacterization
  MatrixNormRelations --> TightBounds
  SpectralNormGap --> TightBounds
```

</details>

Proof notes: [SVD](docs/svd.md) · [Eckart–Young](docs/eckart-young.md) ·
[Kronecker](docs/kronecker.md).

## Build

[elan](https://github.com/leanprover/elan) installs the toolchain pinned in
[`lean-toolchain`](lean-toolchain); Mathlib is pinned in [`lake-manifest.json`](lake-manifest.json).

```bash
lake exe cache get   # prebuilt Mathlib, once
lake build           # all 10 libraries
lake build SVD       # one library and its imports
```

Don't run `lake update`: `lakefile.toml` tracks Mathlib `master`, so it would jump past the
pinned revision.

CI builds every library on each push to `main` and each pull request, fails on any `sorry`, `admit` or `axiom`,
and checks that `docs/INDEX.md` is current.

## Citation

```bibtex
@software{flywheel2025,
  author  = {Markovski, Aleksandar},
  title   = {{FLYWHEEL}: Formalized Linear Algebra in Lean 4},
  year    = {2025},
  url     = {https://github.com/acomarce/FLYWHEEL},
  license = {Apache-2.0}
}
```

## References

- C. Eckart, G. Young. The approximation of one matrix by another of lower rank.
  *Psychometrika* 1(3), 211–218, 1936.
- H. Weyl. Das asymptotische Verteilungsgesetz der Eigenwerte linearer partieller
  Differentialgleichungen. *Math. Ann.* 71, 441–479, 1912.
- C. F. Van Loan, N. Pitsianis. Approximation with Kronecker products. In *Linear Algebra for
  Large Scale and Real-Time Applications*, 293–314, 1993.
- R. A. Horn, C. R. Johnson. *Matrix Analysis*, 2nd ed. Cambridge University Press, 2012.
- G. H. Golub, C. F. Van Loan. *Matrix Computations*, 4th ed. Johns Hopkins University Press, 2013.

## License

[Apache 2.0](LICENSE)
