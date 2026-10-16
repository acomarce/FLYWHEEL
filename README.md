# FLYWHEEL

**F**ormalized **L**inear Algebra in **L**ean 4

A Lean 4 formalization of fundamental theorems in matrix analysis, including the Courant-Fischer min-max theorem, Singular Value Decomposition (SVD), Frobenius norm properties, and the Eckart-Young theorem.

## Overview

FLYWHEEL provides machine-verified proofs of key results in numerical linear algebra, built on top of [Mathlib4](https://github.com/leanprover-community/mathlib4). The library focuses on spectral theory and matrix approximation.

## Contents

| File | Description |
|------|-------------|
| [SVD.lean](src/SVD.lean) | Singular Value Decomposition for complex matrices |
| [CourantFischer.lean](src/CourantFischer.lean) | Courant-Fischer min-max characterization of eigenvalues |
| [FrobeniusNorm.lean](src/FrobeniusNorm.lean) | Frobenius norm properties, unitary invariance, Eckart-Young (Frobenius) |
| [MatrixNormRelations.lean](src/MatrixNormRelations.lean) | Spectral (L2 operator) norm facts, Eckart-Young (spectral), Kronecker norm bounds |
| [WeylInequality.lean](src/WeylInequality.lean) | Weyl's eigenvalue and singular value inequalities |
| [KroneckerRearrangement.lean](src/KroneckerRearrangement.lean) | Van Loan-Pitsianis rearrangement for Kronecker approximation |
| [SpectralNormGap.lean](src/SpectralNormGap.lean) | Spectral norm bounds for Kronecker approximation |
| [TightBounds.lean](src/TightBounds.lean) | Tight error bounds for rank-k approximation |
| [CoherenceCharacterization.lean](src/CoherenceCharacterization.lean) | Coherence/incoherence characterization |
| [TruncatedSVDRank1.lean](src/TruncatedSVDRank1.lean) | Truncated SVD for rank-1 matrices |

## Main Results

### Singular Value Decomposition
- `singularValues`: Definition of singular values as √(eigenvalues of Aᴴ * A)
- `singularValues_nonneg`: Singular values are non-negative
- `singularValues₀_antitone`: Sorted singular values are decreasing
- `svd_decomposition`: Any square matrix admits an SVD: A = U * Σ * Vᴴ

### Courant-Fischer Theorem
- `subspace_intersection_nontrivial`: Dimension counting for subspace intersections
- `rayleigh_eq_eigenvalue_on_eigenvector`: R(uᵢ) = λᵢ for eigenvector uᵢ
- `rayleigh_le_eigenvalue_max`: R(x) ≤ λ_max for unit vectors
- `rayleigh_ge_eigenvalue_min`: R(x) ≥ λ_min for unit vectors

### Frobenius Norm & Eckart-Young
- `frobenius_norm_sq_eq_trace`: ‖A‖_F² = Re(trace(Aᴴ * A))
- `frobenius_norm_unitary_mul`: ‖U * A‖_F = ‖A‖_F for unitary U
- `frobenius_norm_mul_unitary`: ‖A * V‖_F = ‖A‖_F for unitary V
- `frobenius_norm_sq_diagonal`: ‖diagonal d‖_F² = Σᵢ |dᵢ|²
- `eckart_young_frobenius`: ‖A - Aₖ‖_F ≤ ‖A - B‖_F for every B with rank B ≤ k (square matrices)
- `eckart_young_spectral`: ‖A - Aₖ‖₂ ≤ ‖A - B‖₂ for every B with rank B ≤ k (square matrices)
- `spectral_error_truncatedSVD`: ‖A - Aₖ‖₂ = σₖ (0-indexed)

### Weyl Inequalities
- `weyl_eigenvalue_lower_bound`: λₖ(A+B) ≥ λₖ(A) + λₙ₋₁(B)
- `weyl_eigenvalue_upper_bound`: λₖ(A+B) ≤ λₖ(A) + λ₀(B)
- `thompson_interlacing`: σᵢ₊ᵣ(A) ≤ σᵢ(A+B) when rank B ≤ r

### Kronecker Approximation
- `R_kronecker`: R(A ⊗ B) = vec(A) ⬝ vec(B)ᵀ (Van Loan-Pitsianis)
- `R_frobenius_norm_eq`: ‖R(M)‖_F = ‖M‖_F (Frobenius isometry)

Full names, files and line numbers for every declaration are in [docs/INDEX.md](docs/INDEX.md)
(for example `eckart_young_spectral` is `Matrix.SVD.Rectangular.eckart_young_spectral`).
Proof-architecture notes are in [docs/](docs/).

## Requirements

- [Lean 4](https://leanprover.github.io/lean4/doc/), version pinned in [lean-toolchain](lean-toolchain)
  (installed automatically by [elan](https://github.com/leanprover/elan))
- [Mathlib4](https://github.com/leanprover-community/mathlib4), revision pinned in
  [lake-manifest.json](lake-manifest.json)

## Building

From the repository root:

```bash
lake exe cache get   # download prebuilt Mathlib
lake build           # build all libraries
```

Don't run `lake update`: it would move Mathlib to the latest `master`, past the pinned revision.

## License

Apache License 2.0. See [LICENSE](LICENSE) for details.

## Citation

If you use FLYWHEEL in your research, please cite:

### BibTeX
```bibtex
@software{flywheel2025,
  author       = {Markovski, Aleksandar},
  title        = {{FLYWHEEL}: Formalized Linear Algebra in Lean 4},
  year         = {2025},
  url          = {https://github.com/acomarce/FLYWHEEL},
  license      = {Apache-2.0}
}
```

### APA
Markovski, A. (2025). *FLYWHEEL: Formalized Linear Algebra in Lean 4* [Computer software]. https://github.com/acomarce/FLYWHEEL

### Chicago
Markovski, Aleksandar. 2025. "FLYWHEEL: Formalized Linear Algebra in Lean 4." https://github.com/acomarce/FLYWHEEL.

## References

- Horn, R.A. & Johnson, C.R. (2012). *Matrix Analysis*. Cambridge University Press.
- Van Loan, C.F. & Pitsianis, N. (1993). "Approximation with Kronecker Products". *Linear Algebra for Large Scale and Real-Time Applications*, pp. 293-314.
- [Mathlib Documentation](https://leanprover-community.github.io/mathlib4_docs/)
