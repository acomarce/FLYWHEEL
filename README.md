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
| [SpectralNormGap.lean](src/SpectralNormGap.lean) | Spectral vs. Frobenius bounds for Kronecker approximation |
| [TightBounds.lean](src/TightBounds.lean) | Rectangular truncated SVD: error formulas, Eckart-Young, Van Loan-Pitsianis |
| [CoherenceCharacterization.lean](src/CoherenceCharacterization.lean) | Coherence/incoherence characterization |
| [TruncatedSVDRank1.lean](src/TruncatedSVDRank1.lean) | truncatedSVD A k = A when rank A ≤ k |

## Main Results

Short names below; full names, files and line numbers for every declaration are in
[docs/INDEX.md](docs/INDEX.md).

### Singular Value Decomposition
- `svd_decomposition`: every square complex matrix is A = U * Σ * Vᴴ with U, V unitary and Σ
  diagonal with nonnegative entries
- `svd_decomposition_rectangular`: the same for m × n matrices, with Σ the m × n diagonal of the
  sorted singular values
- `singularValues₀_antitone`: sorted singular values are decreasing

### Courant-Fischer Theorem
- `courantFischer_maxMin` / `courantFischer_minMax`: λₖ is the greatest (least) value of the
  max-min (min-max) Rayleigh-quotient expression (`IsGreatest` / `IsLeast`)
- `courantFischer_maxMin_eq_iSup` / `courantFischer_minMax_eq_iInf`: the same as equalities

### Weyl and Thompson Inequalities
- `weyl_eigenvalue_lower_bound` / `weyl_eigenvalue_upper_bound`: λₖ(A) + λₙ₋₁(B) ≤ λₖ(A+B) ≤
  λₖ(A) + λ₀(B)
- `weyl_singularValue_perturbation`: |σₖ(A) - σₖ(B)| ≤ σ₀(A - B), which is ‖A - B‖₂
- `thompson_interlacing` / `thompson_interlacing_rect`: σᵢ₊ᵣ(A) ≤ σᵢ(A+B) when rank B ≤ r

### Eckart-Young
- `eckart_young_frobenius` / `eckart_young_frobenius_rect`: ‖A - Aₖ‖_F ≤ ‖A - B‖_F for every B
  with rank B ≤ k (square / rectangular)
- `eckart_young_spectral` / `eckart_young_spectral_rect`: the same in the spectral norm
- `spectral_error_truncatedSVD(_rect)`: ‖A - Aₖ‖₂ = σₖ (0-indexed)
- `frobenius_error_truncatedSVD(_rect)`: ‖A - Aₖ‖_F² = Σᵢ≥ₖ σᵢ²

### Spectral vs. Frobenius Norm
- `norm_eq_frobeniusNorm'_iff_rank_le_one` / `spectral_eq_frobenius_rect_iff_rank_le_one`:
  ‖A‖₂ = ‖A‖_F iff rank A ≤ 1 (square / rectangular)
- `coherenceFactor_eq_one_iff`: the coherence factor ‖A‖_F / (√rank A · ‖A‖₂) equals 1 iff all
  nonzero singular values are equal
- `stableRank_le_effectiveRank`: (‖A‖_F / ‖A‖₂)² ≤ exp(entropy of σᵢ² / ‖A‖_F²)

### Kronecker Approximation
- `R_kronecker`: R(A ⊗ B) = vec(A) vec(B)ᵀ; `R_frobenius_norm_eq`: R is a Frobenius isometry
- `kroneckerApprox_optimal` (Van Loan-Pitsianis): `kroneckerApprox M`, the image under R⁻¹ of the
  rank-1 truncated SVD of R(M), satisfies ‖M - kroneckerApprox M‖_F ≤ ‖M - A ⊗ B‖_F for all A, B;
  `kroneckerApprox_isKronecker` shows it is itself a Kronecker product
- `kroneckerApprox_error_sq`: its squared error is Σᵢ≥₁ σᵢ(R(M))²
- `R_inv_spectral_eq_frobenius_iff_rank_le_one`: ‖R⁻¹X‖₂ ≤ ‖X‖_F is an equality iff
  rank(R⁻¹X) ≤ 1

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
