# FLYWHEEL: notes for Claude

FLYWHEEL is a Lean 4 + Mathlib formalization of matrix analysis: SVD, Courant–Fischer, Weyl and
Thompson interlacing, Eckart–Young, Kronecker (Van Loan–Pitsianis) approximation and coherence.
There are no `sorry`/`axiom`/`admit`, and it must stay that way.

## Layout

- Lake project at the repo root:
  - `lakefile.toml` sets `srcDir = "src"`.
  - `lean-toolchain` pins `leanprover/lean4:v4.26.0-rc2`.
  - `lake-manifest.json` pins Mathlib at `dc19f2a6…`.
- All Lean sources are flat in `src/`. Each file is its own `lean_lib` of the same name (module
  `SVD` = `src/SVD.lean`).
- To add a file: add a `[[lean_lib]]` and put it in `defaultTargets`. The index check fails
  otherwise.
- `docs/INDEX.md`: every top-level declaration with full name, kind, `file:line` and a doc
  summary. It is generated, so **grep it** to find a lemma instead of reading the sources.
- `docs/svd.md`, `docs/eckart-young.md`, `docs/kronecker.md`: proof architecture notes and known
  traps.
- `scripts/gen_index.py`: generates and checks the index. `.claude/hooks/session-start.sh`:
  cloud-session setup.

## Build

```bash
lake exe cache get          # prebuilt Mathlib oleans; needed once
lake build                  # builds all 10 libraries (defaultTargets lists them all)
lake build TightBounds      # one library plus its imports
lake env lean src/SVD.lean  # elaborate a single file
python3 -I scripts/gen_index.py   # regenerate docs/INDEX.md after editing any .lean file
```

- **Never run `lake update`.** `lakefile.toml` requires Mathlib `rev = "master"`, so an update
  would jump far past the pinned revision and toolchain.
- The build prints many linter warnings (`unusedSectionVars`, `unusedVariables`,
  `unusedSimpArgs`). They predate this setup and are not errors. Do not mass-fix them in an
  unrelated change.

### Cloud sessions (claude.ai/code)

- The network policy blocks the Mathlib cache hosts (`lakecache.blob.core.windows.net`,
  `mathlib4.lean-cache.cloud`) and `releases.lean-lang.org`.
- The SessionStart hook installs elan and the pinned toolchain from GitHub release assets, then
  clones Mathlib. It runs `lake exe cache get` only if a cache host answers, and otherwise
  prints a warning.
- Without the cache, `lake build` and `lake env lean` compile Mathlib from source, which takes
  hours. **Don't.** Instead:
  - Grep `.lake/packages/mathlib/Mathlib` for Mathlib API names.
  - Run `python3 -I scripts/gen_index.py --check` (fast; catches lakefile and comment/scope
    damage).
  - Push and read the CI job log (GitHub MCP `get_job_logs`). A run takes about 4 minutes.
- If the owner adds the cache hosts to the environment's allowed domains, local builds work.
- Manual toolchain install, if the hook didn't run:
  - Download `lean-4.26.0-rc2-linux.tar.zst` from the `leanprover/lean4` GitHub release.
  - Decompress it with `zstd`, or with python `zstandard` if `zstd` is missing.
  - Extract it to `~/.elan/toolchains/leanprover--lean4---v4.26.0-rc2`.

## Import graph (project-internal)

```
SVD, KroneckerRearrangement   roots
CourantFischer                ← SVD
TruncatedSVDRank1             ← SVD
WeylInequality                ← SVD, CourantFischer
FrobeniusNorm                 ← SVD, WeylInequality
MatrixNormRelations           ← FrobeniusNorm, KroneckerRearrangement
SpectralNormGap               ← MatrixNormRelations
CoherenceCharacterization     ← MatrixNormRelations, SpectralNormGap
TightBounds                   ← MatrixNormRelations, SpectralNormGap
```

`CourantFischer` and `WeylInequality` do `import Mathlib`; the other files import specific
modules.

## Namespace map

Namespaces do not match file names. Always look a name up in `docs/INDEX.md`.

| File | Namespaces |
|---|---|
| SVD | `Matrix.SVD` (square), `Matrix.SVD.Real`, `Matrix.SVD.Rectangular`, and root (see below) |
| KroneckerRearrangement | `Matrix.KroneckerRearrangement` (`vec`, `R`, `R_inv`, `outerProduct`) |
| CourantFischer | top-level `CourantFischer` (not `Matrix.*`) |
| TruncatedSVDRank1 | root (no namespace) |
| WeylInequality | `Matrix.WeylInequality` (Weyl, Thompson interlacing) |
| FrobeniusNorm | `Matrix.FrobeniusNorm` (includes `eckart_young_frobenius`) |
| MatrixNormRelations | `Matrix.SVD`, `Matrix.SpectralNorm`, `Matrix.SVD.Rectangular`, `Matrix.KroneckerRearrangement`, `Matrix.KroneckerPerturbation` |
| SpectralNormGap | `Matrix.Kronecker.SpectralGap`, `Matrix.Kronecker.SpectralGapCharacterization` |
| CoherenceCharacterization | `Matrix.Coherence` |
| TightBounds | `Matrix.TightBounds` (rectangular `truncatedSVD_rect`, `singularValues₀_rect`) |

Traps:
- **`Matrix.SVD.Rectangular` is split across two files.** The genuinely rectangular SVD is in
  SVD.lean. MatrixNormRelations.lean adds `truncatedSVD` (an `abbrev` for the *square*
  `Matrix.SVD.truncatedSVD`), `eckart_young_frobenius`, `spectral_error_truncatedSVD` and
  `eckart_young_spectral`, and **all of these are square-only**. Example:
  `Matrix.SVD.Rectangular.eckart_young_spectral`.
- **SVD.lean has root-namespace sections.** `FrobeniusNormRectangular` and
  `SpectralNormRectangular` declare fully qualified `Matrix.SVD.Rectangular.*` names (their
  private helpers stay at root). `RectangularCoherenceFactor` is genuinely root:
  `coherenceFactorRect`, `frobeniusNormRect`, ….
- **Nothing opens `Matrix.SVD.Rectangular`.** Downstream files spell names fully, e.g.
  `Matrix.SVD.Rectangular.eckart_young_spectral` in CoherenceCharacterization.

## Norms: check which one is active before touching any `‖·‖`

- Mathlib has no default norm on `Matrix`. Files switch one on per section with
  `attribute [local instance] …`:
  - **Frobenius**: `Matrix.frobeniusSeminormedAddCommGroup`. The explicit-function variants
    (`frobeniusNorm'`, `frobeniusNorm''`, `frobeniusNormRect`) use
    `Matrix.frobeniusNormedAddCommGroup`.
  - **L2 operator (spectral)**: `Matrix.instL2OpNormedAddCommGroup`, plus `instL2OpNormedSpace`,
    `instL2OpNormedRing`, `instL2OpNormedAlgebra`, `instL2OpMetricSpace`, and often
    `Matrix.instCStarRing`.
- **There is one global instance.** `Matrix.SpectralNorm.instCStarAlgebraMatrix :
  CStarAlgebra (Matrix n n ℂ)` in MatrixNormRelations.lean is not local.
  - Consequence: from that point on, and in SpectralNormGap, CoherenceCharacterization and
    TightBounds, square complex matrices have the L2 norm by default.
  - To get Frobenius there, use `attribute [local instance 1001]
    Matrix.frobeniusSeminormedAddCommGroup`, as the `EckartYoung` section of
    MatrixNormRelations does, or write the norm explicitly.
  - Rectangular matrices get no default norm from this project.
- **Mixed-norm statements spell both norms out:** `@Norm.norm _
  Matrix.instL2OpNormedAddCommGroup.toNorm A` and `@Norm.norm _
  Matrix.frobeniusSeminormedAddCommGroup.toNorm A`. Some sections define local notations
  `‖A‖₂` / `‖A‖_F` for these (SVD.lean, CoherenceCharacterization).
- **If a norm lemma "should" apply but doesn't**, suspect the wrong instance. Compare the
  instance in the goal (`set_option pp.explicit true`) with the one the lemma expects.

## Eigenvalue / singular-value indexing (invariant)

- Mathlib defines `hA.eigenvalues i = hA.eigenvalues₀ ((Fintype.equivOfCardEq
  (Fintype.card_fin _)).symm i)`. `eigenvalues₀ : Fin (card n) → ℝ` is antitone (index 0 is
  the largest); `eigenvalues : n → ℝ` is not sorted.
- `Matrix.SVD.Rectangular.eigenvaluesBijection α` is *defined* as `(Fintype.equivOfCardEq
  (Fintype.card_fin _)).symm`, exactly Mathlib's bijection. So the two indexings agree by
  `rfl`.
- **Never use `Fintype.equivFin` for eigenvalue indexing.** Equating two `Trunc.out` choices is
  unprovable.
- Square SVD: `singularValues A : n → ℝ` (unsorted) vs `singularValues₀ A : Fin (card n) → ℝ`
  (sorted, antitone). They are related by `Matrix.SVD.singularValues_eq_singularValues₀`.
  - Rectangular: `Matrix.SVD.Rectangular.singularValues A : Fin (min #m #n) → ℝ` (sorted).

## CI and merging

- `.github/workflows/lean.yml`, job `build`, runs:
  1. lean-action with the Mathlib cache;
  2. `lake build`;
  3. a fail on `declaration uses 'sorry'` in the log, or a grep hit in `src/**/*.lean`. The
     grep catches `axiom` at line start and the words `sorry`/`admit` **anywhere, comments
     included**;
  4. `python3 -I scripts/gen_index.py --check`, which runs even if the build failed.
- The `main` ruleset requires a PR, requires the status check `build`, and allows **rebase
  merges only**.
- `docs/INDEX.md` records line numbers, so almost every `.lean` edit needs it regenerated.
  Commit the regenerated file in the same PR.

## Conventions

- **File shape:** a `/- Copyright … Authors: … -/` header, then the imports, then a `/-! #
  Title … -/` module doc. Sections are introduced with `/-! ## … -/` and are named
  (`section Foo … end Foo`).
- **Doc comments:** give every new public declaration a `/-- … -/`. Headline results start with a
  bold title (`/-- **Eckart-Young Theorem (Spectral norm):** …`). The index uses the first
  sentence, so make it say what the result is.
- **Section variables:** to drop one that a declaration doesn't use, put `omit [Nonempty n] in`
  (or `omit [DecidableEq m] in`, …) on its own line *before* the doc comment. Some files use
  `set_option linter.unusedSectionVars false in` the same way.
- **Statements:** changing a theorem statement changes what is proved, so call it out in the PR.
  Proofs are written as structured `have` steps with short comments; match that.
- **Commit messages:** `<File or area>: <imperative summary>`, e.g. `TightBounds: fix
  injectivity argument in rank bound`.
- **Corruption history:** main once had duplicated `section` lines, truncated and duplicated
  comment openers (Lean block comments nest, so a stray `/-` silently comments out the rest of
  the file) and a bogus proof step. If you see odd duplicated lines, suspect this. The index
  script reports unterminated comments and mismatched `end`s.

## Source comments that overstate what is proved

Details are in the `docs/` notes.
- `Matrix.SVD.Rectangular.svd_decomposition_rectangular` does not constrain `S`, so as stated
  it is trivially true. The real content is `AV_eq_US_rectangular` with `singularDiagonal`.
- No rectangular Eckart–Young (optimality) theorem exists. TightBounds proves the rectangular
  spectral error formula and the rank bound only.
- SpectralNormGap's "tight for unit vectors" and its `Tightness` section prove only `≤`.
  Tightness is false in general (`R_inv (vec I₂ vec I₂ᵀ) = I₄`).
