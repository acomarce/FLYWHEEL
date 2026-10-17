# FLYWHEEL: notes for Claude

FLYWHEEL is a Lean 4 + Mathlib formalization of matrix analysis: SVD, Courant–Fischer, Weyl and
Thompson interlacing, Eckart–Young, Kronecker (Van Loan–Pitsianis) approximation and coherence.
There are no `sorry`/`axiom`/`admit`, and it must stay that way.

## Layout

- Lake project at the repo root:
  - `lakefile.toml` sets `srcDir = "src"`.
  - `lean-toolchain` pins `leanprover/lean4:v4.35.0`.
  - `lakefile.toml` (`rev`) and `lake-manifest.json` (`rev`, `inputRev`) pin Mathlib at
    commit `ccbef15e…`.
- All Lean sources are flat in `src/`. Each file is its own `lean_lib` of the same name (module
  `SVD` = `src/SVD.lean`). Every file is a Lean module (see "Module system" below).
- To add a file: give it the module header (see Conventions), add a `[[lean_lib]]`, put it in
  `defaultTargets` and import it in `scripts/CheckAxioms.lean`. The index check fails otherwise.
- `docs/INDEX.md`: every top-level declaration with full name, kind, `file:line` and a doc
  summary. It is generated, so **grep it** to find a lemma instead of reading the sources.
- `docs/svd.md`, `docs/eckart-young.md`, `docs/kronecker.md`, `docs/davis-kahan.md`: proof
  architecture notes and known traps.
- `scripts/gen_index.py`: generates and checks the index. `scripts/CheckAxioms.lean`: the CI
  axiom check (imports every library). `.claude/hooks/session-start.sh`: cloud-session setup.

## Build

```bash
lake exe cache get          # prebuilt Mathlib oleans; needed once
lake build                  # builds all 12 libraries (defaultTargets lists them all)
lake build TightBounds      # one library plus its imports
lake env lean src/SVD.lean  # elaborate a single file
lake env lean scripts/CheckAxioms.lean  # after a build: only propext, Classical.choice, Quot.sound
python3 -I scripts/gen_index.py   # regenerate docs/INDEX.md after editing any .lean file
```

- Mathlib is pinned by commit, so `lake update` does not move it. Still don't run it in a cloud
  session: Mathlib's post-update hook runs `lake exe cache get`, which stalls on the blocked
  cache hosts (set `MATHLIB_NO_CACHE_ON_UPDATE=1` to skip it).
- To bump Mathlib: set `rev` in `lakefile.toml` to the new commit and `lean-toolchain` to
  Mathlib's at that commit, then `lake update mathlib` (or edit `lake-manifest.json` by hand, as
  the v4.35 bump did; keep `rev` and `inputRev` equal to the lakefile's `rev`, or Lake warns
  "manifest out of date").
- The build is warning-free and CI keeps it so: it runs `lake build --wfail`.

### Cloud sessions (claude.ai/code)

- The network policy blocks the Mathlib cache hosts (`cache.mathlib.org`, which `lake exe cache
  get` reads from, and the Azure account behind it, `lakecache.blob.core.windows.net`) and
  `releases.lean-lang.org`.
- The SessionStart hook installs elan and the pinned toolchain from GitHub release assets, then
  clones Mathlib. It runs `lake exe cache get` only if a cache host answers, and otherwise
  prints a warning.
- Without the cache, `lake build` and `lake env lean` compile Mathlib from source, which takes
  hours. **Don't.** Instead:
  - Grep `.lake/packages/mathlib/Mathlib` for Mathlib API names.
  - Run `python3 -I scripts/gen_index.py --check` (fast; catches lakefile and comment/scope
    damage and a missing `module` header).
  - Push and read the CI job log (GitHub MCP `get_job_logs`). A run takes about 4 minutes.
    Pushes to a branch without a PR do not start CI; start it with the GitHub MCP
    `actions_run_trigger` (`run_workflow`, workflow `lean.yml`, `ref` = the branch).
- If the owner adds `cache.mathlib.org` to the environment's allowed domains, local builds work.
- Manual toolchain install, if the hook didn't run:
  - Download `lean-4.35.0-linux.tar.zst` from the `leanprover/lean4` GitHub release.
  - Decompress it with `zstd`, or with python `zstandard` if `zstd` is missing.
  - Extract it to `~/.elan/toolchains/leanprover--lean4---v4.35.0`.

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
FrobeniusUniqueness           ← TightBounds
DavisKahan                    ← CoherenceCharacterization
```

`CourantFischer` and `WeylInequality` do `public import Mathlib`, so every file downstream of
them sees all of Mathlib. SVD, KroneckerRearrangement and TruncatedSVDRank1 import specific
modules and see less (next section).

## Module system

Every file starts with `module` and uses `public import` for all its imports. Lean then applies
visibility rules that non-module files never had:

- **Import closure.** A module loads only the *public*-import closure of its imports. When a
  Mathlib file does a plain `import X`, X is not loaded for us. So a lemma, tactic, instance or
  simp lemma can be missing in SVD, KroneckerRearrangement or TruncatedSVDRank1 even though their
  imports reached it before the conversion. Import its module directly.
- **Exposure.** Downstream proofs can unfold a definition (`unfold`, `simp [f]`, `rfl`, defeq in
  `exact`) only if its body is exposed. Files that define something open `@[expose] public
  section`, so all project definitions are exposed. A Mathlib `def` is exposed if it is an
  `abbrev`, carries `@[expose]`, or sits in an `@[expose] public section`. Otherwise it is opaque
  here: use its API lemmas.
- **Private declarations** cannot appear in a public statement (including a `let` in the
  statement) or in an exposed definition body. They are fine inside proofs. This is why
  `Matrix.SVD.Real.transpose_mul_self_isHermitian'` is public.
- Theorem proofs are always private, so a proof may use `private` lemmas.

## Namespace map

Namespaces do not match file names. Always look a name up in `docs/INDEX.md`.

| File | Namespaces |
|---|---|
| SVD | `Matrix.SVD` (square), `Matrix.SVD.Real`, `Matrix.SVD.Rectangular`, two `Matrix.SpectralNorm` Hermitian-norm lemmas, and root (see below) |
| KroneckerRearrangement | `Matrix.KroneckerRearrangement` (`vec`, `R`, `R_inv`, `outerProduct`) |
| CourantFischer | top-level `CourantFischer` (not `Matrix.*`) |
| TruncatedSVDRank1 | root (no namespace) |
| WeylInequality | `Matrix.WeylInequality` (Weyl, Thompson interlacing) |
| FrobeniusNorm | `Matrix.FrobeniusNorm` (includes `eckart_young_frobenius`) |
| MatrixNormRelations | `Matrix.SVD` (square spectral Eckart–Young and its non-uniqueness counterexample), `Matrix.SpectralNorm`, `Matrix.KroneckerRearrangement`, `Matrix.KroneckerPerturbation`, root `Finset.sup'_prod_eq_mul_sup'` |
| SpectralNormGap | `Matrix.Kronecker.SpectralBounds` (‖·‖₂ vs ‖·‖_F through R⁻¹) |
| CoherenceCharacterization | `Matrix.Coherence` |
| TightBounds | `Matrix.TightBounds` (rectangular `truncatedSVD_rect`, rectangular Eckart–Young, Van Loan–Pitsianis `kroneckerApprox`) |
| FrobeniusUniqueness | `Matrix.FrobeniusUniqueness` (uniqueness of the Frobenius-optimal truncation under a gap: square, rectangular, `kroneckerApprox`) |
| DavisKahan | `Matrix.DavisKahan` (sin θ for the top eigenvector, Frobenius sin Θ for top-k eigenspaces, Gram-matrix corollaries for the top right singular vector) |

Traps:
- **Square vs rectangular Eckart–Young.** The square theorems are
  `Matrix.FrobeniusNorm.eckart_young_frobenius` and `Matrix.SVD.eckart_young_spectral`; the
  rectangular ones are `Matrix.TightBounds.eckart_young_frobenius_rect` and
  `eckart_young_spectral_rect`. `Matrix.SVD.Rectangular` (SVD.lean only) holds the rectangular
  SVD itself.
- **SVD.lean has root-namespace sections.** `FrobeniusNormRectangular` and
  `SpectralNormRectangular` declare fully qualified `Matrix.SVD.Rectangular.*` names (their
  private helpers stay at root). `SpectralNormRectangular` also declares
  `Matrix.SpectralNorm.l2_opNorm_hermitian_eq_sup_abs_eigenvalues` (used by MatrixNormRelations).
  `RectangularCoherenceFactor` is genuinely root: `coherenceFactorRect`, `frobeniusNormRect`, ….
  The order lemma `Finset.sup'_sq_eq_sq_sup'` is in the real `Finset` namespace.
- **Nothing opens `Matrix.SVD.Rectangular`.** Downstream files spell names fully, e.g.
  `Matrix.SVD.Rectangular.singularValues` in WeylInequality and TightBounds.

## Norms: check which one is active before touching any `‖·‖`

- Mathlib has no default norm on `Matrix`. Files switch one on per section with
  `attribute [local instance] …`:
  - **Frobenius**: `Matrix.frobeniusSeminormedAddCommGroup`. The explicit-function variants
    (`frobeniusNorm'`, `frobeniusNormRect`) use
    `Matrix.frobeniusNormedAddCommGroup`.
  - **L2 operator (spectral)**: `Matrix.instL2OpNormedAddCommGroup`, plus `instL2OpNormedSpace`,
    `instL2OpNormedRing`, `instL2OpNormedAlgebra`, `instL2OpMetricSpace`, and often
    `Matrix.instCStarRing`.
- **There is one global instance.** `Matrix.SpectralNorm.instCStarAlgebraMatrix :
  CStarAlgebra (Matrix n n ℂ)` in MatrixNormRelations.lean is not local.
  - Consequence: from that point on, and in SpectralNormGap, CoherenceCharacterization,
    TightBounds, FrobeniusUniqueness and DavisKahan, square complex matrices have the L2 norm by
    default.
  - To get Frobenius there, write the norm explicitly (next bullet) or use an explicit function
    such as `frobeniusNorm'`. No code here relies on overriding the global instance with
    `attribute [local instance 1001] Matrix.frobeniusSeminormedAddCommGroup`, so that route is
    untested.
  - Rectangular matrices get no default norm from this project.
- **Mixed-norm statements spell both norms out:** `@Norm.norm _
  Matrix.instL2OpNormedAddCommGroup.toNorm A` and `@Norm.norm _
  Matrix.frobeniusSeminormedAddCommGroup.toNorm A`. Some sections define local notations
  `‖A‖₂` / `‖A‖_F` for these (SVD.lean, CoherenceCharacterization, the `Square` section of
  FrobeniusUniqueness).
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
  2. `lake build --wfail`, which fails on any warning;
  3. a fail on `declaration uses 'sorry'` in the log, or a grep hit in `src/**/*.lean`. The
     grep catches `axiom` at line start and the words `sorry`/`admit` **anywhere, comments
     included**;
  4. `lake env lean scripts/CheckAxioms.lean`: every declaration of the 12 libraries may
     depend only on `propext`, `Classical.choice` and `Quot.sound`. This also catches what the
     grep cannot, such as `private axiom` or `native_decide` (`Lean.ofReduceBool`);
  5. `python3 -I scripts/gen_index.py --check`, which runs even if the build failed. It also
     fails if `scripts/CheckAxioms.lean` does not import exactly the `src/` modules.
- The `main` ruleset requires a PR, requires the status check `build`, and allows **rebase
  merges only**.
- `docs/INDEX.md` records line numbers, so almost every `.lean` edit needs it regenerated.
  Commit the regenerated file in the same PR.

## Conventions

- **File shape:** a `/- Copyright … Authors: … -/` header, `module`, the `public import`s, a
  `/-! # Title … -/` module doc, then `@[expose] public section`. Use plain `public section` if
  the file defines nothing. This file-level section stays open at end of file, as in Mathlib.
  Inner sections are introduced with `/-! ## … -/` and are named (`section Foo … end Foo`).
- **Doc comments:** give every new public declaration a `/-- … -/`. Headline results start with a
  bold title (`/-- **Eckart-Young Theorem (Spectral norm):** …`). The index uses the first
  sentence, so make it say what the result is.
- **Section variables:** to drop one that a declaration doesn't use, put `omit [Nonempty n] in`
  (or `omit [DecidableEq m] in`, …) on its own line *before* the doc comment. Some files use
  `set_option linter.unusedSectionVars false in` the same way.
  - `omit [T] in` drops *every* section variable whose type is `T`. Never declare the same
    instance twice in one scope; `omit` would then remove both copies.
  - Sections that re-declare `variable {n : Type*} …` shadow the outer `n`, so `omit` and the
    linter then refer to the inner `n`.
- **Statements:** changing a theorem statement changes what is proved, so call it out in the PR.
  Proofs are written as structured `have` steps with short comments; match that.
- **Commit messages:** `<File or area>: <imperative summary>`, e.g. `TightBounds: fix
  injectivity argument in rank bound`.
- **Proof-writing traps** (met while writing FrobeniusUniqueness and DavisKahan):
  - `λ` is a keyword, so it cannot appear in identifiers (`hλ` does not parse).
  - `have h := foo (fun x => …) …` keeps beta-redexes like `(fun x => …) a` in the type of `h`,
    and a later `rw … at h` cannot see through them. Give `h` its type explicitly.
  - `simp only [Matrix.mul_assoc, h]` re-associates products inside the goal but not in `h`'s
    left side. If `h` mentions a composite like `W * D * star W`, first name it with
    `obtain ⟨Q, hQ⟩ : ∃ Q, Q = W * D * star W := ⟨_, rfl⟩`.
  - A defensive `<;> rfl` after a `simp` that already closes the goal is a linter warning.
  - `@[deprecated]` sits on the line above the declaration, so grep Mathlib and the toolchain's
    `Init` with `-B1` (e.g. `Fin.lt_iff_val_lt_val` is deprecated for `Fin.lt_def`). A deprecated
    name only warns.
- **Toolchain traps** (met moving from Lean v4.26 / Mathlib dc19f2a to v4.35 / ccbef15):
  - `if_pos`/`if_neg`/`dif_pos`/`dif_neg` are deprecated in core: use `ite_eq_left`/`ite_eq_right`/
    `dite_eq_left`/`dite_eq_right` (same arguments). `push_neg` is deprecated: use `push Not`.
  - Renamed Mathlib API: `Set.mem_setOf_eq` → `Set.mem_ofPred_eq`, `Set.restrict` →
    `Set.domRestrict`, `Fin.coe_castLE` → `Fin.val_castLE`, `List.Sorted` → `List.Pairwise` /
    `SortedGE` (`Antitone.sortedGE_ofFn`), `isHermitian_iff_isSymmetric` →
    `isSymmetric_toEuclideanLin_iff` (direction flipped). `Matrix.toEuclideanLin` is now an abbrev
    for `Matrix.toLpLin 2 2`, so rewrite with `Matrix.toLpLin_apply`. `spectralRadius` is a
    supremum over the quasispectrum; use `spectralRadius_eq_of_unital` to get the spectrum.
  - Defeq checks respect transparency more strictly. `convert … using k` may leave goals it
    used to close, e.g. `k = ⟨↑k_succ - 1, _⟩` through a `let`, or `0 = ⟨0, _⟩`; finish them
    with `Fin.ext (by simp [k_succ])`. `simpa using h` closes at reducible transparency
    (`simpa using! h` is the old behaviour). `simp [norm_nonneg]` may not fire on an explicitly
    instanced norm: use `@norm_nonneg _ inst _`. `unfold f` on the goal leaves hypotheses that
    mention `f` ill-typed against it; rewrite without unfolding.
  - Linters: `haveI` on a Prop goal must be `have`; a `def` of class type needs
    `@[instance_reducible]`; a computable `def` that uses `Complex.instRCLike` needs
    `noncomputable`.
- **Corruption history:** main once had duplicated `section` lines, truncated and duplicated
  comment openers (Lean block comments nest, so a stray `/-` silently comments out the rest of
  the file) and a bogus proof step. If you see odd duplicated lines, suspect this. The index
  script reports unterminated comments and mismatched `end`s.

## Known gaps

Details are in the `docs/` notes.
- Uniqueness is proved only in the Frobenius norm, and only under a gap σₖ₋₁ > σₖ (0-indexed):
  `Matrix.FrobeniusUniqueness.eckart_young_frobenius_unique` (square),
  `eckart_young_frobenius_rect_unique` and `kroneckerApprox_unique` (σ₀(R C) > σ₁(R C)). When
  σₖ₋₁ = σₖ > 0 the optimum is not unique; no counterexample for that is formalized. The case
  σₖ₋₁ = σₖ = 0 (rank A < k, where B = A is forced) is excluded by the hypothesis but not
  stated separately. The Kronecker factors A, B are not unique (scaling); only A ⊗ B is.
- Spectral norm: optima are not unique, shown by one counterexample
  (`Matrix.SVD.spectral_best_rank_one_not_unique`, A = diag(2, 1), k = 1). No characterization of
  all spectral optima.
- Subspace perturbation (`Matrix.DavisKahan`): the top eigenvector (`davis_kahan_top`), the
  top-k eigenspace in Frobenius form with a factor k (`davis_kahan_sin_theta`), and, through the
  Gram matrix, the top right singular vector of a square matrix
  (`top_right_singular_vector_perturbation`,
  `top_right_singular_vector_perturbation_of_spectralGap`). Not formalized: the
  operator-norm sin Θ for k > 1, and Wedin's theorem (gap σₖ₋₁ - σₖ, ‖E‖₂ directly, left and
  right singular subspaces, rectangular matrices).
