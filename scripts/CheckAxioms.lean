/-
Copyright (c) 2026 FLYWHEEL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aleksandar Markovski
-/
import SVD
import KroneckerRearrangement
import CourantFischer
import TruncatedSVDRank1
import WeylInequality
import FrobeniusNorm
import MatrixNormRelations
import SpectralNormGap
import CoherenceCharacterization
import TightBounds
import FrobeniusUniqueness
import DavisKahan
import Wedin

/-!
# Axiom check

Run after `lake build`:

    lake env lean scripts/CheckAxioms.lean

It fails unless every declaration of the project libraries (the imports above) depends only on
Lean's standard axioms `propext`, `Classical.choice` and `Quot.sound`. That rules out `sorryAx`,
`Lean.ofReduceBool` (`native_decide`) and any `axiom` declared in the project, however the
source spells it.

This file is not a `module`, so Lean loads its imports in full, theorem proofs and private
declarations included, and `collectAxioms` also reads the axioms Lean recorded for each module
when it wrote the `.olean`. As a canary, some project declaration must use `Classical.choice`;
if none does, the scan is not seeing proofs.

`python3 -I scripts/gen_index.py --check` fails if a `src/*.lean` file is missing from the imports.
-/

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  -- The project modules: the direct imports, minus the implicit `Init`
  let imports := env.imports.filter (·.module != `Init)
  let projectMods := imports.filterMap fun i => (env.getModuleIdx? i.module).map (·.toNat)
  let mut checked : Nat := 0
  let mut used : NameSet := {}
  let mut bad : Array (Name × Array Name) := #[]
  for (name, idx) in env.const2ModIdx do
    unless projectMods.contains idx.toNat do continue
    let axs ← collectAxioms name
    checked := checked + 1
    used := axs.foldl NameSet.insert used
    let extra := axs.filter (!allowed.contains ·)
    unless extra.isEmpty do bad := bad.push (name, extra)
  if checked == 0 || projectMods.size != imports.size then
    throwError "found {checked} declarations in {projectMods.size} of {imports.size} imported modules"
  unless used.contains ``Classical.choice do
    throwError "no project declaration uses Classical.choice, so the scan is not seeing proofs"
  unless bad.isEmpty do
    let lines := (bad.qsort (·.1.lt ·.1)).toList.map fun (n, axs) => m!"{n}: {axs.toList}"
    throwError "{bad.size} declarations use non-standard axioms:\
      {indentD (MessageData.joinSep lines Format.line)}"
  logInfo m!"{checked} declarations in {projectMods.size} modules use only {allowed.toList}"
