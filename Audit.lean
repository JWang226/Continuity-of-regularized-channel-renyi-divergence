/-
Copyright (c) 2026 Jinzhao Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzhao Wang (AI-assisted formalization)
-/

import QuantumChannelContinuity
import Lean.Util.CollectAxioms

/-!
Audit every project declaration, including private helpers and definitions
containing proof fields. `collectAxioms` follows transitive imported proof
dependencies. Explicit theorem premises are not axioms; they remain visible
in the theorem statements and in README.md.
-/

open Lean Elab Command

#check QuantumChannelContinuity.theorem_one
#print axioms QuantumChannelContinuity.theorem_one
#print axioms QuantumChannelContinuity.blockRenyi_tendsto_regularized
#print axioms QuantumChannelContinuity.blockRelative_tendsto_regularized

run_cmd do
  let env ← getEnv
  let names := env.constants.fold (init := #[]) fun acc name _ =>
    let s := name.toString
    if s.startsWith "ChannelContinuity." || s.startsWith "QuantumChannelContinuity." ||
        s.startsWith "_private.ChannelContinuity." ||
        s.startsWith "_private.QuantumChannelContinuity." || s.startsWith "Sion." then
      acc.push name
    else acc
  let (_, auditState) := ((names.forM Lean.CollectAxioms.collect).run env).run {}
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := auditState.axioms.filter (fun a => !allowed.contains a)
  unless unexpected.isEmpty do
    throwError "Unexpected axioms in project dependency closure: {unexpected}"
  let theoremNames := names.filter fun name =>
    (env.find? name).any (fun c => match c with | .thmInfo _ => true | _ => false)
  for name in theoremNames do
    logInfo m!"Checked theorem: {name}"
  logInfo m!"AUDIT PASSED: {names.size} project declarations, {theoremNames.size} theorems; transitive axioms {auditState.axioms}."
