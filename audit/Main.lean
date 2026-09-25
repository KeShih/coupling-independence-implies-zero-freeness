import ZeroFreeness.Potts.Main
import ZeroFreeness.LeeYang
import ZeroFreeness.Holant
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-!
Audit every declaration in the two project namespaces, including transitive
dependencies. This file supplies no declarations to the proof library.
-/

open Lean Elab Command in
run_elab do
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let names := (← getEnv).constants.fold (init := #[]) fun acc name _ =>
    if (`ZeroFreeness).isPrefixOf name || (`PottsCI).isPrefixOf name then acc.push name else acc
  let mut used : Array Name := #[]
  for name in names do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Unapproved axiom {ax} in {name}"
      unless used.contains ax do
        used := used.push ax
  if names.isEmpty then throwError "No project declarations found"
  logInfo m!"Axiom audit passed: {names.size} declarations; allowed dependencies used: {used}"
