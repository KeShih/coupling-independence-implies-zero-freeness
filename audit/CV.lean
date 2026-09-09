import CI2ZF.Potts.Regions.CV
import Lean.Util.CollectAxioms
import Lean.Elab.Command

open Lean Elab Command in
run_elab do
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let names := (← getEnv).constants.fold (init := #[]) fun acc name _ =>
    if (`CI2ZF.Appendix.CV).isPrefixOf name then acc.push name else acc
  for name in names do
    for ax in (← Lean.collectAxioms name) do
      unless allowed.contains ax do
        throwError "Unapproved axiom {ax} in {name}"
  if names.isEmpty then throwError "No CV declarations found"
  logInfo m!"CV axiom audit passed: {names.size} declarations, transitive dependencies checked"
