import CI2ZF
import CI2ZF.Appendix.CompletedRegions
import Lean.Util.CollectAxioms
import Lean.Elab.Command

open Lean Elab Command in
run_elab do
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let names := (← getEnv).constants.fold (init := #[]) fun acc name _ =>
    if (`CI2ZF).isPrefixOf name || (`PottsCI).isPrefixOf name then acc.push name else acc
  let mut used : Array Name := #[]
  for name in names do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Unapproved axiom {ax} in {name}"
      unless used.contains ax do
        used := used.push ax
  if names.isEmpty then throwError "No project declarations found"
  logInfo m!"Complete-library axiom audit passed: {names.size} declarations; allowed dependencies used: {used}"
