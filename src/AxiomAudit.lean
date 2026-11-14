module

public import ContinuousFlexibility
public import Lean.Util.CollectAxioms

/-!
# Axiom audit of project theorems

The audit rejects `sorryAx` and every axiom other than Lean's usual
`propext`, `Classical.choice`, and `Quot.sound`. It examines all imported
declarations owned by project modules, including private helper declarations,
as well as declarations in the project namespace and transitive dependencies.
-/

@[expose] public section

open Lean in
run_cmd do
  let env ← getEnv
  let mut checked : Nat := 0
  let mut declarations : Nat := 0
  for (name, info) in env.constants.toList do
    let projectOwner := match env.getModuleIdxFor? name with
      | some idx => (`ContinuousFlexibility).isPrefixOf env.allImportedModuleNames[idx.toNat]!
      | none => false
    if (`ContinuousFlexibility).isPrefixOf name || projectOwner then
      declarations := declarations + 1
      match info with
      | .thmInfo _ => checked := checked + 1
      | .axiomInfo _ => throwError "Project axiom declared: {name}"
      | _ => pure ()
      let axioms ← collectAxioms name
      for ax in axioms do
        unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
          throwError "Unexpected axiom {ax} in {name}"
  if checked == 0 then
    throwError "No project theorems were found; the audit would be vacuous"
  logInfo m!"Axiom audit passed for {declarations} project declarations ({checked} theorems)"
