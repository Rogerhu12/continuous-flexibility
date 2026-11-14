module

public import ContinuousFlexibility.Statements.Milestones
public import Lean.Util.CollectAxioms
public import Lean.Compiler.Old

/-!
This audit checks actual declaration ownership, including private helpers and
generated structure declarations. It rejects project axioms, unsafe code,
handwritten partial definitions, and any axiom outside Lean's three standard
logical axioms. Lean's partial runtime auxiliary of a checked recursive
definition is identified separately; its axioms are still checked.
It also checks that all 58 milestone declarations have the closed type Prop.
Passing this audit does not construct a proof of any milestone proposition.
-/

@[expose] public section

open Lean in
run_cmd do
  let env ← getEnv
  let expected : List Name := [
    `ContinuousFlexibility.Statements.C00Statement,
    `ContinuousFlexibility.Statements.S01Statement,
    `ContinuousFlexibility.Statements.S02Statement,
    `ContinuousFlexibility.Statements.R01Statement,
    `ContinuousFlexibility.Statements.S03Statement,
    `ContinuousFlexibility.Statements.S04Statement,
    `ContinuousFlexibility.Statements.S05Statement,
    `ContinuousFlexibility.Statements.R02Statement,
    `ContinuousFlexibility.Statements.R03Statement,
    `ContinuousFlexibility.Statements.R04Statement,
    `ContinuousFlexibility.Statements.R05Statement,
    `ContinuousFlexibility.Statements.R06Statement,
    `ContinuousFlexibility.Statements.R07Statement,
    `ContinuousFlexibility.Statements.R08Statement,
    `ContinuousFlexibility.Statements.R09Statement,
    `ContinuousFlexibility.Statements.R10Statement,
    `ContinuousFlexibility.Statements.R11Statement,
    `ContinuousFlexibility.Statements.R12Statement,
    `ContinuousFlexibility.Statements.W01Statement,
    `ContinuousFlexibility.Statements.H01Statement,
    `ContinuousFlexibility.Statements.W02Statement,
    `ContinuousFlexibility.Statements.W03Statement,
    `ContinuousFlexibility.Statements.N01Statement,
    `ContinuousFlexibility.Statements.N02Statement,
    `ContinuousFlexibility.Statements.N03Statement,
    `ContinuousFlexibility.Statements.N04Statement,
    `ContinuousFlexibility.Statements.N05Statement,
    `ContinuousFlexibility.Statements.N06Statement,
    `ContinuousFlexibility.Statements.H02Statement,
    `ContinuousFlexibility.Statements.N07Statement,
    `ContinuousFlexibility.Statements.N08Statement,
    `ContinuousFlexibility.Statements.N09Statement,
    `ContinuousFlexibility.Statements.N10Statement,
    `ContinuousFlexibility.Statements.H03Statement,
    `ContinuousFlexibility.Statements.N11Statement,
    `ContinuousFlexibility.Statements.N12Statement,
    `ContinuousFlexibility.Statements.D01Statement,
    `ContinuousFlexibility.Statements.D02Statement,
    `ContinuousFlexibility.Statements.G01Statement,
    `ContinuousFlexibility.Statements.G02Statement,
    `ContinuousFlexibility.Statements.G03Statement,
    `ContinuousFlexibility.Statements.G04Statement,
    `ContinuousFlexibility.Statements.G05Statement,
    `ContinuousFlexibility.Statements.G06Statement,
    `ContinuousFlexibility.Statements.G07Statement,
    `ContinuousFlexibility.Statements.G08Statement,
    `ContinuousFlexibility.Statements.G09Statement,
    `ContinuousFlexibility.Statements.G10Statement,
    `ContinuousFlexibility.Statements.G11Statement,
    `ContinuousFlexibility.Statements.G12Statement,
    `ContinuousFlexibility.Statements.G13Statement,
    `ContinuousFlexibility.Statements.G14Statement,
    `ContinuousFlexibility.Statements.G15Statement,
    `ContinuousFlexibility.Statements.G16Statement,
    `ContinuousFlexibility.Statements.MAINStatement,
    `ContinuousFlexibility.Statements.X01Statement,
    `ContinuousFlexibility.Statements.X02Statement,
    `ContinuousFlexibility.Statements.X03Statement]
  if expected.length != 58 || expected.eraseDups.length != 58 then
    throwError "The milestone target list must contain 58 distinct names"
  for name in expected do
    let some info := env.find? name
      | throwError "Missing milestone target {name}"
    unless info.type == mkSort Level.zero do
      throwError "Milestone {name} is not a closed Prop: {info.type}"
    match info with
    | .defnInfo _ => pure ()
    | .opaqueInfo _ => throwError "Opaque target {name} hides its mathematical statement"
    | .axiomInfo _ => throwError "Target {name} is an axiom"
    | _ => throwError "Milestone {name} must define its explicit proposition"
  let mut projectDeclarations : Nat := 0
  let mut targetDeclarations : Nat := 0
  let mut targetTheorems : Nat := 0
  let mut compilerRecursions : Nat := 0
  let mut observed : List Name := []
  for (name, info) in env.constants.toList do
    let owner := match env.getModuleIdxFor? name with
      | some idx => env.allImportedModuleNames[idx.toNat]!
      | none => env.mainModule
    let projectOwner := (`ContinuousFlexibility).isPrefixOf owner
    if projectOwner then
      projectDeclarations := projectDeclarations + 1
      if info.isUnsafe then
        throwError "Unsafe project declaration: {name}"
      if info.isPartial then
        let some parent := Compiler.isUnsafeRecName? name
          | throwError "Partial project declaration: {name}"
        let some (.defnInfo checked) := env.find? parent
          | throwError "Recursive runtime auxiliary has no checked definition: {name}"
        unless checked.safety == .safe && info.type == checked.type &&
            env.getModuleIdxFor? name == env.getModuleIdxFor? parent do
          throwError "Recursive runtime auxiliary has an invalid checked definition: {name}"
        compilerRecursions := compilerRecursions + 1
      match info with
      | .axiomInfo _ => throwError "Project axiom declared: {name}"
      | _ => pure ()
      if (`ContinuousFlexibility.Statements).isPrefixOf owner then
        targetDeclarations := targetDeclarations + 1
        match info with
        | .thmInfo _ => targetTheorems := targetTheorems + 1
        | _ => pure ()
      let axioms ← collectAxioms name
      for ax in axioms do
        unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
          throwError "Unexpected axiom {ax} in {name}"
        unless observed.contains ax do
          observed := ax :: observed
  if targetDeclarations == 0 || projectDeclarations == 0 then
    throwError "The declaration audit would be empty"
  logInfo m!"STATEMENT_AUDIT|milestones=58|target_declarations={targetDeclarations}|target_generated_theorems={targetTheorems}|project_declarations={projectDeclarations}|axioms={observed}"
  logInfo m!"STATEMENT_COMPILER_RECURSION|{compilerRecursions}"
  let projectModules := env.mainModule ::
    env.allImportedModuleNames.toList.filter (fun n => (`ContinuousFlexibility).isPrefixOf n)
  let moduleNames := String.intercalate "," (projectModules.map (fun n => n.toString))
  logInfo m!"STATEMENT_IMPORTS|{moduleNames}"
  logInfo "All 58 targets are explicit closed propositions; no target existence proof is asserted."

