import FlexibleSphereSolution
import Lean.Util.CollectAxioms

/-!
Prints, for every blueprint node, whether its proof still depends on `sorryAx`, and
the axioms of the Challenge theorem. Run with `lake env lean scripts/BlueprintStatus.lean`.
-/

open Lean in
run_cmd do
  let env ← getEnv
  let nodes := #["S01", "S02", "R01", "S03", "S04", "S05", "R02", "R03", "R04", "R05", "R06",
    "R07", "R08", "R09", "R10", "R11", "R12", "W01", "H01", "W02", "W03", "N01", "N02", "N03",
    "N04", "N05", "N06", "H02", "N07", "N08", "N09", "N10", "H03", "N11", "N12"]
  let mut proved : Array String := #[]
  let mut openNodes : Array String := #[]
  for n in nodes do
    let name := (`ContinuousFlexibility.Blueprint).str n
    unless env.contains name do
      throwError "missing blueprint node {name}"
    let axioms ← collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound || ax == ``sorryAx do
        throwError "Unexpected axiom {ax} in {name}"
    if axioms.contains ``sorryAx then openNodes := openNodes.push n else proved := proved.push n
  logInfo m!"blueprint statements proved / total: {proved.size} / {nodes.size}"
  logInfo m!"proved: {proved}"
  logInfo m!"open: {openNodes}"
  let endpoint ← collectAxioms `FlexibleSphere.exists_closedBending
  logInfo m!"axioms of FlexibleSphere.exists_closedBending: {endpoint}"
