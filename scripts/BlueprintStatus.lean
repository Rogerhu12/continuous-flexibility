import FlexibleSphereSolution
import Lean.Util.CollectAxioms

/-!
Prints, for every blueprint node, whether its proof still depends on `sorryAx`, and
the axioms of the Challenge theorem. Run with `lake env lean scripts/BlueprintStatus.lean`.
-/

open Lean in
run_cmd do
  let env ← getEnv
  let nodes := #["S01", "S02", "R01", "R02", "R03", "R04", "W01", "ScalarCalculus",
    "ScalarWeighted", "Tame", "Spaces", "R05a", "R05b", "R06a", "R06b", "R06c", "R07",
    "R08", "R09", "R10a", "R10b", "R11a", "R11b", "R12", "N01a", "N01b", "N01c", "N02N03",
    "N04Root", "N04Cubic", "N04Transmission", "N04a", "N04b", "N04Coordinates", "N05",
    "N06", "N07a", "N07b", "N08", "N09N10", "Solve", "N12"]
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

#print axioms ContinuousFlexibility.Blueprint.R06a

#print axioms ContinuousFlexibility.Blueprint.R07
