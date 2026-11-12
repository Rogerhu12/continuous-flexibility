import FlexibleSphereSolution
import ContinuousFlexibility.Analysis.SobolevExtension
import ContinuousFlexibility.Analysis.HadamardThreeLinesExtension
import ContinuousFlexibility.Radial.OuterUniformInverse
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
    "N06", "N07a", "N07b", "N08", "N09N10", "Solve", "N12",
    "N01cCoefficients", "N01cSpeeds", "N01cFlows"]
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
  -- Strictly close all four N01c declarations; other nodes retain the status audit above.
  let strictNodes := #["N01cCoefficients", "N01cSpeeds", "N01cFlows", "N01c"]
  for n in strictNodes do
    let name := (`ContinuousFlexibility.Blueprint).str n
    unless env.contains name do
      throwError "missing required N01c declaration {name}"
    let axioms ← collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "N01c axiom gate failed: {name} depends on {ax}"
  logInfo m!"N01c axiom gate passed: {strictNodes}"

#print axioms ContinuousFlexibility.Blueprint.R06a
#print axioms ContinuousFlexibility.Blueprint.N01cCoefficients
#print axioms ContinuousFlexibility.Blueprint.N01cSpeeds
#print axioms ContinuousFlexibility.Blueprint.N01cFlows
#print axioms ContinuousFlexibility.Blueprint.N01c
#print axioms ContinuousFlexibility.Blueprint.ScalarWeighted

-- The external-input tool has no blueprint node: audit its actual endpoints.
#print axioms ContinuousFlexibility.Analysis.exists_halfLineSobolevExtension
#print axioms ContinuousFlexibility.Analysis.exists_intervalSobolevExtension
#print axioms ContinuousFlexibility.Analysis.SobolevExtensionOperator.completion_rightInverse
#print axioms ContinuousFlexibility.Analysis.SobolevExtensionOperator.completion_compatible
#print axioms ContinuousFlexibility.Analysis.hadamard_threeLines_operator_norm_unit
#print axioms ContinuousFlexibility.Analysis.hadamardThreeLinesExtension_spec_unit
#print axioms ContinuousFlexibility.Blueprint.R07
#print axioms ContinuousFlexibility.Blueprint.R08
#print axioms ContinuousFlexibility.Blueprint.R12
#print axioms ContinuousFlexibility.Blueprint.R10b
#print axioms ContinuousFlexibility.Blueprint.N01b
#print axioms ContinuousFlexibility.Blueprint.R11b
#print axioms ContinuousFlexibility.Blueprint.N04a

-- Tool-R10a-Outer: actual inverse, ordinary compact sources, and the refuted global bound.
#print axioms ContinuousFlexibility.Radial.exists_uniform_morseOuterInverse_fixed_parameters
#print axioms ContinuousFlexibility.Radial.OuterPhysicalRobinInverse.assertions
#print axioms ContinuousFlexibility.Radial.OuterPhysicalRobinInverse.ordinary_jacobi_source
#print axioms ContinuousFlexibility.Radial.accumulatingProfile_no_unweighted_outer_inverse
