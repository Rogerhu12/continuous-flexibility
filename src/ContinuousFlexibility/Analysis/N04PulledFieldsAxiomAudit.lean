import ContinuousFlexibility.Analysis.N04PulledFieldsColumnPhysical
import ContinuousFlexibility.Analysis.N04PulledFieldsCurrentData
import ContinuousFlexibility.Analysis.N04PulledFieldsStaticReference
import ContinuousFlexibility.Analysis.N04PulledFieldsReferenceCost
import ContinuousFlexibility.Analysis.N04PulledFieldsReferenceSplit
import ContinuousFlexibility.Analysis.N04PulledFieldsInverseJoint
import ContinuousFlexibility.Analysis.N04PulledFieldsCoefficientVariation
import ContinuousFlexibility.Analysis.N04PulledFieldsCoefficientMixedVariation
import ContinuousFlexibility.Analysis.N04PulledFieldsCoefficientRegularity
import Lean.Util.CollectAxioms

/-!
# Axiom audit of the PulledFields support modules

This target audits every declaration owned by the imported PulledFields
modules, including private helpers and all transitive dependencies. It is
independent of the open blueprint theorem: a passing support audit does
not assert that `N04RealizationPulledFields` has been proved.
-/

open Lean in
run_cmd do
  let env ← getEnv
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  for (name, info) in env.constants.toList do
    let own := match env.getModuleIdxFor? name with
      | some idx => env.allImportedModuleNames[idx.toNat]!.toString.startsWith
          "ContinuousFlexibility.Analysis.N04PulledFields"
      | none => false
    if own then
      declarations := declarations + 1
      match info with
      | .thmInfo _ => theorems := theorems + 1
      | .axiomInfo _ => throwError "PulledFields support declared an axiom: {name}"
      | _ => pure ()
      let axioms ← collectAxioms name
      for ax in axioms do
        unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
          throwError "Unexpected axiom {ax} in PulledFields support declaration {name}"
  if theorems == 0 then
    throwError "No PulledFields support theorem was audited"
  logInfo m!"PulledFields support axiom audit passed: {declarations} declarations, {theorems} theorems"

#print axioms ContinuousFlexibility.Analysis.n04PulledFieldsColumn_uniformHeight
#print axioms ContinuousFlexibility.Analysis.n04PulledFieldsCurrentData_of_positiveJets
#print axioms ContinuousFlexibility.Analysis.n04PulledFields_staticReference_currentJetDataOn
#print axioms ContinuousFlexibility.Analysis.n04PulledFields_geometry_rawSpatial
#print axioms ContinuousFlexibility.Analysis.n04PulledFields_inversePoint_jointDirections
#print axioms ContinuousFlexibility.Analysis.PulledFieldsReferenceRepair.currentObligation_of_referenceSplit
#print axioms ContinuousFlexibility.Analysis.n04PulledFields_hasDerivAt_radialCoefficient_mixedHeight
#print axioms ContinuousFlexibility.Analysis.n04PulledFields_correctedCoefficientMixedRegularity
