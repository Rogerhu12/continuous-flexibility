module

public import ContinuousFlexibility.Analysis.N04PulledFieldsColumnPhysical
public import ContinuousFlexibility.Analysis.N04PulledFieldsCurrentData
public import ContinuousFlexibility.Analysis.N04PulledFieldsStaticReference
public import ContinuousFlexibility.Analysis.N04PulledFieldsReferenceCost
public import ContinuousFlexibility.Analysis.N04PulledFieldsReferenceSplit
public import ContinuousFlexibility.Analysis.N04PulledFieldsInverseJoint
public import ContinuousFlexibility.Analysis.N04PulledFieldsCoefficientVariation
public import ContinuousFlexibility.Analysis.N04PulledFieldsCoefficientMixedVariation
public import ContinuousFlexibility.Analysis.N04PulledFieldsCoefficientRegularity
public import ContinuousFlexibility.Analysis.N04PulledFieldsSelectorFixedBase
public import ContinuousFlexibility.Analysis.N04PulledFieldsInverseSlotBounds
public import ContinuousFlexibility.Analysis.N04PulledFieldsSpatial
public import ContinuousFlexibility.Analysis.N04PulledFieldsColumnRegularity
public import ContinuousFlexibility.Analysis.N04PulledFieldsRawPrefix
public import ContinuousFlexibility.Analysis.N04PulledFieldsMaskedExpansion
public import ContinuousFlexibility.Analysis.N04PulledFieldsMaskedComposition
public import ContinuousFlexibility.Analysis.N04PulledFieldsInversePrefixPower
public import ContinuousFlexibility.Analysis.N04PulledFieldsInversePrefixSlots
public import ContinuousFlexibility.Analysis.N04PulledFieldsInverseRawFamily
public import ContinuousFlexibility.Analysis.N04PulledFieldsKernelJointFixedBase
public import ContinuousFlexibility.Analysis.N04PulledFieldsForwardFixedBase
public import ContinuousFlexibility.Analysis.N04PulledFieldsCompositionBudget
public import ContinuousFlexibility.Analysis.N04PulledFieldsMovingPointOneHigh
public import ContinuousFlexibility.Analysis.N04PulledFieldsCompositionCost
public import ContinuousFlexibility.Analysis.N04PulledFieldsSampleTransport
public import ContinuousFlexibility.Analysis.N04PulledFieldsInverseAffineBounds
public import ContinuousFlexibility.Analysis.N04PulledFieldsMovingFamily
public import ContinuousFlexibility.Analysis.N04PulledFieldsAuxiliaryReduction
public import ContinuousFlexibility.Analysis.N04PulledFieldsCoefficientJoint
public import ContinuousFlexibility.Analysis.N04PulledFieldsColumnCurrent
public import ContinuousFlexibility.Analysis.N04PulledFieldsAverageFixedBase
public import ContinuousFlexibility.Analysis.N04PulledFieldsInversePointData
public import ContinuousFlexibility.Analysis.N04PulledFieldsVelocityFixedBase
public import ContinuousFlexibility.Analysis.N04PulledFieldsJointExpansion
public import ContinuousFlexibility.Analysis.N04PulledFieldsPhysicalCurrent
public import ContinuousFlexibility.Analysis.N04PulledFieldsPhysicalPrefixPower
public import ContinuousFlexibility.Analysis.N04PulledFieldsSampledCoefficientCost
public import ContinuousFlexibility.Analysis.N04PulledFieldsReferenceCoefficients
public import ContinuousFlexibility.Analysis.N04PulledFieldsFixedBasePrefixRadius
public import ContinuousFlexibility.Analysis.N04PulledFieldsTransportParameterBudget
public import ContinuousFlexibility.Analysis.N04PulledFieldsFieldAssembly
public import ContinuousFlexibility.Analysis.N04PulledFieldsCoefficientCurrent
public import ContinuousFlexibility.Analysis.N04PulledFieldsPolynomialFixedBase
public import ContinuousFlexibility.Analysis.N04PulledFieldsCharacteristicPower
public import ContinuousFlexibility.Analysis.N04PulledFieldsCoefficientPhysicalAssembly
public import ContinuousFlexibility.Analysis.N04PulledFieldsActualDisplacementFixedBase
public import ContinuousFlexibility.Analysis.N04PulledFieldsStripAngularPower
public import ContinuousFlexibility.Analysis.N04PulledFieldsActualPolynomialGrowth
public import ContinuousFlexibility.Analysis.N04PulledFieldsActualVelocityMixedGrowth
public import ContinuousFlexibility.Analysis.N04PulledFieldsStripPhysicalCost
public import ContinuousFlexibility.Analysis.N04PulledFieldsActualErrorPhysical
public import ContinuousFlexibility.Analysis.N04PulledFieldsOriginalDifferencePhysical
public import ContinuousFlexibility.Blueprint.N04Coordinates.Realization.PulledFields
public import Lean.Util.CollectAxioms

/-!
# Axiom audit of the PulledFields support modules

This target audits every declaration owned by the imported PulledFields
modules, including private helpers and all transitive dependencies. It
also audits the actual blueprint theorem assembled from those proofs.
-/

@[expose] public section

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
  let target := ``ContinuousFlexibility.Blueprint.N04RealizationPulledFields
  let axioms ← collectAxioms target
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in PulledFields blueprint theorem"
  logInfo m!"PulledFields blueprint axiom audit passed: {target}"

#print axioms ContinuousFlexibility.Blueprint.N04RealizationPulledFields

#print axioms ContinuousFlexibility.Analysis.n04PulledFieldsColumn_uniformHeight
#print axioms ContinuousFlexibility.Analysis.n04PulledFieldsCurrentData_of_positiveJets
#print axioms ContinuousFlexibility.Analysis.n04PulledFields_staticReference_currentJetDataOn
#print axioms ContinuousFlexibility.Analysis.n04PulledFields_geometry_rawSpatial
#print axioms ContinuousFlexibility.Analysis.n04PulledFields_inversePoint_jointDirections
#print axioms ContinuousFlexibility.Analysis.PulledFieldsReferenceRepair.currentObligation_of_referenceSplit
#print axioms ContinuousFlexibility.Analysis.n04PulledFields_hasDerivAt_radialCoefficient_mixedHeight
#print axioms ContinuousFlexibility.Analysis.n04PulledFields_correctedCoefficientMixedRegularity
#print axioms ContinuousFlexibility.Statements.N01Properties.n04PulledFields_selectorInverseCircle_fixedBase_oneHigh
#print axioms ContinuousFlexibility.Analysis.n04PulledFields_doubleExpansion_pureSlots_bound
#print axioms ContinuousFlexibility.Analysis.n04PulledFields_coefficient_spatial
#print axioms ContinuousFlexibility.Analysis.n04PulledFieldsColumn_regularity
#print axioms ContinuousFlexibility.Analysis.n04PulledFields_differenceData_of_positiveJets
#print axioms ContinuousFlexibility.Analysis.n04PulledFields_currentData_rawPositive_prefix
#print axioms ContinuousFlexibility.Analysis.n04PulledFields_doubleExpansion_congr_stateBudget
#print axioms ContinuousFlexibility.Analysis.n04PulledFields_movingPoint_maskedMixedHeight_bound
#print axioms ContinuousFlexibility.Analysis.n04PulledFields_inversePrefix_power
#print axioms ContinuousFlexibility.Analysis.n04PulledFields_inversePrefix_pureWord
#print axioms ContinuousFlexibility.Analysis.n04PulledFields_currentData_rawFamily_pureWord
#print axioms ContinuousFlexibility.Analysis.n04PulledFields_coupledKernelJointJet_fixedBase
#print axioms ContinuousFlexibility.Statements.n04PulledFields_circleForward_fixedBase_oneHigh
#print axioms ContinuousFlexibility.Analysis.n04PulledFieldsCompositionLoss_maxHigh
#print axioms ContinuousFlexibility.Analysis.n04PulledFields_movingPoint_masked_positive_oneHigh
#print axioms ContinuousFlexibility.Analysis.n04PulledFields_movingPoint_materialOneHigh
#print axioms ContinuousFlexibility.Analysis.n04PulledFields_pulledPoint_sample_endpointX
#print axioms ContinuousFlexibility.Analysis.n04PulledFields_movingFamily_positiveJets
#print axioms ContinuousFlexibility.Analysis.n04PulledFields_obligation_of_fixedAuxiliary
#print axioms ContinuousFlexibility.Analysis.n04PulledFields_correctedCoefficientJointDirections
#print axioms ContinuousFlexibility.Analysis.n04PulledFieldsColumn_commonPhysicalData
#print axioms ContinuousFlexibility.Analysis.n04PulledFieldsColumn_currentData_of_inversePrefix
#print axioms ContinuousFlexibility.Statements.n04PulledFields_circleAverage_fixedBase_oneHigh
#print axioms ContinuousFlexibility.Analysis.n04PulledFields_inversePoint_neighborhood
#print axioms ContinuousFlexibility.Analysis.n04PulledFieldsColumn_currentData
#print axioms ContinuousFlexibility.Analysis.n04PulledFields_jointDirections_mixedExpansion
#print axioms ContinuousFlexibility.Analysis.n04PulledFields_physical_currentData
#print axioms ContinuousFlexibility.Analysis.n04PulledFields_physicalPrefix_of_oneHigh
#print axioms ContinuousFlexibility.Statements.N01Properties.n04PulledFields_actualVelocity_fixedBase_oneHigh
#print axioms ContinuousFlexibility.Analysis.n04PulledFields_correctedCoefficient_reference_uniform
#print axioms ContinuousFlexibility.Analysis.n04PulledFields_fieldData_of_coefficientData
#print axioms ContinuousFlexibility.Analysis.n04PulledFields_coefficient_currentData_of_sampledOneHigh
#print axioms ContinuousFlexibility.Analysis.n04PulledFields_fieldData_of_physicalDifference
#print axioms ContinuousFlexibility.Analysis.n04PulledFields_actualError_physicalOneHigh
#print axioms ContinuousFlexibility.Analysis.n04PulledFields_originalCoefficient_difference_physicalOneHigh
