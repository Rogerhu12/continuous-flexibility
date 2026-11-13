import ContinuousFlexibility.Analysis.N04PulledFieldsCoefficientCurrent
import ContinuousFlexibility.Analysis.N04PulledFieldsReferenceCoefficients
import ContinuousFlexibility.Analysis.N04PulledFieldsPhysicalDifferenceCost
import ContinuousFlexibility.Analysis.N04PulledFieldsFieldAssembly

/-!
# Assembly from the actual physical coefficient difference estimates

The physical coefficient differences are transferred to the retained
samples, their actual reference is restored, and moving-point composition
gives the coefficient current data. The constructed two column families
then supply the remaining clauses on the common neighborhood.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements

/-- The physical coefficient difference estimate is the only remaining
quantitative input; all inverse, reference and column data are constructed
from the admissible gauge and the supplied geometry and reference jets. -/
theorem n04PulledFields_fieldData_of_physicalDifference
    (G : N04RealizationGauge) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    {base : ℕ} {ε : ℝ} (hadm : G.Admissible base ε)
    (hgeo : G.GeometryData η (fun _ => True) base ε) (href : G.ReferenceData η)
    (hphysical : N04PulledFieldsPhysicalDifferenceOneHigh G η base ε
      (G.coefficientField η) (n04PulledFields_coefficientMixedOn G η hadm)) :
    ∃ base' : ℕ, ∃ ε' : ℝ, base ≤ base' ∧ 0 < ε' ∧ ε' ≤ ε ∧
      G.FieldData η base' ε' := by
  apply n04PulledFields_fieldData_of_coefficientData G η hadm hgeo href
  apply n04PulledFields_coefficient_currentData_of_sampledOneHigh G η hadm hgeo href
  exact n04PulledFields_sampledOneHigh_of_physicalDifference G η hadm
    (G.coefficientField η) (n04PulledFields_coefficientMixedOn G η hadm) hphysical
    (n04PulledFields_gaugeCoefficient_reference_uniform G η)

end ContinuousFlexibility.Analysis
