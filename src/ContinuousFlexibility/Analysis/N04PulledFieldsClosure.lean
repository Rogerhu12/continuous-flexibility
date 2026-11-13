import ContinuousFlexibility.Analysis.N04PulledFieldsCoefficientPhysicalDifference
import ContinuousFlexibility.Analysis.N04PulledFieldsCoefficientPhysicalAssembly
import ContinuousFlexibility.Analysis.N04PulledFieldsAuxiliaryReduction

/-!
# Closing the pulled-field obligation

The retained physical coefficient difference estimates, the constructed
column estimates, and the actual inverse-chart data give all five fields
at a fixed same-atlas reference witness. Auxiliary independence then
puts the common neighborhood before every auxiliary column, as required
by the shared obligation used in the unchanged parent assembly.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

/-- The actual five fields satisfy the current interface at every fixed
same-atlas reference witness, with no additional quantitative premise. -/
theorem n04PulledFields_fixedAuxiliary
    (G : N04RealizationGauge) (base : ℕ) (ε : ℝ) (hadm : G.Admissible base ε)
    (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    (href : G.ReferenceData η) (hgeo : G.GeometryData η (fun _ => True) base ε) :
    ∃ base' : ℕ, ∃ ε' : ℝ, base ≤ base' ∧ 0 < ε' ∧ ε' ≤ ε ∧
      G.FieldData η base' ε' :=
  n04PulledFields_fieldData_of_physicalDifference G η hadm hgeo href
    (n04PulledFields_coefficient_physicalDifference G η hadm)

/-- The shared pulled-field obligation, with its original common
neighborhood quantifiers and the parent's retained reference premise. -/
theorem n04PulledFields_obligation : N04RealizationPulledFieldObligation :=
  n04PulledFields_obligation_of_fixedAuxiliary n04PulledFields_fixedAuxiliary

end ContinuousFlexibility.Analysis
