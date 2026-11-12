import ContinuousFlexibility.Radial.InnerUnitWeights

/-!
# Unit-weight compatibility for the matched inner inverse

The existing module supplies the scalar restriction, boundary diagonal,
and general physical multiplier identities. Reusing those declarations
avoids duplicate names when the generated root imports both modules.
The matched construction retains its specialized supported-space API.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open MeasureTheory

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)

/-- The unit weight is the identity on the actual supported source space. -/
theorem innerSupportedWeightMultiplier_one_unit (s : Set α) (hs : MeasurableSet s)
    (bordered : Bool) :
    innerSupportedWeightMultiplier μ s hs bordered (fun _ => (1 : ℝ))
      measurable_const 1 (fun _ => by norm_num) =
        ContinuousLinearMap.id ℝ ↥(innerSupportedAdmissibleSource μ s bordered) := by
  exact innerSupportedWeightMultiplier_one μ s hs bordered
    measurable_const 1 (fun _ => by norm_num)

end ContinuousFlexibility.Radial
