import ContinuousFlexibility.Analysis.CanonicalSourceMeasure

/-!
# Angular boundary lines inside an arbitrary physical domain

Replacing the half-open angular period by the open period removes a null
line even when the physical domain is not a radial product. No regularity
or measurability assumption on the intersected domain is needed.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory

/-- The angular boundary is null after intersection with any physical set. -/
theorem polarDomain_Ioc_ae_eq_Ioo (Ω : Set PolarPoint) (a b : ℝ) :
    (Ω ∩ (univ ×ˢ Ioc a b)) =ᵐ[volume]
      (Ω ∩ (univ ×ˢ Ioo a b)) := by
  have hstrip : (univ ×ˢ Ioc a b : Set PolarPoint) =ᵐ[volume]
      (univ ×ˢ Ioo a b) :=
    Measure.set_prod_ae_eq Filter.EventuallyEq.rfl Ioo_ae_eq_Ioc.symm
  filter_upwards [hstrip] with p hp
  change (p ∈ Ω ∧ p ∈ (univ ×ˢ Ioc a b : Set PolarPoint)) =
    (p ∈ Ω ∧ p ∈ (univ ×ˢ Ioo a b : Set PolarPoint))
  exact congrArg (fun P : Prop => p ∈ Ω ∧ P) hp

end ContinuousFlexibility.Analysis
