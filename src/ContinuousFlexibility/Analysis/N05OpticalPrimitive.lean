module

public import ContinuousFlexibility.Analysis.OpticalTravelVariation
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The actual optical primitive in the physical core

The optical speed is continuous throughout the open radial core, including
the roots of the radial derivative.  Its ordinary interval integral is a
genuine differentiable primitive there.  No regularity at the outer
physical endpoints is used.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped Topology ContDiff

theorem n05_opticalSpeed_continuousOn_core
    {D : ReferenceData} (hD : IsAccumulatingProfile D) :
    ContinuousOn (opticalSpeed D.w) (radialCore D) := by
  obtain ⟨B, hB⟩ := hD
  have hw : ContDiff ℝ ∞ D.w := hB.1.2.2.1.1
  have hden : ∀ r ∈ radialCore D, r * D.w r ≠ 0 := by
    intro r hr
    exact mul_ne_zero (hB.1.1.trans hr.1).ne' (hB.1.2.2.2.2.1 r hr).ne'
  exact Real.continuous_sqrt.comp_continuousOn
    (((hw.continuous_deriv (by simp)).neg.continuousOn).div
      (continuous_id.mul hw.continuous).continuousOn hden)

/-- The ordinary optical travel integral has the actual optical speed as
its derivative at every physical core point. -/
theorem n05_opticalTravel_hasDerivAt_core
    {D : ReferenceData} (hD : IsAccumulatingProfile D)
    {l r : ℝ} (hl : l ∈ radialCore D) (hr : r ∈ radialCore D) :
    HasDerivAt (opticalTravel D.w l) (opticalSpeed D.w r) r := by
  have hf := n05_opticalSpeed_continuousOn_core hD
  have hsub : uIcc l r ⊆ radialCore D := by
    intro t ht
    exact ⟨(lt_min hl.1 hr.1).trans_le ht.1,
      ht.2.trans_lt (max_lt hl.2 hr.2)⟩
  exact intervalIntegral.integral_hasDerivAt_right (hf.mono hsub).intervalIntegrable
    (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo hf r hr)
    (hf.continuousAt (isOpen_Ioo.mem_nhds hr))

theorem n05_opticalTravel_continuousOn_core
    {D : ReferenceData} (hD : IsAccumulatingProfile D)
    {l : ℝ} (hl : l ∈ radialCore D) :
    ContinuousOn (opticalTravel D.w l) (radialCore D) := fun r hr =>
  (n05_opticalTravel_hasDerivAt_core hD hl hr).continuousAt.continuousWithinAt

end ContinuousFlexibility.Statements
