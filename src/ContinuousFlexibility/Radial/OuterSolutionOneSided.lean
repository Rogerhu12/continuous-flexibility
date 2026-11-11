import ContinuousFlexibility.Radial.OuterEntranceVariation
import ContinuousFlexibility.Radial.OuterFirstOrderRegularity

/-!
# One-sided C¹ regularity of the full-source Green representative

The value and flux extend continuously to the regular entrance.  Their
relation uses the within-derivative there, so no extension of the source
or the solution across that entrance is required.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped ContDiff
open ContinuousFlexibility.Analysis

theorem outerSolution_oneSided_regular
    {a b lam cA cB : ℝ} {w U V f : ℝ → ℝ} (hab : a < b)
    (hw : ContinuousOn w (Ico a b))
    (hU : ContDiffOn ℝ 1 U (Ioo a b)) (hV : ContDiffOn ℝ 1 V (Ioo a b))
    (hUc : ContinuousOn U (Ico a b)) (hVc : ContinuousOn V (Ico a b))
    (hDU : ContinuousOn (deriv U) (Ico a b))
    (hDV : ContinuousOn (deriv V) (Ico a b))
    (hf : LocallyIntegrableOn f (Ioo a b))
    (hUi : ∀ x ∈ Ioo a b, IntervalIntegrable (fun t => U t * f t) volume a x)
    (hVi : ∀ x ∈ Ioo a b, IntervalIntegrable (fun t => V t * f t) volume a x) :
    ContDiffOn ℝ 1 (outerSolution lam cA cB a U V f) (Ico a b) ∧
      ContinuousOn (outerSolutionFlux lam cA cB a w U V f) (Ico a b) ∧
      (∀ x ∈ Ico a b, outerSolutionFlux lam cA cB a w U V f x =
        w x * derivWithin (outerSolution lam cA cB a U V f) (Ico a b) x) := by
  have hA : ContinuousOn (fun x => cA + ∫ t in a..x, U t * f t) (Ico a b) :=
    continuousOn_const.add (continuousOn_initialPrimitive hUi)
  have hB : ContinuousOn (fun x => cB - ∫ t in a..x, V t * f t) (Ico a b) :=
    continuousOn_const.sub (continuousOn_initialPrimitive hVi)
  have hvalue : ContinuousOn (outerSolution lam cA cB a U V f) (Ico a b) :=
    continuousOn_const.mul ((hVc.mul hA).add (hUc.mul hB))
  let d : ℝ → ℝ := fun x => -(1 / lam) *
    (deriv V x * (cA + ∫ t in a..x, U t * f t) +
      deriv U x * (cB - ∫ t in a..x, V t * f t))
  have hdc : ContinuousOn d (Ico a b) :=
    continuousOn_const.mul ((hDV.mul hA).add (hDU.mul hB))
  have hd : ∀ x ∈ Ico a b,
      HasDerivWithinAt (outerSolution lam cA cB a U V f) (d x) (Ico a b) x :=
    tail_hasDerivWithinAt_Ico_of_continuous hab hvalue hdc
      (hasDerivAt_outerSolution_from_left hU hV hf hUi hVi)
  refine ⟨(contDiffOn_one_iff_derivWithin (uniqueDiffOn_Ico a b)).mpr
    ⟨fun x hx => (hd x hx).differentiableWithinAt,
      hdc.congr (fun x hx => (hd x hx).derivWithin (uniqueDiffOn_Ico a b x hx))⟩,
    continuousOn_const.mul (((hw.mul hDV).mul hA).add ((hw.mul hDU).mul hB)), ?_⟩
  intro x hx
  rw [(hd x hx).derivWithin (uniqueDiffOn_Ico a b x hx)]
  dsimp only [outerSolutionFlux, d]
  ring

/-- A continuous weak derivative is the actual derivative at every
interior point of the same representative. -/
theorem hasDerivAt_of_continuous_interval_weakDerivative
    {a b : ℝ} {u g : ℝ → ℝ} (hab : a < b)
    (hu : ContinuousOn u (Ioo a b)) (hg : ContinuousOn g (Ioo a b))
    (hweak : HasIntervalWeakDerivative a b u g) :
    ∀ x ∈ Ioo a b, HasDerivAt u (g x) x := by
  obtain ⟨c, hc⟩ := nonempty_Ioo.mpr hab
  obtain ⟨k, v, _, hae, hd⟩ := exists_interval_classical_rep
    (hu.locallyIntegrableOn measurableSet_Ioo) hg hc hweak
  have hv : ContinuousOn v (Ioo a b) :=
    fun x hx => (hd x hx).continuousAt.continuousWithinAt
  have heq : EqOn u v (Ioo a b) := Measure.eqOn_Ioo_of_ae_eq hae hu hv
  intro x hx
  apply (hd x hx).congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
  exact heq hy

end ContinuousFlexibility.Radial
