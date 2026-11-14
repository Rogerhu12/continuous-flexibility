module

public import ContinuousFlexibility.Radial.OuterPhysicalRobinSolution

/-!
# The actual endpoint Green bracket vanishes

The bracket against the same normalized natural solution is the remaining
natural source integral.  Its endpoint limit is zero for every weighted
L² source, by integrability of that actual pairing.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

theorem outerSolutionFlux_bracket {lam cA cB a x : ℝ} {w U V f : ℝ → ℝ}
    (hlam : lam ≠ 0) (hW : radialWronskian w U V x = -lam) :
    outerSolution lam cA cB a U V f x * (w x * deriv V x) -
      outerSolutionFlux lam cA cB a w U V f x * V x =
        cB - ∫ t in a..x, V t * f t := by
  calc
    _ = -(1 / lam) * radialWronskian w U V x *
        (cB - ∫ t in a..x, V t * f t) := by
      unfold outerSolution outerSolutionFlux radialWronskian
      ring
    _ = _ := by rw [hW]; field_simp [hlam]

theorem outerPhysicalGreenFlux_eq_deriv
    {D : ReferenceData} (hD : IsAccumulatingProfile D)
    {right : Bool} {entry c lam J : ℝ} (hentry : entry ∈ radialCore D)
    (hlam : lam ≠ 0) {P ZP Q ZQ : ℝ → ℝ}
    (H : OuterFundamentalStatePair
      (fun x => lam / outerTailOutwardWeight D right x)
      (fun x => J * deriv (outerTailOutwardWeight D right) x / (lam * x))
      P ZP Q ZQ (outerOutwardRadius right entry) c
      (outerOutwardRadius right (tailPhysicalEndpoint D right)))
    (f : OuterWholeL2 D right entry) :
    ∀ x ∈ Ioo (outerOutwardRadius right entry)
        (outerOutwardRadius right (tailPhysicalEndpoint D right)),
      outerPhysicalGreenFlux D right entry lam H.U H.V f x =
        outerTailOutwardWeight D right x *
          deriv (outerPhysicalGreenValue D right entry lam H.U H.V f) x := by
  let a := outerOutwardRadius right entry
  let b := outerOutwardRadius right (tailPhysicalEndpoint D right)
  have hcoeff := outerWhole_coefficients_smooth (right := right) (J := J)
    (matchingProfileGeometry hD) hentry hlam
  have hU : ContDiffOn ℝ 1 H.U (Ioo a b) :=
    (((H.U_system.contDiffOn (uniqueDiffOn_Ico a b) hcoeff.1 hcoeff.2).1).of_le
      (by simp)).mono Ioo_subset_Ico_self
  have hV : ContDiffOn ℝ 1 H.V (Ioo a b) :=
    (((H.V_system.contDiffOn (uniqueDiffOn_Ico a b) hcoeff.1 hcoeff.2).1).of_le
      (by simp)).mono Ioo_subset_Ico_self
  exact outerSolutionFlux_eq_from_left hU hV
    (outerWholeSource_integrable hD hentry f).locallyIntegrableOn
    (outerWholeSource_initial_integrable hD hentry f H.U_system.continuousOn.1)
    (outerWholeSource_initial_integrable hD hentry f H.V_system.continuousOn.1)

/-- The true value/flux bracket tends to zero at the singular endpoint. -/
theorem outerPhysicalGreen_endpoint_bracket
    {D : ReferenceData} (hD : IsAccumulatingProfile D)
    {right : Bool} {entry c lam J : ℝ} (hentry : entry ∈ radialCore D)
    (hlam : lam ≠ 0) {P ZP Q ZQ : ℝ → ℝ}
    (H : OuterFundamentalStatePair
      (fun x => lam / outerTailOutwardWeight D right x)
      (fun x => J * deriv (outerTailOutwardWeight D right) x / (lam * x))
      P ZP Q ZQ (outerOutwardRadius right entry) c
      (outerOutwardRadius right (tailPhysicalEndpoint D right)))
    (hV : MemLp H.V 2 (outerWholeMeasure D right entry))
    (f : OuterWholeL2 D right entry) :
    Tendsto (fun x =>
      outerPhysicalGreenValue D right entry lam H.U H.V f x *
          (outerTailOutwardWeight D right x * deriv H.V x) -
        outerTailOutwardWeight D right x *
          deriv (outerPhysicalGreenValue D right entry lam H.U H.V f) x * H.V x)
      (𝓝[<] (outerOutwardRadius right (tailPhysicalEndpoint D right))) (𝓝 0) := by
  let a := outerOutwardRadius right entry
  let b := outerOutwardRadius right (tailPhysicalEndpoint D right)
  let g : ℝ → ℝ := fun x => outerWholeDensity D right x * (H.V x * f x)
  let total : ℝ := ∫ x, H.V x * f x ∂outerWholeMeasure D right entry
  have hab : a < b := outerWhole_interval hentry
  have hi : IntervalIntegrable g volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).mpr
      ((outerWholeDensity_integrable_iff hD hentry _).mp
        (hV.integrable_mul (Lp.memLp f)))
  have ht : total = ∫ x in a..b, g x := outerWholeDensity_integral hD hentry _
  have hc : ContinuousOn (fun x => ∫ t in a..x, g t) (Icc a b) := by
    simpa only [uIcc_of_le hab.le] using
      (hi.absolutelyContinuousOnInterval_intervalIntegral (c := a) (by simp)).continuousOn
  have hb := hc b ⟨hab.le, le_rfl⟩
  rw [ContinuousWithinAt, nhdsWithin_Icc_eq_nhdsLE hab] at hb
  have hp : Tendsto (fun x => ∫ t in a..x, g t) (𝓝[<] b)
      (𝓝 (∫ t in a..b, g t)) :=
    hb.mono_left (nhdsWithin_mono b Iio_subset_Iic_self)
  have hlim : Tendsto (fun x => -total + ∫ t in a..x, g t) (𝓝[<] b) (𝓝 0) := by
    have hh : Tendsto (fun x => -total + ∫ t in a..x, g t) (𝓝[<] b)
        (𝓝 (-total + ∫ t in a..b, g t)) := tendsto_const_nhds.add hp
    simpa only [← ht, neg_add_cancel] using hh
  apply hlim.congr'
  filter_upwards [Ioo_mem_nhdsLT hab] with x hx
  have hwne : ∀ y ∈ Ico a b, outerTailOutwardWeight D right y ≠ 0 :=
    fun y hy => (outerWhole_weight_pos (matchingProfileGeometry hD) hentry hy).ne'
  have hW := H.radialWronskian hwne x (Ioo_subset_Ico_self hx)
  have hprimitive :
      (∫ t in a..x, H.V t * (-(outerWholeDensity D right t * f t))) =
        -(∫ t in a..x, g t) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only [g]
    ring
  rw [← outerPhysicalGreenFlux_eq_deriv hD hentry hlam H f x hx,
    outerPhysicalGreenValue, outerPhysicalGreenFlux,
    outerSolutionFlux_bracket hlam hW]
  change -total + (∫ t in a..x, g t) =
    -total - ∫ t in a..x, H.V t * (-(outerWholeDensity D right t * f t))
  rw [hprimitive]
  ring

end ContinuousFlexibility.Radial
