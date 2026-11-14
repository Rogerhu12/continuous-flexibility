module

public import ContinuousFlexibility.Radial.OuterGreenSplit
public import ContinuousFlexibility.Radial.OuterRobinWeakGraph

/-!
# The actual physical Green solution and its Robin trace

For every source in the physical outer Hilbert space, the same min/max
kernel gives a C¹ one-sided representative.  Its conormal flux satisfies
the original Jacobi equation weakly, its normalized Robin trace vanishes,
and the complementary trace is the natural L² pairing divided by λ.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped ContDiff
open ContinuousFlexibility.Statements ContinuousFlexibility.Analysis

def outerPhysicalGreenValue (D : ReferenceData) (right : Bool) (entry lam : ℝ)
    (U V : ℝ → ℝ) (f : OuterWholeL2 D right entry) : ℝ → ℝ :=
  outerSolution lam 0 (-(∫ y, V y * f y ∂outerWholeMeasure D right entry))
    (outerOutwardRadius right entry) U V (fun y => -(outerWholeDensity D right y * f y))

def outerPhysicalGreenFlux (D : ReferenceData) (right : Bool) (entry lam : ℝ)
    (U V : ℝ → ℝ) (f : OuterWholeL2 D right entry) : ℝ → ℝ :=
  outerSolutionFlux lam 0 (-(∫ y, V y * f y ∂outerWholeMeasure D right entry))
    (outerOutwardRadius right entry) (outerTailOutwardWeight D right) U V
    (fun y => -(outerWholeDensity D right y * f y))

theorem outerPhysicalGreenValue_ae {D : ReferenceData} (hD : IsAccumulatingProfile D)
    {right : Bool} {entry lam : ℝ} (hentry : entry ∈ radialCore D) {U V : ℝ → ℝ}
    (hU : ContinuousOn U (Ico (outerOutwardRadius right entry)
      (outerOutwardRadius right (tailPhysicalEndpoint D right))))
    (hV : MemLp V 2 (outerWholeMeasure D right entry))
    (R : OuterWholeL2 D right entry →L[ℝ] OuterWholeL2 D right entry)
    (hR : ∀ f, (R f : ℝ → ℝ) =ᵐ[outerWholeMeasure D right entry]
      fun x => ∫ y, outerGreenKernel lam U V x y * f y ∂outerWholeMeasure D right entry)
    (f : OuterWholeL2 D right entry) :
    (R f : ℝ → ℝ) =ᵐ[outerWholeMeasure D right entry]
      outerPhysicalGreenValue D right entry lam U V f := by
  filter_upwards [hR f, outerWholeMeasure_ae_mem hentry] with x hx hxi
  exact hx.trans (outerWholeGreen_integral_eq_solution hD hentry hU hV f
    (Ioo_subset_Ico_self hxi))

/-- The canonical full-source representative belongs to the actual weak
Robin graph and has the manuscript's complementary entrance trace. -/
theorem outerPhysicalGreenValue_graph_and_trace
    {D : ReferenceData} (hD : IsAccumulatingProfile D)
    {right : Bool} {entry c lam J : ℝ} (hentry : entry ∈ radialCore D)
    (hlam : lam ≠ 0) {P ZP Q ZQ : ℝ → ℝ}
    (H : OuterFundamentalStatePair
      (fun x => lam / outerTailOutwardWeight D right x)
      (fun x => J * deriv (outerTailOutwardWeight D right) x / (lam * x))
      P ZP Q ZQ (outerOutwardRadius right entry) c
      (outerOutwardRadius right (tailPhysicalEndpoint D right)))
    (hV : MemLp H.V 2 (outerWholeMeasure D right entry))
    (R : OuterWholeL2 D right entry →L[ℝ] OuterWholeL2 D right entry)
    (hR : ∀ f, (R f : ℝ → ℝ) =ᵐ[outerWholeMeasure D right entry]
      fun x => ∫ y, outerGreenKernel lam H.U H.V x y * f y ∂outerWholeMeasure D right entry)
    (f : OuterWholeL2 D right entry) :
    let a := outerOutwardRadius right entry
    let b := outerOutwardRadius right (tailPhysicalEndpoint D right)
    let u := outerPhysicalGreenValue D right entry lam H.U H.V f
    OuterRobinWeakGraph (outerWholeMeasure D right entry) a b J lam
        (outerTailOutwardWeight D right) (outerWholeDensity D right) H.entrance (R f) f ∧
      ContDiffOn ℝ 1 u (Ico a b) ∧
      outerStatePair (outerStatePerp H.entrance)
        (u a, outerTailOutwardWeight D right a * derivWithin u (Ico a b) a / lam) =
          (∫ y, H.V y * f y ∂outerWholeMeasure D right entry) / lam := by
  let a := outerOutwardRadius right entry
  let b := outerOutwardRadius right (tailPhysicalEndpoint D right)
  let w := outerTailOutwardWeight D right
  let source : ℝ → ℝ := fun x => -(outerWholeDensity D right x * f x)
  let cb : ℝ := -(∫ y, H.V y * f y ∂outerWholeMeasure D right entry)
  let u := outerSolution lam 0 cb a H.U H.V source
  let q := outerSolutionFlux lam 0 cb a w H.U H.V source
  have hab : a < b := outerWhole_interval hentry
  have ha : a ∈ Ico a b := ⟨le_rfl, hab⟩
  have hw : ContDiff ℝ ∞ w := outerWhole_weight_smooth (matchingProfileGeometry hD) right
  have hwne : ∀ x ∈ Ico a b, w x ≠ 0 :=
    fun x hx => (outerWhole_weight_pos (matchingProfileGeometry hD) hentry hx).ne'
  have hxne : ∀ x ∈ Ico a b, x ≠ 0 :=
    fun x hx => outerWhole_coordinate_ne_zero (matchingProfileGeometry hD) hentry hx
  have hcoeff := outerWhole_coefficients_smooth (right := right) (J := J)
    (matchingProfileGeometry hD) hentry hlam
  have hUc := H.U_system.continuousOn.1
  have hVc := H.V_system.continuousOn.1
  have hDU := (H.U_system.continuousOn_deriv
    hcoeff.1.continuousOn hcoeff.2.continuousOn).1
  have hDV := (H.V_system.continuousOn_deriv
    hcoeff.1.continuousOn hcoeff.2.continuousOn).1
  have hUs := (H.U_system.contDiffOn (uniqueDiffOn_Ico a b) hcoeff.1 hcoeff.2).1
  have hVs := (H.V_system.contDiffOn (uniqueDiffOn_Ico a b) hcoeff.1 hcoeff.2).1
  have hU₂ : ContDiffOn ℝ 2 H.U (Ioo a b) :=
    (hUs.of_le (by simp)).mono Ioo_subset_Ico_self
  have hV₂ : ContDiffOn ℝ 2 H.V (Ioo a b) :=
    (hVs.of_le (by simp)).mono Ioo_subset_Ico_self
  have hU₁ := hU₂.of_le (show (1 : ℕ∞ω) ≤ 2 by norm_num)
  have hV₁ := hV₂.of_le (show (1 : ℕ∞ω) ≤ 2 by norm_num)
  have hf : LocallyIntegrableOn source (Ioo a b) :=
    (outerWholeSource_integrable hD hentry f).locallyIntegrableOn
  have hUi := outerWholeSource_initial_integrable hD hentry f hUc
  have hVi := outerWholeSource_initial_integrable hD hentry f hVc
  have hreg := outerSolution_oneSided_regular (lam := lam) (cA := 0) (cB := cb) hab
    hw.continuous.continuousOn hU₁ hV₁ hUc hVc hDU hDV hf hUi hVi
  have hUeq : ∀ x ∈ Ioo a b, radialJacobi J w H.U x = 0 :=
    outerFirstOrderSystem_radialJacobi isOpen_Ioo hlam
      (fun x hx => H.U_system x (Ioo_subset_Ico_self hx))
      (fun x hx => hwne x (Ioo_subset_Ico_self hx))
      (fun x hx => hxne x (Ioo_subset_Ico_self hx))
  have hVeq : ∀ x ∈ Ioo a b, radialJacobi J w H.V x = 0 :=
    outerFirstOrderSystem_radialJacobi isOpen_Ioo hlam
      (fun x hx => H.V_system x (Ioo_subset_Ico_self hx))
      (fun x hx => hwne x (Ioo_subset_Ico_self hx))
      (fun x hx => hxne x (Ioo_subset_Ico_self hx))
  have hW : ∀ x ∈ Ioo a b, radialWronskian w H.U H.V x = -lam :=
    fun x hx => H.radialWronskian hwne x (Ioo_subset_Ico_self hx)
  have hweak := outerSolutionFlux_weakDerivative_from_left (cA := 0) (cB := cb)
    hab (hw.of_le (by simp)).contDiffOn hU₂ hV₂ hUeq hVeq hW hlam hf hUi hVi
  have hstate : outerFluxState lam w H.U a = outerStatePerp H.entrance :=
    ((H.flux_states hlam hwne a ha).1).trans H.U_initial
  have htraces := outerSolution_entrance_traces (cB := cb) hab H.unit
    hU₁ hV₁ hUc hVc hDU hDV hf hUi hVi hstate
  change OuterRobinWeakGraph (outerWholeMeasure D right entry) a b J lam w
      (outerWholeDensity D right) H.entrance (R f) f ∧
    ContDiffOn ℝ 1 u (Ico a b) ∧
    outerStatePair (outerStatePerp H.entrance)
      (u a, w a * derivWithin u (Ico a b) a / lam) =
        (∫ y, H.V y * f y ∂outerWholeMeasure D right entry) / lam
  refine ⟨⟨u, q, outerPhysicalGreenValue_ae hD hentry hUc hV R hR f,
    hreg.1, hreg.2.1, hreg.2.2, ?_, ?_⟩, hreg.1, ?_⟩
  · simpa only [sub_eq_add_neg] using hweak
  · change outerStatePair H.entrance (u a, q a / lam) = 0
    have hqa : q a = w a * derivWithin u (Ico a b) a := hreg.2.2 a ha
    rw [hqa]
    exact htraces.1
  · simpa only [cb, neg_div, neg_neg] using htraces.2

end ContinuousFlexibility.Radial
