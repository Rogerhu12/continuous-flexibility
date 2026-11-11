import ContinuousFlexibility.Radial.OuterWholeSource

/-!
# The same outer kernel as an entrance-based variation formula

The min/max kernel splits at the output point.  The right primitive is
the full natural pairing minus its initial primitive.  This identifies
the already constructed L² operator with a single continuous one-sided
representative for every L² source.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements

theorem outerGreenKernel_source_split (lam x y : ℝ) (U V f : ℝ → ℝ) :
    outerGreenKernel lam U V x y * f y =
      (Iic x).indicator (fun t => (V x / lam) * (U t * f t)) y +
        (Iic x)ᶜ.indicator (fun t => (U x / lam) * (V t * f t)) y := by
  by_cases hy : y ≤ x
  · have hys : y ∈ Iic x := hy
    rw [indicator_of_mem hys, indicator_of_notMem (notMem_compl_iff.mpr hys), add_zero,
      outerGreenKernel_symm, outerGreenKernel_of_le hy]
    ring
  · have hys : y ∉ Iic x := hy
    rw [indicator_of_notMem hys, indicator_of_mem (mem_compl hys), zero_add,
      outerGreenKernel_of_le (not_le.mp hy).le]
    ring

theorem outerGreen_integrable_mul {μ : Measure ℝ} {lam x : ℝ} {U V f : ℝ → ℝ}
    (hU : IntegrableOn (fun y => U y * f y) (Iic x) μ)
    (hV : Integrable (fun y => V y * f y) μ) :
    Integrable (fun y => outerGreenKernel lam U V x y * f y) μ := by
  have hA := IntegrableOn.integrable_indicator (s := Iic x)
    (hU.const_mul (V x / lam)) measurableSet_Iic
  have hB := IntegrableOn.integrable_indicator (s := (Iic x)ᶜ)
    ((hV.integrableOn (s := (Iic x)ᶜ)).const_mul (U x / lam)) measurableSet_Iic.compl
  apply (hA.add hB).congr
  exact Eventually.of_forall fun y => (outerGreenKernel_source_split lam x y U V f).symm

theorem outerGreen_integral_split {μ : Measure ℝ} {lam x : ℝ} {U V f : ℝ → ℝ}
    (hU : IntegrableOn (fun y => U y * f y) (Iic x) μ)
    (hV : Integrable (fun y => V y * f y) μ) :
    (∫ y, outerGreenKernel lam U V x y * f y ∂μ) =
      (V x / lam) * (∫ y in Iic x, U y * f y ∂μ) +
        (U x / lam) * ((∫ y, V y * f y ∂μ) - ∫ y in Iic x, V y * f y ∂μ) := by
  have hA := IntegrableOn.integrable_indicator (s := Iic x)
    (hU.const_mul (V x / lam)) measurableSet_Iic
  have hB := IntegrableOn.integrable_indicator (s := (Iic x)ᶜ)
    ((hV.integrableOn (s := (Iic x)ᶜ)).const_mul (U x / lam)) measurableSet_Iic.compl
  calc
    _ = ∫ y, (Iic x).indicator (fun t => (V x / lam) * (U t * f t)) y +
        (Iic x)ᶜ.indicator (fun t => (U x / lam) * (V t * f t)) y ∂μ :=
      integral_congr_ae (Eventually.of_forall fun y =>
        outerGreenKernel_source_split lam x y U V f)
    _ = _ := by
      rw [integral_add hA hB, integral_indicator measurableSet_Iic,
        integral_indicator measurableSet_Iic.compl, integral_const_mul,
        integral_const_mul, setIntegral_compl measurableSet_Iic hV]

/-- The actual physical kernel integral is the entrance-based formula,
including at the entrance.  The source needs only weighted L² membership. -/
theorem outerWholeGreen_integral_eq_solution {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {right : Bool} {entry lam : ℝ}
    (hentry : entry ∈ radialCore D) {U V : ℝ → ℝ}
    (hU : ContinuousOn U (Ico (outerOutwardRadius right entry)
      (outerOutwardRadius right (tailPhysicalEndpoint D right))))
    (hV : MemLp V 2 (outerWholeMeasure D right entry))
    (f : OuterWholeL2 D right entry) {x : ℝ}
    (hx : x ∈ Ico (outerOutwardRadius right entry)
      (outerOutwardRadius right (tailPhysicalEndpoint D right))) :
    (∫ y, outerGreenKernel lam U V x y * f y ∂outerWholeMeasure D right entry) =
      outerSolution lam 0 (-(∫ y, V y * f y ∂outerWholeMeasure D right entry))
        (outerOutwardRadius right entry) U V
        (fun y => -(outerWholeDensity D right y * f y)) x := by
  have hUi : IntegrableOn (fun y => U y * f y) (Iic x)
      (outerWholeMeasure D right entry) := by
    apply (outerWholeDensity_initial_integrable_iff hD hentry _ hx).mpr
    rcases eq_or_lt_of_le hx.1 with heq | hlt
    · subst x
      exact IntervalIntegrable.refl
    · have h := (outerWholeSource_initial_integrable hD hentry f hU x ⟨hlt, hx.2⟩).neg
      apply h.congr
      intro y _
      simp only [Pi.neg_apply]
      ring
  have hVi : Integrable (fun y => V y * f y) (outerWholeMeasure D right entry) :=
    hV.integrable_mul (Lp.memLp f)
  have hprimitive (W : ℝ → ℝ) :
      (∫ y in (outerOutwardRadius right entry)..x,
        W y * (-(outerWholeDensity D right y * f y))) =
      -(∫ y in (outerOutwardRadius right entry)..x,
        outerWholeDensity D right y * (W y * f y)) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro y _
    ring
  rw [outerGreen_integral_split hUi hVi,
    outerWholeDensity_initial_integral hD hentry _ hx,
    outerWholeDensity_initial_integral hD hentry _ hx,
    outerSolution, hprimitive U, hprimitive V]
  ring

end ContinuousFlexibility.Radial
