import ContinuousFlexibility.Analysis.N07aAngularPeriodMeasure
import ContinuousFlexibility.Radial.ReferenceCosineParseval

/-!
# The full physical angular mean from a genuine half-period pairing

The physical weak graph uses the normalized full `2π` mean. For a genuine
`π`-periodic integrable function this is exactly `π⁻¹` times the canonical
half-period integral. Integrability is established before Fubini is used.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements ContinuousFlexibility.Radial

theorem n07a_integrable_fullPeriod_of_half {μ : Measure ℝ} [SFinite μ]
    {f : PolarPoint → ℝ} (hf : Integrable f (μ.prod angleMeasure))
    (hp : ∀ᵐ r ∂μ, Function.Periodic (fun θ => f (r, θ)) Real.pi) :
    Integrable f (μ.prod (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))) := by
  have hpres : MeasurePreserving (fun p : PolarPoint => (p.1, p.2 - Real.pi))
      (μ.prod (volume.restrict (Ioc Real.pi (2 * Real.pi)))) (μ.prod angleMeasure) :=
    (MeasurePreserving.id μ).prod n07aAngularHalfShift_preserving
  have hshift := hpres.integrable_comp_of_integrable hf
  have he : (f ∘ (fun p : PolarPoint => (p.1, p.2 - Real.pi))) =ᵐ[
      μ.prod (volume.restrict (Ioc Real.pi (2 * Real.pi)))] f := by
    filter_upwards [(Measure.quasiMeasurePreserving_fst
      (μ := μ) (ν := volume.restrict (Ioc Real.pi (2 * Real.pi)))).ae hp] with p hpr
    exact hpr.sub_eq p.2
  have hf₂ := (integrable_congr he).mp hshift
  have hsum : μ.prod (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))) =
      μ.prod angleMeasure + μ.prod (volume.restrict (Ioc Real.pi (2 * Real.pi))) := by
    rw [← Ioc_union_Ioc_eq_Ioc Real.pi_pos.le (show Real.pi ≤ 2 * Real.pi by linarith [Real.pi_pos]),
      Measure.restrict_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc,
      Measure.prod_add]
    rfl
  rw [hsum]
  exact hf.add_measure hf₂

theorem n07a_periodic_radial_mean_eq_half {a b : ℝ} (hab : a ≤ b)
    {f : PolarPoint → ℝ}
    (hf : Integrable f ((volume.restrict (Ioo a b)).prod angleMeasure))
    (hp : ∀ᵐ r ∂volume.restrict (Ioo a b), Function.Periodic (fun θ => f (r, θ)) Real.pi) :
    (∫ r in a..b, radialAngularMean (fun θ => f (r, θ))) =
      Real.pi⁻¹ * ∫ p, f p ∂((volume.restrict (Ioo a b)).prod angleMeasure) := by
  have hfull := n07a_integrable_fullPeriod_of_half hf hp
  have he : (fun r => radialAngularMean (fun θ => f (r, θ))) =ᵐ[
      volume.restrict (Ioo a b)]
      fun r => Real.pi⁻¹ * ∫ θ, f (r, θ) ∂angleMeasure := by
    filter_upwards [hp, hfull.prod_right_ae] with r hpr hri
    have hir : IntervalIntegrable (fun θ => f (r, θ)) volume 0 (2 * Real.pi) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)).mpr hri
    rw [radialAngularMean_eq_halfPeriod hpr hir,
      intervalIntegral.integral_of_le Real.pi_pos.le]
    rfl
  rw [intervalIntegral.integral_of_le hab, ← restrict_Ioo_eq_restrict_Ioc]
  rw [integral_congr_ae he, integral_const_mul, ← integral_prod _ hf]

end ContinuousFlexibility.Analysis
