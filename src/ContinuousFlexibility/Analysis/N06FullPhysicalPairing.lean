import ContinuousFlexibility.Analysis.N06HalfPhysicalPairing

/-!
# Full physical tests from the two actual half-period pairings

Only the represented physical field is periodic. The function paired
against it may be the actual current differential operator applied to an
arbitrary full-period test, and need not be half-periodic. Integrability
on the first half and of its translated second half suffices for the
full physical weak pairing. No periodicity of the corrected coefficients
is assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory

set_option backward.isDefEq.respectTransparency false

theorem n06_intervalIntegrable_full_pairing
    {u φ : ℝ → ℝ} (hu : Function.Periodic u Real.pi)
    (hfirst : IntervalIntegrable (fun θ => u θ * φ θ) volume 0 Real.pi)
    (hshift : IntervalIntegrable (fun θ => u θ * φ (θ + Real.pi)) volume 0 Real.pi) :
    IntervalIntegrable (fun θ => u θ * φ θ) volume 0 (2 * Real.pi) := by
  have htranslated : IntervalIntegrable (fun θ => u (θ + Real.pi) * φ (θ + Real.pi))
      volume 0 Real.pi := by
    have hu' : ∀ θ, u (θ + Real.pi) = u θ := hu
    simpa only [hu'] using hshift
  have hsecond : IntervalIntegrable (fun θ => u θ * φ θ)
      volume Real.pi (2 * Real.pi) := by
    simpa only [zero_add, show Real.pi + Real.pi = 2 * Real.pi by ring] using
      (IntervalIntegrable.comp_add_right_iff
        (f := fun θ => u θ * φ θ) (a := 0) (b := Real.pi) (c := Real.pi)).mp htranslated
  exact hfirst.trans hsecond

/-- Fubini for the actual half-period mean, without a periodicity
assumption on the integrand. -/
theorem n06_angularMean_halfIntegral
    {D : ReferenceData} (hab : D.a ≤ D.b) {f : PolarPoint → ℝ}
    (hf : IntegrableOn f (radialCore D ×ˢ Ioc (0 : ℝ) Real.pi)) :
    (∫ r in D.a..D.b, angularMean (fun θ => f (r, θ))) =
      Real.pi⁻¹ * ∫ p in radialCore D ×ˢ Ioc (0 : ℝ) Real.pi, f p := by
  have hmeasure : volume.restrict (radialCore D ×ˢ Ioc (0 : ℝ) Real.pi) =
      (volume.restrict (radialCore D)).prod
        (volume.restrict (Ioc (0 : ℝ) Real.pi)) := by
    change ((volume : Measure ℝ).prod volume).restrict _ = _
    rw [← Measure.prod_restrict]
  have hprod : Integrable f ((volume.restrict (radialCore D)).prod
      (volume.restrict (Ioc (0 : ℝ) Real.pi))) := by
    rwa [IntegrableOn, hmeasure] at hf
  have hrad : (volume : Measure ℝ).restrict (radialCore D) =
      volume.restrict (Ioc D.a D.b) := Measure.restrict_congr_set Ioo_ae_eq_Ioc
  unfold angularMean
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_of_le hab]
  simp_rw [intervalIntegral.integral_of_le Real.pi_pos.le]
  rw [← hrad, hmeasure, integral_prod _ hprod, one_div]

/-- Two actual integrable half-tile pairings give the original full
physical mean against the half-period average of the test. The test
itself need not be periodic, smooth, or globally integrable. -/
theorem n06_fullPhysical_pairing_of_two_halves
    {D : ReferenceData} (hab : D.a ≤ D.b) {u φ : PolarPoint → ℝ}
    (hu : Function.Periodic u (0, Real.pi))
    (hfirst : IntegrableOn (fun p => u p * φ p)
      (radialCore D ×ˢ Ioc (0 : ℝ) Real.pi))
    (hshift : IntegrableOn (fun p => u p * φ (p + (0, Real.pi)))
      (radialCore D ×ˢ Ioc (0 : ℝ) Real.pi)) :
    IntegrableOn (fun p => u p * n06_radialTestAverage φ p)
      (radialCore D ×ˢ Ioc (0 : ℝ) Real.pi) ∧
    (∫ r in D.a..D.b, radialAngularMean (fun θ => u (r, θ) * φ (r, θ))) =
      Real.pi⁻¹ * ∫ p in radialCore D ×ˢ Ioc (0 : ℝ) Real.pi,
        u p * n06_radialTestAverage φ p := by
  have havg : (fun p => u p * n06_radialTestAverage φ p) =
      (fun p => (u p * φ p + u p * φ (p + (0, Real.pi))) / 2) := by
    funext p
    simp only [n06_radialTestAverage, n06_halfPeriodAverage, Prod.add_def,
      add_zero, Prod.eta]
    ring
  have havgI : IntegrableOn (fun p => u p * n06_radialTestAverage φ p)
      (radialCore D ×ˢ Ioc (0 : ℝ) Real.pi) := by
    rw [havg]
    exact (hfirst.add hshift).div_const 2
  have hmeasure : volume.restrict (radialCore D ×ˢ Ioc (0 : ℝ) Real.pi) =
      (volume.restrict (radialCore D)).prod
        (volume.restrict (Ioc (0 : ℝ) Real.pi)) := by
    change ((volume : Measure ℝ).prod volume).restrict _ = _
    rw [← Measure.prod_restrict]
  have hfirstP : Integrable (fun p => u p * φ p)
      ((volume.restrict (radialCore D)).prod (volume.restrict (Ioc (0 : ℝ) Real.pi))) := by
    rwa [IntegrableOn, hmeasure] at hfirst
  have hshiftP : Integrable (fun p => u p * φ (p + (0, Real.pi)))
      ((volume.restrict (radialCore D)).prod (volume.restrict (Ioc (0 : ℝ) Real.pi))) := by
    rwa [IntegrableOn, hmeasure] at hshift
  have hmean : (fun r => radialAngularMean (fun θ => u (r, θ) * φ (r, θ))) =ᵐ[
      volume.restrict (radialCore D)]
      (fun r => angularMean (fun θ => u (r, θ) * n06_radialTestAverage φ (r, θ))) := by
    filter_upwards [hfirstP.prod_right_ae, hshiftP.prod_right_ae] with r h₀ h₁
    have hup : Function.Periodic (fun θ => u (r, θ)) Real.pi := by
      intro θ
      simpa only [Prod.mk_add_mk, add_zero] using hu (r, θ)
    have h₀I := (intervalIntegrable_iff_integrableOn_Ioc_of_le Real.pi_pos.le).mpr h₀
    have h₁I : IntervalIntegrable (fun θ => u (r, θ) * φ (r, θ + Real.pi))
        volume 0 Real.pi := by
      simpa only [Prod.mk_add_mk, add_zero] using
        (intervalIntegrable_iff_integrableOn_Ioc_of_le Real.pi_pos.le).mpr h₁
    exact n06_radialAngularMean_pairing hup
      (n06_intervalIntegrable_full_pairing hup h₀I h₁I)
  refine ⟨havgI, ?_⟩
  calc
    _ = ∫ r in D.a..D.b, angularMean
        (fun θ => u (r, θ) * n06_radialTestAverage φ (r, θ)) := by
      have hrad : (volume : Measure ℝ).restrict (radialCore D) =
          volume.restrict (Ioc D.a D.b) := Measure.restrict_congr_set Ioo_ae_eq_Ioc
      rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
      rw [hrad] at hmean
      exact integral_congr_ae hmean
    _ = _ := n06_angularMean_halfIntegral hab havgI

end ContinuousFlexibility.Statements
