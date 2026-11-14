module

public import ContinuousFlexibility.Analysis.N07aAngularReferenceRadialGreen
public import ContinuousFlexibility.Analysis.N07aAngularReferenceTestParts

/-!
# The transported field satisfies the actual maximum reference equation

This is the original full-period RadialTest identity. The continuous
first jet removes interface flux jumps; the second normal derivative is
used only on actual open pieces and as the integrable right derivative.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open ContinuousFlexibility.Radial
open scoped Topology ContDiff

theorem n07a_referenceInteriorDifferential_green
    {D : ReferenceData} {S : PhysicalSpacesData} {K : CanonicalData S}
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    {v : PolarPoint → ℝ} (hv : ContDiffOn ℝ 1 v (annularOpen D))
    (hpiece : ∀ m, ContDiffOn ℝ ∞ v (referencePhysicalPieceOpen S K m))
    (hvp : Function.Periodic v (0, Real.pi))
    (hright : ∀ p ∈ annularOpen D, ∃ u : PolarPoint → ℝ,
      ContDiffAt ℝ ∞ u p ∧ ∀ᶠ q in 𝓝 p, p.1 ≤ q.1 → v q = u q)
    (hcover : ∀ᵐ r ∂volume.restrict (radialCore D),
      ∃ m, r ∈ Ioo (K.physicalLeft m) (K.physicalRight m))
    {γ M μ : ℝ} (hOut : OutputMember D γ M (v, μ))
    (hN : Integrable (n07aReferenceNormalSource D K v) (radialPhysicalMeasure D))
    (hF : Integrable (n07aReferenceInteriorDifferential D K v) (radialPhysicalMeasure D))
    {φ : PolarPoint → ℝ} (hφ : RadialTest D φ) :
    radialWeakPairing D v φ = ∫ r in D.a..D.b, radialAngularMean
      (fun θ => n07aReferenceInteriorDifferential D K v (r, θ) * φ (r, θ)) := by
  have hgeom := hD.choose_spec.1
  have hab := hgeom.2.1.le
  have hw := hgeom.2.2.1
  obtain ⟨hNs, hAs, J, hJ, hJD, hzero⟩ := n07a_referenceTestParts_continuous_support hgeom hφ
  have hNv : Integrable (fun p => v p * n07aReferenceTestNormal D φ p)
      (radialPhysicalMeasure D) := r11b_output_pairing_integrable hD hborder hOut hNs
    ⟨J, hJ, hJD, fun r hr θ => (hzero r hr θ).1⟩
  have hAv : Integrable (fun p => v p * n07aReferenceTestAngular D φ p)
      (radialPhysicalMeasure D) := r11b_output_pairing_integrable hD hborder hOut hAs
    ⟨J, hJ, hJD, fun r hr θ => (hzero r hr θ).2⟩
  have hNφ := n07a_physical_integrable_mul_continuous hN hφ.1.continuous
  have hFφ := n07a_physical_integrable_mul_continuous hF hφ.1.continuous
  have hAφ : Integrable (fun p => (n07aReferenceInteriorDifferential D K v p -
      n07aReferenceNormalSource D K v p) * φ p) (radialPhysicalMeasure D) := by
    exact (hFφ.sub hNφ).congr (Eventually.of_forall fun p => by
      simp only [Pi.sub_apply, sub_mul])
  have hNp : Integrable (n07aReferenceNormalSource D K v)
      ((volume.restrict (radialCore D)).prod
        (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))) := by
    simpa only [r11b_radialPhysicalMeasure_eq_prod] using hN
  have hRad : (∫ p, v p * n07aReferenceTestNormal D φ p ∂radialPhysicalMeasure D) =
      ∫ p, n07aReferenceNormalSource D K v p * φ p ∂radialPhysicalMeasure D := by
    have hNv' := hNv
    have hNφ' := hNφ
    rw [r11b_radialPhysicalMeasure_eq_prod] at hNv' hNφ' ⊢
    rw [integral_prod_symm _ hNv', integral_prod_symm _ hNφ']
    apply integral_congr_ae
    filter_upwards [hNp.prod_left_ae] with θ hθ
    have he := n07a_referenceNormalSource_ae_right
      (hw.1.differentiable (by simp)) hpiece hcover θ
    have hg : IntervalIntegrable (fun r => n07aReferenceRightFluxDerivative D v (r, θ))
        volume D.a D.b :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le hab).mpr (hθ.congr he)
    have hgreen := n07a_reference_radial_green_slice hgeom.2.1 hw hv hright hφ θ hg
    simp_rw [← n07a_referenceTestNormal_slice (hw.1.differentiable (by simp)) hφ.1] at hgreen
    rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab,
      ← restrict_Ioo_eq_restrict_Ioc] at hgreen
    exact hgreen.trans (integral_congr_ae (he.symm.mono fun r hr =>
      congrArg (· * φ (r, θ)) hr))
  have hAng : (∫ p, v p * n07aReferenceTestAngular D φ p ∂radialPhysicalMeasure D) =
      ∫ p, (n07aReferenceInteriorDifferential D K v p -
        n07aReferenceNormalSource D K v p) * φ p ∂radialPhysicalMeasure D := by
    have hAv' := hAv
    have hAφ' := hAφ
    rw [r11b_radialPhysicalMeasure_eq_prod] at hAv' hAφ' ⊢
    rw [integral_prod _ hAv', integral_prod _ hAφ']
    apply integral_congr_ae
    filter_upwards [hcover] with r hr
    obtain ⟨m, hm⟩ := hr
    have hgreen := n07a_reference_angular_green_on_piece (hpiece m) hvp hφ hm
    simpa only [intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)] using hgreen
  have hL := r11b_radialPDE_test_pairing_integrable hD hborder hOut hφ
  rw [radialWeakPairing, r11b_integral_angularMean_eq hab hL,
    r11b_integral_angularMean_eq hab hFφ]
  apply congrArg ((2 * Real.pi)⁻¹ * ·)
  have heq : (fun p : PolarPoint => v p * radialPDE D.w (fun r θ => φ (r, θ)) p.1 p.2) =
      fun p => v p * n07aReferenceTestNormal D φ p + v p * n07aReferenceTestAngular D φ p := by
    funext p
    rw [n07a_referenceTest_parts (hw.1.differentiable (by simp)) hφ.1, mul_add]
  rw [heq, integral_add hNv hAv, hRad, hAng, ← integral_add hNφ hAφ]
  apply integral_congr_ae
  exact Eventually.of_forall fun p => by ring

end ContinuousFlexibility.Analysis
