import ContinuousFlexibility.Analysis.N07aAngularReferenceDecomposition
import ContinuousFlexibility.Analysis.N07aAngularEndpointFlux

/-!
# The actual compatible mean of the transported reference source

Fubini is used only after the genuine physical source is integrable. Its
normal part has zero radial integral by the continuous endpoint flux.
Its angular part has zero mean on every actual open piece, which is an
a.e. cover. No compatibility condition is imposed on the new source.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open ContinuousFlexibility.Radial
open scoped Topology ContDiff

theorem n07a_integrable_radialAngularMean {D : ReferenceData} (hab : D.a ≤ D.b)
    {f : PolarPoint → ℝ} (hf : Integrable f (radialPhysicalMeasure D)) :
    IntervalIntegrable (fun r => radialAngularMean (fun θ => f (r, θ))) volume D.a D.b := by
  have hp : Integrable f ((volume.restrict (radialCore D)).prod
      (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))) := by
    simpa only [r11b_radialPhysicalMeasure_eq_prod] using hf
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hab]
  simpa only [radialAngularMean, radialCore, IntegrableOn,
    intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)] using
      hp.integral_prod_left.const_mul ((2 * Real.pi)⁻¹)

theorem n07a_radialMean_integral_zero_of_sections {D : ReferenceData}
    (hab : D.a ≤ D.b) {f : PolarPoint → ℝ}
    (hf : Integrable f (radialPhysicalMeasure D))
    (hsections : ∀ᵐ θ ∂volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)),
      (∫ r in D.a..D.b, f (r, θ)) = 0) :
    (∫ r in D.a..D.b, radialAngularMean (fun θ => f (r, θ))) = 0 := by
  have hp : Integrable f ((volume.restrict (radialCore D)).prod
      (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))) := by
    simpa only [r11b_radialPhysicalMeasure_eq_prod] using hf
  rw [r11b_integral_angularMean_eq hab hf, r11b_radialPhysicalMeasure_eq_prod,
    integral_prod_symm _ hp]
  have he : (fun θ => ∫ r, f (r, θ) ∂volume.restrict (radialCore D)) =ᵐ[
      volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))] fun _ => (0 : ℝ) := by
    filter_upwards [hsections] with θ hθ
    simpa only [intervalIntegral.integral_of_le hab,
      radialCore, restrict_Ioo_eq_restrict_Ioc] using hθ
  rw [integral_congr_ae he, integral_zero, mul_zero]

theorem n07a_referenceInteriorDifferential_compatible_mean
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ}
    (h04 : N04Properties D T S C L K base loss ε)
    (hab : D.a ≤ D.b) (hw : EndpointFlat D D.w) {v : PolarPoint → ℝ}
    (hv : ContDiffOn ℝ 1 v (annularOpen D))
    (hpiece : ∀ m, ContDiffOn ℝ ∞ v (physicalPieceOpen S K m))
    (hvp : Function.Periodic v (0, Real.pi))
    (hright : ∀ p ∈ annularOpen D, ∃ u : PolarPoint → ℝ,
      ContDiffAt ℝ ∞ u p ∧ ∀ᶠ q in 𝓝 p, p.1 ≤ q.1 → v q = u q)
    {B : ℝ} (hB : ∀ r ∈ radialCore D, ∀ θ, |radialPartial v (r, θ)| ≤ B)
    (hN : Integrable (n07aReferenceNormalSource D K v) (radialPhysicalMeasure D))
    (hF : Integrable (n07aReferenceInteriorDifferential D K v) (radialPhysicalMeasure D)) :
    IntervalIntegrable (fun r => radialAngularMean
      (fun θ => n07aReferenceInteriorDifferential D K v (r, θ))) volume D.a D.b ∧
    (∫ r in D.a..D.b, radialAngularMean
      (fun θ => n07aReferenceInteriorDifferential D K v (r, θ))) = 0 := by
  have hcover := n07a_referencePieceInterior_ae h04
  have hNp : Integrable (n07aReferenceNormalSource D K v)
      ((volume.restrict (radialCore D)).prod
        (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))) := by
    simpa only [r11b_radialPhysicalMeasure_eq_prod] using hN
  have hnormal : (∫ r in D.a..D.b, radialAngularMean
      (fun θ => n07aReferenceNormalSource D K v (r, θ))) = 0 := by
    apply n07a_radialMean_integral_zero_of_sections hab hN
    filter_upwards [hNp.prod_left_ae] with θ hθ
    have he := n07a_referenceNormalSource_ae_right
      (hw.1.differentiable (by simp)) hpiece hcover θ
    have hg : IntervalIntegrable (fun r => n07aReferenceRightFluxDerivative D v (r, θ))
        volume D.a D.b :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le hab).mpr (hθ.congr he)
    calc
      _ = ∫ r in D.a..D.b, n07aReferenceRightFluxDerivative D v (r, θ) := by
        rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab,
          ← restrict_Ioo_eq_restrict_Ioc]
        exact integral_congr_ae he
      _ = 0 := n07a_referenceRightFluxDerivative_integral_zero hab hw hv hright θ
        (fun r hr => hB r hr θ) hg
  refine ⟨n07a_integrable_radialAngularMean hab hF, ?_⟩
  calc
    _ = ∫ r in D.a..D.b, radialAngularMean
        (fun θ => n07aReferenceNormalSource D K v (r, θ)) := by
      rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab,
        ← restrict_Ioo_eq_restrict_Ioc]
      apply integral_congr_ae
      filter_upwards [hcover] with r hr
      obtain ⟨m, hm⟩ := hr
      exact n07a_referenceSource_mean_eq_normal_on_piece (hpiece m) hvp hm
    _ = 0 := hnormal

end ContinuousFlexibility.Analysis
