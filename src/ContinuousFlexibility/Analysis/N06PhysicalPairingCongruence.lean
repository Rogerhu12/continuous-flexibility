import ContinuousFlexibility.Analysis.N06PeriodicNormalizedRepresentation

/-!
# Physical weak pairings respect almost-everywhere representatives

The physical formulation uses an iterated full-period angular integral.
Fubini's almost-everywhere implication is enough to transport equality of
representatives through this pairing; no new integrability assumption is
needed for equality of the integrals themselves.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped Topology

set_option backward.isDefEq.respectTransparency false

theorem n06_radialAngularIntegral_congr_ae {D : ReferenceData} (hab : D.a ≤ D.b)
    {f g : PolarPoint → ℝ} (heq : f =ᵐ[volume.restrict (annularOpen D)] g) :
    (∫ r in D.a..D.b, radialAngularMean (fun θ => f (r, θ))) =
      ∫ r in D.a..D.b, radialAngularMean (fun θ => g (r, θ)) := by
  have hmeasure : (volume.restrict (Ioo D.a D.b)).prod (volume : Measure ℝ) =
      volume.restrict (annularOpen D) := by
    change _ = ((volume : Measure ℝ).prod (volume : Measure ℝ)).restrict
      (Ioo D.a D.b ×ˢ univ)
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  have hprod : f =ᵐ[(volume.restrict (Ioo D.a D.b)).prod (volume : Measure ℝ)] g := by
    rwa [hmeasure]
  have hmean : (fun r => radialAngularMean (fun θ => f (r, θ))) =ᵐ[
      volume.restrict (Ioo D.a D.b)]
      (fun r => radialAngularMean (fun θ => g (r, θ))) := by
    filter_upwards [Measure.ae_ae_of_ae_prod hprod] with r hr
    unfold radialAngularMean
    apply congrArg (fun x : ℝ => (2 * Real.pi)⁻¹ * x)
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hr] with θ hθ
    exact fun _ => hθ
  have hrestrict : (volume : Measure ℝ).restrict (Ioo D.a D.b) =
      volume.restrict (Ioc D.a D.b) := Measure.restrict_congr_set Ioo_ae_eq_Ioc
  rw [hrestrict] at hmean
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
  exact integral_congr_ae hmean

theorem n06_physicalPairing_congr_ae {D : ReferenceData} (hab : D.a ≤ D.b)
    {f g : PolarPoint → ℝ} (heq : f =ᵐ[volume.restrict (annularOpen D)] g)
    (φ : PolarPoint → ℝ) :
    (∫ r in D.a..D.b, radialAngularMean (fun θ => f (r, θ) * φ (r, θ))) =
      ∫ r in D.a..D.b, radialAngularMean (fun θ => g (r, θ) * φ (r, θ)) :=
  n06_radialAngularIntegral_congr_ae hab (heq.mul (Filter.EventuallyEq.refl _ _))

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ}

/-- A physical equation already proved for periodic representatives can be
transferred to any a.e.-equal representatives while keeping the exact row,
columns and full-period test class. -/
theorem n06_perturbedEquation_congr_ae (hab : D.a ≤ D.b)
    (z : AnnularState S × ℝ) (U : CanonicalUnknown S K)
    {η η' f f' : PolarPoint → ℝ}
    (hη : η' =ᵐ[volume.restrict (annularOpen D)] η)
    (hf : f' =ᵐ[volume.restrict (annularOpen D)] f)
    (hrow : referenceRow D η = 0)
    (heq : ∀ φ, RadialTest D φ →
      (∫ r in D.a..D.b, radialAngularMean (fun θ =>
        η (r, θ) * divergenceOperator (L.coefficients z) φ (r, θ))) +
        U.2.2.1 * (∫ r in D.a..D.b, radialAngularMean (fun θ =>
          nuColumnField D S C z (r, θ) * φ (r, θ))) +
        U.2.2.2 * (∫ r in D.a..D.b, radialAngularMean (fun θ =>
          (S.height (3 / 4 : ℝ)).decode S.psi (r, θ) * φ (r, θ))) =
      ∫ r in D.a..D.b, radialAngularMean (fun θ => f (r, θ) * φ (r, θ))) :
    referenceRow D η' = 0 ∧ ∀ φ, RadialTest D φ →
      (∫ r in D.a..D.b, radialAngularMean (fun θ =>
        η' (r, θ) * divergenceOperator (L.coefficients z) φ (r, θ))) +
        U.2.2.1 * (∫ r in D.a..D.b, radialAngularMean (fun θ =>
          nuColumnField D S C z (r, θ) * φ (r, θ))) +
        U.2.2.2 * (∫ r in D.a..D.b, radialAngularMean (fun θ =>
          (S.height (3 / 4 : ℝ)).decode S.psi (r, θ) * φ (r, θ))) =
      ∫ r in D.a..D.b, radialAngularMean (fun θ => f' (r, θ) * φ (r, θ)) := by
  refine ⟨(n06_referenceRow_congr_ae hab hη).trans hrow, ?_⟩
  intro φ hφ
  rw [n06_physicalPairing_congr_ae hab hη (divergenceOperator (L.coefficients z) φ),
    n06_physicalPairing_congr_ae hab hf φ]
  exact heq φ hφ

end ContinuousFlexibility.Statements
