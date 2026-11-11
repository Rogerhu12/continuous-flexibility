import ContinuousFlexibility.Radial.R11bGlobalL2
import ContinuousFlexibility.Radial.ReferenceCellAlgebra

/-!
# Uniqueness of the auxiliary source scalar

The integral obstruction is removed by a fixed normalized column. Actual
positive-weight source membership supplies the integrability needed to
compare a.e. representatives; no identity of total integrals is used
without that premise.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open ContinuousFlexibility.Radial

/-- The two compatible sources determine the same auxiliary scalar, even
when their positive endpoint and material exponents differ. -/
theorem n05_referenceAuxiliaryScalar_unique {D : ReferenceData}
    (hD : IsAccumulatingProfile D)
    {γ₀ γ₁ M₀ M₁ a b : ℝ} (hγ₀ : 0 < γ₀) (hγ₁ : 0 < γ₁)
    {ψ f g : PolarPoint → ℝ}
    (hψ : (∫ r in D.a..D.b, radialAngularMean (fun θ => ψ (r, θ))) = 1)
    (hfg : f =ᵐ[radialPhysicalMeasure D] g)
    (hf : SourceMember D γ₀ M₀ ((fun p => f p - a * ψ p), 0))
    (hg : SourceMember D γ₁ M₁ ((fun p => g p - b * ψ p), 0)) :
    a = b := by
  letI : IsFiniteMeasure (radialPhysicalMeasure D) :=
    ⟨r11b_radialPhysicalMeasure_finite D⟩
  have hab : D.a ≤ D.b := hD.choose_spec.1.2.1.le
  let u : PolarPoint → ℝ := fun p => f p - a * ψ p
  let v : PolarPoint → ℝ := fun p => g p - b * ψ p
  have hu : Integrable u (radialPhysicalMeasure D) :=
    (r11b_source_memLp hD hγ₀ hf).integrable (by norm_num)
  have hv : Integrable v (radialPhysicalMeasure D) :=
    (r11b_source_memLp hD hγ₁ hg).integrable (by norm_num)
  have humean : (∫ r in D.a..D.b, radialAngularMean (fun θ => u (r, θ))) = 0 :=
    hf.2.2.2.2.2
  have hvmean : (∫ r in D.a..D.b, radialAngularMean (fun θ => v (r, θ))) = 0 :=
    hg.2.2.2.2.2
  have hmean : (∫ r in D.a..D.b,
      radialAngularMean (fun θ => u (r, θ) - v (r, θ))) = 0 := by
    rw [r11b_integral_angularMean_eq hab (hu.sub hv),
      integral_sub hu hv, mul_sub,
      ← r11b_integral_angularMean_eq hab hu,
      ← r11b_integral_angularMean_eq hab hv, humean, hvmean, sub_self]
  have he : (fun p => u p - v p) =ᵐ[radialPhysicalMeasure D]
      (fun p => (b - a) * ψ p) := by
    filter_upwards [hfg] with p hp
    dsimp only [u, v]
    rw [hp]
    ring
  have hscaled : Integrable (fun p => (b - a) * ψ p) (radialPhysicalMeasure D) :=
    (hu.sub hv).congr he
  have hzero : (∫ r in D.a..D.b,
      radialAngularMean (fun θ => (b - a) * ψ (r, θ))) = 0 :=
    (r11b_integral_angularMean_congr_ae hab (hu.sub hv) hscaled he).symm.trans hmean
  simp_rw [radialAngularMean_const_mul] at hzero
  rw [intervalIntegral.integral_const_mul, hψ, mul_one] at hzero
  linarith

end ContinuousFlexibility.Statements
