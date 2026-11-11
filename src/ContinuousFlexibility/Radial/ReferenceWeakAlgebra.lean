import ContinuousFlexibility.Radial.ReferenceTestIntegrability

/-!
# Algebra and representative invariance of the actual weak pairing

The addition rules use genuine integrability of the test products.
Consequently they apply on the repaired local L² domain and do not
depend on totalized integrals of nonmeasurable representatives.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory

theorem integral_angularMean_add {D : ReferenceData} (hab : D.a ≤ D.b)
    {f g : PolarPoint → ℝ}
    (hf : Integrable f (radialPhysicalMeasure D))
    (hg : Integrable g (radialPhysicalMeasure D)) :
    (∫ r in D.a..D.b, radialAngularMean (fun θ => f (r, θ) + g (r, θ))) =
      (∫ r in D.a..D.b, radialAngularMean (fun θ => f (r, θ))) +
        ∫ r in D.a..D.b, radialAngularMean (fun θ => g (r, θ)) := by
  have hfg : Integrable (fun x => f x + g x) (radialPhysicalMeasure D) := by
    simpa only [Pi.add_apply] using hf.add hg
  rw [integral_angularMean_eq_physical hab hfg,
    integral_angularMean_eq_physical hab hf,
    integral_angularMean_eq_physical hab hg,
    integral_add hf hg, mul_add]

theorem integral_angularMean_congr_ae {D : ReferenceData} (hab : D.a ≤ D.b)
    {f g : PolarPoint → ℝ}
    (hf : Integrable f (radialPhysicalMeasure D))
    (hfg : f =ᵐ[radialPhysicalMeasure D] g) :
    (∫ r in D.a..D.b, radialAngularMean (fun θ => f (r, θ))) =
      ∫ r in D.a..D.b, radialAngularMean (fun θ => g (r, θ)) := by
  rw [integral_angularMean_eq_physical hab hf,
    integral_angularMean_eq_physical hab (hf.congr hfg)]
  exact congrArg (fun z : ℝ => (2 * Real.pi)⁻¹ * z) (integral_congr_ae hfg)

theorem radialWeakPairing_const_mul (D : ReferenceData) (c : ℝ)
    (f ψ : PolarPoint → ℝ) :
    radialWeakPairing D (fun x => c * f x) ψ = c * radialWeakPairing D f ψ := by
  unfold radialWeakPairing
  simp only [mul_assoc, radialAngularMean_const_mul, intervalIntegral.integral_const_mul]

theorem radialWeakPairing_add {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {f g ψ : PolarPoint → ℝ}
    (hf : RadialCellIntegrable D f) (hg : RadialCellIntegrable D g)
    (hψ : RadialTest D ψ) :
    radialWeakPairing D (fun x => f x + g x) ψ =
      radialWeakPairing D f ψ + radialWeakPairing D g ψ := by
  obtain ⟨C, hC⟩ := hD
  simpa only [radialWeakPairing, add_mul] using
    integral_angularMean_add hC.1.2.1.le
      (hf.integrable_mul_testOperator ⟨C, hC⟩ hψ)
      (hg.integrable_mul_testOperator ⟨C, hC⟩ hψ)

theorem radialWeakPairing_congr_ae {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {f g ψ : PolarPoint → ℝ}
    (hf : RadialCellIntegrable D f) (hψ : RadialTest D ψ)
    (hfg : f =ᵐ[radialPhysicalMeasure D] g) :
    radialWeakPairing D f ψ = radialWeakPairing D g ψ := by
  obtain ⟨C, hC⟩ := hD
  have he : (fun x => f x *
      Radial.radialPDE D.w (fun r θ => ψ (r, θ)) x.1 x.2) =ᵐ[radialPhysicalMeasure D]
      (fun x => g x * Radial.radialPDE D.w (fun r θ => ψ (r, θ)) x.1 x.2) := by
    filter_upwards [hfg] with x hx
    exact congrArg (fun y => y *
      Radial.radialPDE D.w (fun r θ => ψ (r, θ)) x.1 x.2) hx
  simpa only [radialWeakPairing] using
    integral_angularMean_congr_ae hC.1.2.1.le
      (hf.integrable_mul_testOperator ⟨C, hC⟩ hψ) he

theorem radialWeakPairing_sub {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {f g ψ : PolarPoint → ℝ}
    (hf : RadialCellIntegrable D f) (hg : RadialCellIntegrable D g)
    (hψ : RadialTest D ψ) :
    radialWeakPairing D (fun x => f x - g x) ψ =
      radialWeakPairing D f ψ - radialWeakPairing D g ψ := by
  have he : (fun x => f x - g x) = (fun x => f x + (-1) * g x) := by
    funext x
    ring
  rw [he, radialWeakPairing_add hD hf (hg.const_mul (-1)) hψ,
    radialWeakPairing_const_mul]
  ring

end ContinuousFlexibility.Statements
