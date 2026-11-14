module

public import ContinuousFlexibility.Radial.R11bModeL2
public import ContinuousFlexibility.Radial.R11bRadialTests
public import ContinuousFlexibility.Radial.R11bPhysicalPairing

/-!
# Closure of the actual normal weak derivative under physical L² convergence

Every smooth radial test and its normal partial derivative are physical L²
functions on the bounded annulus. The weak identity therefore passes to the
limit through the continuous Hilbert pairing, with the original angular
normalization preserved.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology InnerProductSpace
open ContinuousFlexibility.Statements

theorem r11b_tendsto_integral_mul_of_L2_tendsto
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : ℕ → α → ℝ} {u p : α → ℝ}
    (hf : ∀ n, MemLp (f n) 2 μ) (hu : MemLp u 2 μ) (hp : MemLp p 2 μ)
    (hlim : Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 (hu.toLp u))) :
    Tendsto (fun n => ∫ x, f n x * p x ∂μ) atTop (𝓝 (∫ x, u x * p x ∂μ)) := by
  have h := hlim.inner (𝕜 := ℝ)
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => hp.toLp p) atTop (𝓝 (hp.toLp p)))
  simpa only [r11b_real_inner_toLp_eq_integral] using h

theorem r11b_tendsto_angularMean_pairing_of_L2_tendsto
    {D : ReferenceData} (hab : D.a ≤ D.b)
    {f : ℕ → PolarPoint → ℝ} {u p : PolarPoint → ℝ}
    (hf : ∀ n, MemLp (f n) 2 (radialPhysicalMeasure D))
    (hu : MemLp u 2 (radialPhysicalMeasure D)) (hp : MemLp p 2 (radialPhysicalMeasure D))
    (hlim : Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 (hu.toLp u))) :
    Tendsto (fun n => ∫ r in D.a..D.b,
      radialAngularMean (fun θ => f n (r, θ) * p (r, θ))) atTop
      (𝓝 (∫ r in D.a..D.b, radialAngularMean (fun θ => u (r, θ) * p (r, θ)))) := by
  have hfun : (fun n => ∫ r in D.a..D.b,
      radialAngularMean (fun θ => f n (r, θ) * p (r, θ))) =
        (fun n => (2 * Real.pi)⁻¹ * ∫ x, f n x * p x ∂radialPhysicalMeasure D) :=
    funext fun n => r11b_integral_angularMean_mul_eq hab (hf n) hp
  rw [hfun, r11b_integral_angularMean_mul_eq hab hu hp]
  exact tendsto_const_nhds.mul (r11b_tendsto_integral_mul_of_L2_tendsto hf hu hp hlim)

theorem r11b_weakNormalDerivative_of_L2_tendsto
    {D : ReferenceData} (hab : D.a ≤ D.b)
    {f d : ℕ → PolarPoint → ℝ} {u v : PolarPoint → ℝ}
    (hf : ∀ n, MemLp (f n) 2 (radialPhysicalMeasure D))
    (hd : ∀ n, MemLp (d n) 2 (radialPhysicalMeasure D))
    (hu : MemLp u 2 (radialPhysicalMeasure D))
    (hv : MemLp v 2 (radialPhysicalMeasure D))
    (hfu : Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 (hu.toLp u)))
    (hdv : Tendsto (fun n => (hd n).toLp (d n)) atTop (𝓝 (hv.toLp v)))
    (hweak : ∀ n, WeakNormalDerivative D (f n) (d n)) :
    WeakNormalDerivative D u v := by
  intro ψ hψ
  have hψLp : MemLp ψ 2 (radialPhysicalMeasure D) :=
    r11b_continuous_memLp hψ.1.continuous
  have hψrLp : MemLp (radialPartial ψ) 2 (radialPhysicalMeasure D) :=
    r11b_continuous_memLp (r11b_radialTest_radialPartial hψ).1.continuous
  have hleft := r11b_tendsto_angularMean_pairing_of_L2_tendsto hab hf hu hψrLp hfu
  have hright := r11b_tendsto_angularMean_pairing_of_L2_tendsto hab hd hv hψLp hdv
  have hseq : (fun n => ∫ r in D.a..D.b,
      radialAngularMean (fun θ => f n (r, θ) * radialPartial ψ (r, θ))) =
        (fun n => -(∫ r in D.a..D.b,
          radialAngularMean (fun θ => d n (r, θ) * ψ (r, θ)))) :=
    funext fun n => hweak n ψ hψ
  rw [hseq] at hleft
  exact tendsto_nhds_unique hleft hright.neg

end ContinuousFlexibility.Radial
