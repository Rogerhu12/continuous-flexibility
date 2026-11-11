import ContinuousFlexibility.Radial.R11bWeakNormalLimit

/-!
# Finite linearity of the actual weak normal derivative

All sums here are sums of raw physical L² functions. Integrability of the
test pairings justifies each finite interchange of sums and integrals.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory
open scoped BigOperators
open ContinuousFlexibility.Statements

theorem r11b_weakNormalDerivative_finsetSum {D : ReferenceData}
    (hab : D.a ≤ D.b) {ι : Type*} (s : Finset ι)
    (f d : ι → PolarPoint → ℝ)
    (hf : ∀ i ∈ s, MemLp (f i) 2 (radialPhysicalMeasure D))
    (hd : ∀ i ∈ s, MemLp (d i) 2 (radialPhysicalMeasure D))
    (hweak : ∀ i ∈ s, WeakNormalDerivative D (f i) (d i)) :
    WeakNormalDerivative D (fun x => ∑ i ∈ s, f i x)
      (fun x => ∑ i ∈ s, d i x) := by
  have hfs : MemLp (fun x => ∑ i ∈ s, f i x) 2 (radialPhysicalMeasure D) := by
    simpa only [Finset.sum_apply] using memLp_finsetSum s hf
  have hds : MemLp (fun x => ∑ i ∈ s, d i x) 2 (radialPhysicalMeasure D) := by
    simpa only [Finset.sum_apply] using memLp_finsetSum s hd
  intro ψ hψ
  have hψLp : MemLp ψ 2 (radialPhysicalMeasure D) :=
    r11b_continuous_memLp hψ.1.continuous
  have hψrLp : MemLp (radialPartial ψ) 2 (radialPhysicalMeasure D) :=
    r11b_continuous_memLp (r11b_radialTest_radialPartial hψ).1.continuous
  have hi (i : ι) (hi : i ∈ s) :
      (∫ x, f i x * radialPartial ψ x ∂radialPhysicalMeasure D) =
        -(∫ x, d i x * ψ x ∂radialPhysicalMeasure D) := by
    have h := hweak i hi ψ hψ
    rw [r11b_integral_angularMean_mul_eq hab (hf i hi) hψrLp,
      r11b_integral_angularMean_mul_eq hab (hd i hi) hψLp] at h
    apply mul_left_cancel₀ (inv_ne_zero (by positivity : (2 * Real.pi) ≠ 0))
    simpa only [mul_neg] using h
  have hleft :
      (∫ x, (∑ i ∈ s, f i x) * radialPartial ψ x ∂radialPhysicalMeasure D) =
        ∑ i ∈ s, ∫ x, f i x * radialPartial ψ x ∂radialPhysicalMeasure D := by
    simp_rw [Finset.sum_mul]
    exact integral_finsetSum s (fun i hi => (hf i hi).integrable_mul hψrLp)
  have hright :
      (∫ x, (∑ i ∈ s, d i x) * ψ x ∂radialPhysicalMeasure D) =
        ∑ i ∈ s, ∫ x, d i x * ψ x ∂radialPhysicalMeasure D := by
    simp_rw [Finset.sum_mul]
    exact integral_finsetSum s (fun i hi => (hd i hi).integrable_mul hψLp)
  have hsum :
      (∑ i ∈ s, ∫ x, f i x * radialPartial ψ x ∂radialPhysicalMeasure D) =
        -(∑ i ∈ s, ∫ x, d i x * ψ x ∂radialPhysicalMeasure D) := by
    calc
      (∑ i ∈ s, ∫ x, f i x * radialPartial ψ x ∂radialPhysicalMeasure D) =
          ∑ i ∈ s, -(∫ x, d i x * ψ x ∂radialPhysicalMeasure D) :=
        Finset.sum_congr rfl hi
      _ = _ := Finset.sum_neg_distrib
  rw [r11b_integral_angularMean_mul_eq hab hfs hψrLp,
    r11b_integral_angularMean_mul_eq hab hds hψLp, hleft, hright, hsum]
  ring

end ContinuousFlexibility.Radial
