import ContinuousFlexibility.Radial.R11bModeL2
import ContinuousFlexibility.Radial.R11bPhysicalPairing
import ContinuousFlexibility.Radial.AngularMeanProbability

/-!
# Physical fields and the manuscript's angular coefficients

The normalized angular product measure is exactly (2π)⁻¹ times the
physical measure. Thus the raw angular mean and every positive cosine
coefficient of an actual physical L² field are radial L² functions.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory Real
open ContinuousFlexibility.Statements

theorem r11b_radial_prod_angularMeanMeasure (D : ReferenceData) :
    ((volume : Measure ℝ).restrict (radialCore D)).prod angularMeanMeasure =
      ENNReal.ofReal (1 / (2 * Real.pi)) • radialPhysicalMeasure D := by
  rw [angularMeanMeasure, Measure.prod_smul_right,
    ← r11b_radialPhysicalMeasure_eq_prod]

theorem r11b_memLp_radial_angularMean {D : ReferenceData} {f : PolarPoint → ℝ}
    (hf : MemLp f 2 (radialPhysicalMeasure D)) :
    MemLp f 2 (((volume : Measure ℝ).restrict (radialCore D)).prod angularMeanMeasure) := by
  rw [r11b_radial_prod_angularMeanMeasure]
  exact hf.smul_measure ENNReal.ofReal_ne_top

theorem r11b_integral_sq_radial_angularMean (D : ReferenceData) (f : PolarPoint → ℝ) :
    (∫ z, f z ^ 2 ∂((volume : Measure ℝ).restrict (radialCore D)).prod
      angularMeanMeasure) =
      (1 / (2 * Real.pi)) * ∫ z, f z ^ 2 ∂radialPhysicalMeasure D := by
  rw [r11b_radial_prod_angularMeanMeasure, integral_smul_measure,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 1 / (2 * Real.pi)), smul_eq_mul]

theorem r11b_memLp_angularCoefficient {D : ReferenceData} {f : PolarPoint → ℝ}
    {e : ℝ → ℝ} (hf : MemLp f 2 (radialPhysicalMeasure D))
    (he : MemLp e 2 angularMeanMeasure) :
    MemLp (fun r => angularAverage (fun θ => f (r, θ) * e θ))
      2 (volume.restrict (radialCore D)) ∧
      (∫ r, angularAverage (fun θ => f (r, θ) * e θ) ^ 2
        ∂volume.restrict (radialCore D)) ≤
      angularAverage (fun θ => e θ ^ 2) *
        ((1 / (2 * Real.pi)) * ∫ z, f z ^ 2 ∂radialPhysicalMeasure D) := by
  have h := r11b_memLp_modeCoefficient (r11b_memLp_radial_angularMean hf) he
  simp_rw [← angularAverage_eq_integral_angularMeanMeasure] at h
  rw [r11b_integral_sq_radial_angularMean] at h
  exact h

theorem r11b_referenceMode_L2_bound {D : ReferenceData} {f : PolarPoint → ℝ}
    (hf : MemLp f 2 (radialPhysicalMeasure D)) (j : ℕ) (hj : 0 < j) :
    MemLp (referenceMode f j) 2 (volume.restrict (radialCore D)) ∧
      (∫ r, referenceMode f j r ^ 2 ∂volume.restrict (radialCore D)) ≤
        (1 / (2 * Real.pi)) * ∫ z, f z ^ 2 ∂radialPhysicalMeasure D := by
  have he : MemLp (cosineMode j) 2 angularMeanMeasure :=
    memLp_angularMeanMeasure (angularInterval_memLp_of_continuous (by
      unfold cosineMode
      fun_prop))
  have hunit : angularAverage (fun θ => cosineMode j θ ^ 2) = 1 := by
    simpa [angularPairing, pow_two] using
      angularPairing_cosineMode j j hj hj
  have h := r11b_memLp_angularCoefficient hf he
  rw [hunit, one_mul] at h
  have hmode : referenceMode f j =
      fun r => angularAverage (fun θ => f (r, θ) * cosineMode j θ) := by
    funext r
    simp only [referenceMode, radialAngularMean, angularAverage, one_div]
  rw [hmode]
  exact h

theorem r11b_radialAngularMean_L2_bound {D : ReferenceData} {f : PolarPoint → ℝ}
    (hf : MemLp f 2 (radialPhysicalMeasure D)) :
    MemLp (fun r => radialAngularMean (fun θ => f (r, θ)))
      2 (volume.restrict (radialCore D)) ∧
      (∫ r, radialAngularMean (fun θ => f (r, θ)) ^ 2
        ∂volume.restrict (radialCore D)) ≤
        (1 / (2 * Real.pi)) * ∫ z, f z ^ 2 ∂radialPhysicalMeasure D := by
  have he : MemLp (fun _ : ℝ => (1 : ℝ)) 2 angularMeanMeasure := memLp_const 1
  have hunit : angularAverage (fun _ : ℝ => (1 : ℝ) ^ 2) = 1 := by
    rw [angularAverage_eq_integral_angularMeanMeasure]
    simp
  have h := r11b_memLp_angularCoefficient hf he
  rw [hunit, one_mul] at h
  simpa only [mul_one, radialAngularMean, angularAverage, one_div] using h

end ContinuousFlexibility.Radial
