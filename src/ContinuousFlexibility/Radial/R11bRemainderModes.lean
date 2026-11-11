import ContinuousFlexibility.Radial.R11bPhysicalCompleteness

/-!
# Positive angular modes ignore an actual radial remainder

The claim is made almost everywhere in the radial variable. Its proof uses
physical L² slices, so it does not assume integrability of exceptional rows.
-/

namespace ContinuousFlexibility.Radial

noncomputable section

open Set MeasureTheory
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

theorem r11b_angularPairing_constant_cosine_eq_zero
    (c : ℝ) (j : ℕ) (hj : 0 < j) :
    angularPairing (fun _ : ℝ => c) (cosineMode j) = 0 := by
  change (1 / (2 * Real.pi)) *
    (∫ θ in (0 : ℝ)..2 * Real.pi, c * cosineMode j θ) = 0
  rw [intervalIntegral.integral_const_mul, integral_cosineMode j hj, mul_zero, mul_zero]

theorem r11b_referenceMode_sub_radial_ae {D : ReferenceData} {f : PolarPoint → ℝ}
    (hf : MemLp f 2 (radialPhysicalMeasure D)) (a : ℝ → ℝ) (j : ℕ) (hj : 0 < j) :
    referenceMode (fun x => f x - a x.1) j
      =ᵐ[volume.restrict (radialCore D)] referenceMode f j := by
  have hjLp : MemLp (cosineMode j) 2
      (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))) := by
    apply angularInterval_memLp_of_continuous
    exact continuous_const.mul
      (Real.continuous_cos.comp (continuous_const.mul continuous_id))
  filter_upwards [r11b_physical_memLp_angular_sections hf] with r hr
  have haLp : MemLp (fun _ : ℝ => a r) 2
      (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))) :=
    angularInterval_memLp_of_continuous continuous_const
  have h := angularPairing_sub_left_of_memLp hr haLp hjLp
  rw [r11b_angularPairing_constant_cosine_eq_zero (a r) j hj, sub_zero] at h
  simpa only [referenceMode, radialAngularMean, angularPairing, angularAverage, one_div] using h

theorem r11b_referenceMode_outputRemainder_ae {D : ReferenceData} {U : RadialUnknown}
    (hU : MemLp U.1 2 (radialPhysicalMeasure D)) (aL : ℝ) (j : ℕ) (hj : 0 < j) :
    referenceMode (outputRemainder D aL U) j
      =ᵐ[volume.restrict (radialCore D)] referenceMode U.1 j :=
  r11b_referenceMode_sub_radial_ae hU (fun r => aL * D.chiLeft r) j hj

/-- The zero channel changes by exactly the subtracted radial function. -/
theorem r11b_radialAngularMean_sub_radial_ae {D : ReferenceData} {f : PolarPoint → ℝ}
    (hf : MemLp f 2 (radialPhysicalMeasure D)) (a : ℝ → ℝ) :
    (fun r => radialAngularMean (fun θ => f (r, θ) - a r))
      =ᵐ[volume.restrict (radialCore D)]
        (fun r => radialAngularMean (fun θ => f (r, θ)) - a r) := by
  filter_upwards [r11b_physical_memLp_angular_sections hf] with r hr
  have haLp : MemLp (fun _ : ℝ => a r) 2
      (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))) :=
    angularInterval_memLp_of_continuous continuous_const
  have hc : angularAverage (fun _ : ℝ => a r) = a r := by
    rw [angularAverage_eq_integral_angularMeanMeasure]
    simp
  have h := angularAverage_sub_of_memLp hr haLp
  rw [hc] at h
  simpa only [radialAngularMean, angularAverage, one_div] using h

theorem r11b_radialAngularMean_outputRemainder_ae
    {D : ReferenceData} {U : RadialUnknown}
    (hU : MemLp U.1 2 (radialPhysicalMeasure D)) (aL : ℝ) :
    (fun r => radialAngularMean (fun θ => outputRemainder D aL U (r, θ)))
      =ᵐ[volume.restrict (radialCore D)]
        (fun r => radialAngularMean (fun θ => U.1 (r, θ)) - aL * D.chiLeft r) :=
  r11b_radialAngularMean_sub_radial_ae hU (fun r => aL * D.chiLeft r)

end

end ContinuousFlexibility.Radial
