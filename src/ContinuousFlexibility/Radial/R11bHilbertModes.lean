import ContinuousFlexibility.Radial.R11bHilbertDensity
import ContinuousFlexibility.Radial.R11bAngularL2Bridge
import ContinuousFlexibility.Radial.R11bInverseDensity
import ContinuousFlexibility.Radial.R11bGlobalL2

/-!
# Actual source and output coefficients in the radial Hilbert space

The source quotient is the manuscript's -f_j/(12w/r²), with its original
angular integral. The source argument also accepts an arbitrary L² angular
factor, including sine modes. Output coefficients retain the full field;
only the earlier inverse-density estimate uses the subtracted left tail.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory Real
open ContinuousFlexibility.Statements

theorem r11b_angularAverage_const_mul (c : ℝ) (f : ℝ → ℝ) :
    angularAverage (fun θ => c * f θ) = c * angularAverage f := by
  unfold angularAverage
  rw [intervalIntegral.integral_const_mul]
  ring

theorem r11b_angularCoefficient_div_memLp_radialHilbert {D : ReferenceData}
    (hgeom : RadialProfileGeometry D) {f : PolarPoint → ℝ} {e : ℝ → ℝ}
    (hf : MemLp (fun x => sqrt ((D.w x.1)⁻¹) * f x)
      2 (radialPhysicalMeasure D)) (he : MemLp e 2 angularMeanMeasure) :
    MemLp (fun r => -angularAverage (fun θ => f (r, θ) * e θ) /
      (12 * D.w r / r ^ 2)) 2 (radialHilbertMeasure D) := by
  have hcoeff := (r11b_memLp_angularCoefficient hf he).1
  have hweighted : MemLp
      (fun r => sqrt ((D.w r)⁻¹) * angularAverage (fun θ => f (r, θ) * e θ))
      2 (volume.restrict (radialCore D)) := by
    simpa only [mul_assoc, r11b_angularAverage_const_mul] using hcoeff
  have hquot := r11b_memLp_div_radialDensity_of_inverse_sqrt hgeom hweighted
  simpa only [neg_div, Pi.neg_apply] using hquot.neg

theorem r11b_sourceCoefficient_memLp_radialHilbert {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {γ M : ℝ} (hγ : 0 < γ)
    {F : RadialSource} (hF : SourceMember D γ M F)
    {e : ℝ → ℝ} (he : MemLp e 2 angularMeanMeasure) :
    MemLp (fun r => -angularAverage (fun θ => F.1 (r, θ) * e θ) /
      (12 * D.w r / r ^ 2)) 2 (radialHilbertMeasure D) := by
  have hf := r11b_source_inverse_sqrt_memLp hD hγ hF
  obtain ⟨_, hgeom, _⟩ := hD
  exact r11b_angularCoefficient_div_memLp_radialHilbert hgeom hf he

theorem r11b_sourceDerivativeCoefficient_memLp_radialHilbert {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {γ M : ℝ} (hγ : 0 < γ)
    {fθ : PolarPoint → ℝ} (hfθ : SourceDerivativeMember D γ M fθ)
    {e : ℝ → ℝ} (he : MemLp e 2 angularMeanMeasure) :
    MemLp (fun r => -angularAverage (fun θ => fθ (r, θ) * e θ) /
      (12 * D.w r / r ^ 2)) 2 (radialHilbertMeasure D) := by
  have hf := r11b_sourceDerivative_inverse_sqrt_memLp hD hγ hfθ
  obtain ⟨_, hgeom, _⟩ := hD
  exact r11b_angularCoefficient_div_memLp_radialHilbert hgeom hf he

theorem r11b_sourceMode_memLp_radialHilbert {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {γ M : ℝ} (hγ : 0 < γ)
    {F : RadialSource} (hF : SourceMember D γ M F) (j : ℕ) :
    MemLp (fun r => -referenceMode F.1 j r / (12 * D.w r / r ^ 2))
      2 (radialHilbertMeasure D) := by
  have he : MemLp (cosineMode j) 2 angularMeanMeasure :=
    memLp_angularMeanMeasure (angularInterval_memLp_of_continuous (by
      unfold cosineMode
      fun_prop))
  have h := r11b_sourceCoefficient_memLp_radialHilbert hD hγ hF he
  simpa only [referenceMode, radialAngularMean, angularAverage, one_div] using h

theorem r11b_sourceMean_memLp_radialHilbert {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {γ M : ℝ} (hγ : 0 < γ)
    {F : RadialSource} (hF : SourceMember D γ M F) :
    MemLp (fun r => -radialAngularMean (fun θ => F.1 (r, θ)) /
      (12 * D.w r / r ^ 2)) 2 (radialHilbertMeasure D) := by
  have h := r11b_sourceCoefficient_memLp_radialHilbert hD hγ hF
    (memLp_const (1 : ℝ) : MemLp (fun _ : ℝ => (1 : ℝ)) 2 angularMeanMeasure)
  simpa only [mul_one, radialAngularMean, angularAverage, one_div] using h

theorem r11b_outputMode_memLp_radialHilbert {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    {γ M : ℝ} (hγ : 0 < γ) {U : RadialUnknown} (hU : OutputMember D γ M U)
    (j : ℕ) (hj : 0 < j) :
    MemLp (referenceMode U.1 j) 2 (radialHilbertMeasure D) := by
  have hf := r11b_output_memLp hD hborder hγ hU
  obtain ⟨_, hgeom, _⟩ := hD
  exact r11b_memLp_radialHilbert_of_memLp hgeom (r11b_referenceMode_L2_bound hf j hj).1

theorem r11b_outputMean_memLp_radialHilbert {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    {γ M : ℝ} (hγ : 0 < γ) {U : RadialUnknown} (hU : OutputMember D γ M U) :
    MemLp (fun r => radialAngularMean (fun θ => U.1 (r, θ)))
      2 (radialHilbertMeasure D) := by
  have hf := r11b_output_memLp hD hborder hγ hU
  obtain ⟨_, hgeom, _⟩ := hD
  exact r11b_memLp_radialHilbert_of_memLp hgeom (r11b_radialAngularMean_L2_bound hf).1

end ContinuousFlexibility.Radial
