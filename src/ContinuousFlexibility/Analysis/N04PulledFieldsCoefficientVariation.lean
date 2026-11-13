import ContinuousFlexibility.Analysis.N04bOpticalHeightVariation

/-!
# Sensitivity of the actual radial coefficient to a height direction

The coefficient here is `polarLinearA` itself.  Its derivative at the
radial reference is obtained from the actual height-family derivative
and the positive-discriminant normalization.  A radial test can have
zero first derivative and nonzero second derivative at an interior
point.  The last lemma records the effect of a fixed change of radial
coordinate on this response, without assuming any estimate for it.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements ContinuousFlexibility.Radial
open scoped ContDiff

/-- The actual first height variation of the radial principal coefficient.
The reference profile and the reference primitive are retained. -/
theorem n04PulledFields_hasDerivAt_radialCoefficient
    {h w : ℝ → ℝ} {u : PolarPoint → ℝ} {x : PolarPoint}
    (hh : ContDiff ℝ ∞ h) (hhw : ∀ r, HasDerivAt h (w r) r)
    (hu : ContDiff ℝ ∞ u) (hr : x.1 ≠ 0) :
    HasDerivAt
      (fun q => polarLinearA w (heightFamily (radialHeightField h) u q) x)
      ((1 + 3 * w x.1 ^ 2) * heightRadial u x +
        profileEnergy w x * angularPartial (heightAngular u) x) 0 := by
  have hH : ContDiff ℝ ∞ (radialHeightField h) := contDiff_radialHeightField hh
  have hD := hasDerivAt_polarDiscriminant_heightFamily w hH hu x
  have hQ := n04b_hasDerivAt_heightQ_heightFamily w hH hu hr
  have hD0 : polarDiscriminant w (heightFamily (radialHeightField h) u 0) x = 1 := by
    rw [heightFamily_zero, polarDiscriminant_radialHeightField hhw]
  have hQ0 : heightQ (profileEnergy w x)
      (heightRadial (heightFamily (radialHeightField h) u 0) x)
      (angularPartial (heightAngular (heightFamily (radialHeightField h) u 0)) x) =
        w x.1 := by
    rw [heightFamily_zero, n04b_heightQ_radialHeightField hhw]
  have hscale := hasDerivAt_inverseDThreeHalves hD (by rw [hD0]; exact zero_lt_one)
  change HasDerivAt
    (fun q => heightQ (profileEnergy w x)
      (heightRadial (heightFamily (radialHeightField h) u q) x)
      (angularPartial (heightAngular (heightFamily (radialHeightField h) u q)) x) *
        inverseDThreeHalves
          (polarDiscriminant w (heightFamily (radialHeightField h) u q) x)) _ 0
  apply (hQ.mul hscale).congr_deriv
  simp only [hD0, hQ0, inverseDThreeHalves_one, polarDiscriminantVariation,
    heightAngular_radialHeightField hhw, heightRadial_radialHeightField hhw,
    radialHeightField, mul_zero, zero_mul, zero_sub]
  ring

/-- A radial height direction changes the coefficient by
`(1 + 3*w^2) * f'` at the reference parameter. -/
theorem n04PulledFields_hasDerivAt_radialCoefficient_radialIncrement
    {h w f : ℝ → ℝ} {x : PolarPoint}
    (hh : ContDiff ℝ ∞ h) (hhw : ∀ r, HasDerivAt h (w r) r)
    (hf : ContDiff ℝ ∞ f) (hr : x.1 ≠ 0) :
    HasDerivAt (fun q => polarLinearA w
      (heightFamily (radialHeightField h) (radialHeightField f) q) x)
      ((1 + 3 * w x.1 ^ 2) * deriv f x.1) 0 := by
  have hff (r : ℝ) : HasDerivAt f (deriv f r) r :=
    (hf.differentiable (by simp) r).hasDerivAt
  apply (n04PulledFields_hasDerivAt_radialCoefficient hh hhw
    (contDiff_radialHeightField hf) hr).congr_deriv
  rw [heightAngular_radialHeightField hff, angularPartial_const,
    heightRadial_radialHeightField hff]
  simp only [radialHeightField, mul_zero, add_zero]

/-- A stationary first jet of a radial test isolates a strictly positive
response in the next radial derivative. -/
theorem n04PulledFields_radialCoefficientResponse_hasDerivAt
    {w f : ℝ → ℝ} {r : ℝ}
    (hw : DifferentiableAt ℝ w r) (hf : HasDerivAt (deriv f) 1 r)
    (hf0 : deriv f r = 0) :
    HasDerivAt (fun s => (1 + 3 * w s ^ 2) * deriv f s)
      (1 + 3 * w r ^ 2) r := by
  have hd := ((hw.hasDerivAt.pow 2).const_mul 3).const_add 1
  simpa only [hf0, mul_zero, mul_one, zero_add] using hd.mul hf

/-- A fixed coordinate change multiplies this nonzero response by its
inverse slope.  A bound for current-minus-reference coordinate jets
alone cannot bound the factor displayed here. -/
theorem n04PulledFields_radialCoefficientResponse_comp_hasDerivAt
    {w f g : ℝ → ℝ} {y d : ℝ}
    (hw : DifferentiableAt ℝ w (g y))
    (hf : HasDerivAt (deriv f) 1 (g y)) (hf0 : deriv f (g y) = 0)
    (hg : HasDerivAt g d y) :
    HasDerivAt (fun s => (1 + 3 * w (g s) ^ 2) * deriv f (g s))
      ((1 + 3 * w (g y) ^ 2) * d) y :=
  (n04PulledFields_radialCoefficientResponse_hasDerivAt hw hf hf0).comp y hg

theorem n04PulledFields_radialCoefficientResponse_pos (w : ℝ) :
    0 < 1 + 3 * w ^ 2 := by positivity

end ContinuousFlexibility.Analysis
