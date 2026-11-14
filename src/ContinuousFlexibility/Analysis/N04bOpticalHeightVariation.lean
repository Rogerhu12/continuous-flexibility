module

public import ContinuousFlexibility.Scalar.S05CalculusProof
public import ContinuousFlexibility.Radial.RadialHeight
public import ContinuousFlexibility.Analysis.OpticalTravelVariation

/-!
# Optical variation along actual height perturbations

The height is the genuine affine family `h(r) + q * u(r, θ)` at fixed profile
`w = h'`. The first variation below differentiates the actual characteristic
speed already identified with the corrected principal coefficients by S05.
It is different from varying the metric profile in `opticalLogPerturbation`.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open ContinuousFlexibility.Radial
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

/-- The positive radial factor in the characteristic-speed formula agrees
with the reference optical speed. -/
theorem n04b_characteristic_prefactor_eq {w : ℝ → ℝ} {r : ℝ}
    (hr : r ≠ 0) (hw : 0 < w r) :
    Real.sqrt (-w r * deriv w r / r) = w r * opticalSpeed w r := by
  have heq : -w r * deriv w r / r =
      w r ^ 2 * (-deriv w r / (r * w r)) := by
    field_simp [hr, hw.ne']
    <;> ring
  rw [heq, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs, abs_of_pos hw]
  rfl

/-- At a genuine radial primitive, the characteristic denominator is `w`. -/
theorem n04b_heightQ_radialHeightField {h w : ℝ → ℝ}
    (hhw : ∀ r, HasDerivAt h (w r) r) (x : PolarPoint) :
    heightQ (profileEnergy w x) (heightRadial (radialHeightField h) x)
      (angularPartial (heightAngular (radialHeightField h)) x) = w x.1 := by
  rw [heightRadial_radialHeightField hhw, heightAngular_radialHeightField hhw,
    angularPartial_const]
  simp only [heightQ, mul_zero, add_zero, radialHeightField]

/-- The derivative of the actual denominator uses actual spatial jets of
the increment, not an independently prescribed coefficient curve. -/
theorem n04b_hasDerivAt_heightQ_heightFamily (w : ℝ → ℝ)
    {z u : PolarPoint → ℝ} {x : PolarPoint}
    (hz : ContDiff ℝ ∞ z) (hu : ContDiff ℝ ∞ u) (hr : x.1 ≠ 0) :
    HasDerivAt (fun q => heightQ (profileEnergy w x)
      (heightRadial (heightFamily z u q) x)
      (angularPartial (heightAngular (heightFamily z u q)) x))
      (heightRadial u x + profileEnergy w x * angularPartial (heightAngular u) x) 0 := by
  exact (hasDerivAt_heightRadial_heightFamily hz hu x 0).add
    ((hasDerivAt_angularPartial_heightAngular_heightFamily hz hu hr 0).const_mul
      (profileEnergy w x))

/-- The characteristic speed is the actual positive square root of minus
the corrected determinant divided by its radial coefficient. -/
theorem n04b_characteristicSpeed_eq_corrected_ratio
    {w : ℝ → ℝ} {z : PolarPoint → ℝ} {x : PolarPoint}
    (hw : DifferentiableAt ℝ w x.1) (hr : 0 < x.1) (hwp : 0 < w x.1)
    (hwn : deriv w x.1 < 0) (hD : 0 < polarDiscriminant w z x)
    (hQ : 0 < heightQ (profileEnergy w x) (heightRadial z x)
      (angularPartial (heightAngular z) x)) :
    characteristicSpeed w z x =
      Real.sqrt (polarLinearB w z x ^ 2 - polarLinearA w z x * polarCorrectedC w z x) /
        polarLinearA w z x := by
  have ha : 0 < polarLinearA w z x := mul_pos hQ (inverseDThreeHalves_pos _ hD)
  have hrad : 0 < -w x.1 * deriv w x.1 / x.1 :=
    div_pos (mul_pos_of_neg_of_neg (neg_neg_of_pos hwp) hwn) hr
  have hv : 0 < characteristicSpeed w z x :=
    div_pos (mul_pos (Real.sqrt_pos.mpr hrad) (Real.sqrt_pos.mpr hD)) hQ
  have hs := polarLinearA_sq_mul_characteristicSpeed_sq hw hr hwp hwn hD hQ.ne'
  have heq : polarLinearB w z x ^ 2 - polarLinearA w z x * polarCorrectedC w z x =
      (polarLinearA w z x * characteristicSpeed w z x) ^ 2 := by
    rw [mul_pow, hs]
  rw [heq, Real.sqrt_sq (mul_pos ha hv).le]
  field_simp [ha.ne']

/-- The actual height perturbation changes optical speed through the radial
first derivative and the angular second derivative of the increment. -/
theorem n04b_hasDerivAt_characteristicSpeed_radialHeight
    {h w : ℝ → ℝ} {u : PolarPoint → ℝ} {x : PolarPoint}
    (hh : ContDiff ℝ ∞ h) (hhw : ∀ r, HasDerivAt h (w r) r)
    (hu : ContDiff ℝ ∞ u) (hr : 0 < x.1) (hwp : 0 < w x.1) :
    HasDerivAt
      (fun q => characteristicSpeed w (heightFamily (radialHeightField h) u q) x)
      (-opticalSpeed w x.1 * (1 + w x.1 ^ 2) / w x.1 *
        (radialPartial u x + angularPartial (angularPartial u) x / x.1)) 0 := by
  have hH := contDiff_radialHeightField hh
  have hD := hasDerivAt_polarDiscriminant_heightFamily w hH hu x
  have hQ := n04b_hasDerivAt_heightQ_heightFamily w hH hu hr.ne'
  have hD0 : polarDiscriminant w (heightFamily (radialHeightField h) u 0) x = 1 := by
    rw [heightFamily_zero, polarDiscriminant_radialHeightField hhw]
  have hQ0 : heightQ (profileEnergy w x)
      (heightRadial (heightFamily (radialHeightField h) u 0) x)
      (angularPartial (heightAngular (heightFamily (radialHeightField h) u 0)) x) =
      w x.1 := by
    rw [heightFamily_zero, n04b_heightQ_radialHeightField hhw]
  have hs := ((hD.sqrt (by rw [hD0]; exact one_ne_zero)).const_mul
    (Real.sqrt (-w x.1 * deriv w x.1 / x.1))).div hQ
      (by rw [hQ0]; exact hwp.ne')
  apply hs.congr_deriv
  simp only [hD0, hQ0, Real.sqrt_one, polarDiscriminantVariation,
    heightAngular_radialHeightField hhw, heightRadial_radialHeightField hhw,
    radialHeightField, mul_zero, zero_mul, zero_sub]
  rw [n04b_characteristic_prefactor_eq hr.ne' hwp,
    angularPartial_heightAngular_eq hu hr.ne']
  unfold profileEnergy radialEnergy heightRadial
  field_simp [hwp.ne']
  <;> ring

/-- The height variation weight for radial increments. -/
def n04bOpticalHeightWeight (w : ℝ → ℝ) (r : ℝ) : ℝ :=
  opticalSpeed w r * (1 + w r ^ 2) / w r

/-- For a radial height increment, the derivative is `-ω f'` with the
weight determined by the actual corrected operator. -/
theorem n04b_hasDerivAt_characteristicSpeed_radial_increment
    {h w f : ℝ → ℝ} {x : PolarPoint}
    (hh : ContDiff ℝ ∞ h) (hhw : ∀ r, HasDerivAt h (w r) r)
    (hf : ContDiff ℝ ∞ f) (hr : 0 < x.1) (hwp : 0 < w x.1) :
    HasDerivAt (fun q => characteristicSpeed w
      (heightFamily (radialHeightField h) (radialHeightField f) q) x)
      (-n04bOpticalHeightWeight w x.1 * deriv f x.1) 0 := by
  have hθ : angularPartial (radialHeightField f) = fun _ => 0 := by
    funext y
    exact angularPartial_radialHeightField (hf.differentiable (by simp) y.1)
  apply (n04b_hasDerivAt_characteristicSpeed_radialHeight hh hhw
    (contDiff_radialHeightField hf) hr hwp).congr_deriv
  rw [hθ, angularPartial_const, zero_div, add_zero,
    radialPartial_radialHeightField (hf.differentiable (by simp) x.1)]
  unfold n04bOpticalHeightWeight
  ring

end ContinuousFlexibility.Statements
