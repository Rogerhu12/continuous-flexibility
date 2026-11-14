module

public import ContinuousFlexibility.Scalar.HeightDerivatives
public import ContinuousFlexibility.Scalar.ConnectionVariation
public import Mathlib.Analysis.Calculus.LineDeriv.Basic
public import Mathlib.Tactic.Linarith

/-!
# Exterior derivative of the actual height connection

This module binds the parameter differentiation rules to actual coordinate
derivatives. The curl is the coefficient of `dr ∧ dθ` in the exterior
derivative of the displayed one-form. No formal jet is substituted for a
partial derivative. The Cartan structure equations are a separate step.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility

set_option backward.isDefEq.respectTransparency false

def connectionRadialField (E k p : PolarPoint → ℝ) (x : PolarPoint) : ℝ :=
  connectionRadialValue (E x) (k x) (p x) (radialPartial p x)

def connectionAngularField (E k p : PolarPoint → ℝ) (x : PolarPoint) : ℝ :=
  connectionAngularValue (E x) (k x) (p x) (angularPartial p x)

/-- The coefficient of `dr ∧ dθ` in the exterior derivative. -/
def connectionCurl (E k p : PolarPoint → ℝ) (x : PolarPoint) : ℝ :=
  radialPartial (connectionAngularField E k p) x -
    angularPartial (connectionRadialField E k p) x

theorem differentiableAt_connectionInverseRoot
    {E k p : PolarPoint → ℝ} {x : PolarPoint}
    (hE : DifferentiableAt ℝ E x) (hk : DifferentiableAt ℝ k x)
    (hp : DifferentiableAt ℝ p x)
    (hD : 0 < heightDiscriminant (E x) (k x) (p x)) :
    DifferentiableAt ℝ (fun y => connectionInverseRoot (E y) (k y) (p y)) x := by
  have hd : DifferentiableAt ℝ
      (fun y => heightDiscriminant (E y) (k y) (p y)) x :=
    (hE.mul ((hp.pow 2).const_sub 1)).sub (hk.pow 2)
  have hi := (hasDerivAt_inv (Real.sqrt_pos.mpr hD).ne').hasFDerivAt.comp x
    (hd.sqrt hD.ne').hasFDerivAt
  convert hi.differentiableAt using 1
  funext y
  simp only [connectionInverseRoot, Function.comp_apply, one_div]

theorem differentiableAt_connectionB1
    {E k p : PolarPoint → ℝ} {x : PolarPoint}
    (hE : DifferentiableAt ℝ E x) (hk : DifferentiableAt ℝ k x)
    (hp : DifferentiableAt ℝ p x)
    (hD : 0 < heightDiscriminant (E x) (k x) (p x)) :
    DifferentiableAt ℝ (fun y => connectionB1 (E y) (k y) (p y)) x := by
  have hd : DifferentiableAt ℝ
      (fun y => heightDiscriminant (E y) (k y) (p y)) x :=
    (hE.mul ((hp.pow 2).const_sub 1)).sub (hk.pow 2)
  have hden := ((hp.pow 2).const_sub 1).mul (hd.sqrt hD.ne')
  have hi := (hasDerivAt_inv
    (mul_ne_zero (angular_factor_ne_zero_of_discriminant_pos hD)
      (Real.sqrt_pos.mpr hD).ne')).hasFDerivAt.comp x hden.hasFDerivAt
  convert (hk.mul hi.differentiableAt) using 1
  funext y
  simp only [connectionB1, div_eq_mul_inv, Pi.mul_apply,
    Pi.pow_apply, Function.comp_apply]

/-- Actual directional derivative of the radial connection coefficient. -/
theorem fderiv_connectionRadialField
    {E k p : PolarPoint → ℝ} {x : PolarPoint}
    (hE : DifferentiableAt ℝ E x) (hk : DifferentiableAt ℝ k x)
    (hp : DifferentiableAt ℝ p x)
    (hpr : DifferentiableAt ℝ (radialPartial p) x)
    (hD : 0 < heightDiscriminant (E x) (k x) (p x)) (v : PolarPoint) :
    fderiv ℝ (connectionRadialField E k p) x v =
      connectionB1Variation (E x) (k x) (p x)
        (fderiv ℝ E x v) (fderiv ℝ k x v) (fderiv ℝ p x v) * radialPartial p x +
        connectionB1 (E x) (k x) (p x) * fderiv ℝ (radialPartial p) x v := by
  have hfield : DifferentiableAt ℝ (connectionRadialField E k p) x :=
    (differentiableAt_connectionB1 hE hk hp hD).mul hpr
  have hcurve := hasDerivAt_connectionRadialValue
    (hE.hasFDerivAt.hasLineDerivAt v) (hk.hasFDerivAt.hasLineDerivAt v)
    (hp.hasFDerivAt.hasLineDerivAt v) (hpr.hasFDerivAt.hasLineDerivAt v)
    (by simpa only [zero_smul, add_zero] using hD)
  simpa only [zero_smul, add_zero] using
    (hfield.hasFDerivAt.hasLineDerivAt v).unique hcurve

/-- Actual directional derivative of the angular connection coefficient. -/
theorem fderiv_connectionAngularField
    {E k p : PolarPoint → ℝ} {x : PolarPoint}
    (hE : DifferentiableAt ℝ E x) (hk : DifferentiableAt ℝ k x)
    (hp : DifferentiableAt ℝ p x)
    (hpt : DifferentiableAt ℝ (angularPartial p) x)
    (hD : 0 < heightDiscriminant (E x) (k x) (p x)) (v : PolarPoint) :
    fderiv ℝ (connectionAngularField E k p) x v =
      -discriminantVariation (E x) (k x) (p x)
        (fderiv ℝ E x v) (fderiv ℝ k x v) (fderiv ℝ p x v) *
          inverseDThreeHalves (heightDiscriminant (E x) (k x) (p x)) / 2 +
        (connectionB1Variation (E x) (k x) (p x)
          (fderiv ℝ E x v) (fderiv ℝ k x v) (fderiv ℝ p x v) * angularPartial p x +
          connectionB1 (E x) (k x) (p x) * fderiv ℝ (angularPartial p) x v) := by
  have hfield : DifferentiableAt ℝ (connectionAngularField E k p) x :=
    (differentiableAt_connectionInverseRoot hE hk hp hD).add
      ((differentiableAt_connectionB1 hE hk hp hD).mul hpt)
  have hcurve := hasDerivAt_connectionAngularValue
    (hE.hasFDerivAt.hasLineDerivAt v) (hk.hasFDerivAt.hasLineDerivAt v)
    (hp.hasFDerivAt.hasLineDerivAt v) (hpt.hasFDerivAt.hasLineDerivAt v)
    (by simpa only [zero_smul, add_zero] using hD)
  simpa only [zero_smul, add_zero] using
    (hfield.hasFDerivAt.hasLineDerivAt v).unique hcurve

/-- The second derivatives of `p` cancel by actual mixed-partial symmetry. -/
theorem connectionCurl_expansion
    {E k p : PolarPoint → ℝ} {x : PolarPoint}
    (hE : DifferentiableAt ℝ E x) (hk : DifferentiableAt ℝ k x)
    (hp : ContDiffAt ℝ 2 p x)
    (hD : 0 < heightDiscriminant (E x) (k x) (p x)) :
    connectionCurl E k p x =
      -discriminantVariation (E x) (k x) (p x)
        (radialPartial E x) (radialPartial k x) (radialPartial p x) *
          inverseDThreeHalves (heightDiscriminant (E x) (k x) (p x)) / 2 +
        connectionB1Variation (E x) (k x) (p x)
          (radialPartial E x) (radialPartial k x) (radialPartial p x) * angularPartial p x -
        connectionB1Variation (E x) (k x) (p x)
          (angularPartial E x) (angularPartial k x) (angularPartial p x) * radialPartial p x := by
  have hp0 := hp.differentiableAt two_ne_zero
  have hpr := (contDiffAt_radialPartial hp (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hpt := (contDiffAt_angularPartial hp (m := 1) (by norm_num)).differentiableAt one_ne_zero
  unfold connectionCurl
  change fderiv ℝ (connectionAngularField E k p) x (1, 0) -
    fderiv ℝ (connectionRadialField E k p) x (0, 1) = _
  rw [fderiv_connectionAngularField hE hk hp0 hpt hD,
    fderiv_connectionRadialField hE hk hp0 hpr hD]
  have hm : fderiv ℝ (angularPartial p) x (1, 0) =
      fderiv ℝ (radialPartial p) x (0, 1) := radial_angular_commute hp
  rw [hm]
  unfold radialPartial angularPartial
  ring

/-- The manuscript's numerator, now for the curl of actual functions. -/
theorem connectionCurl_eq_scaledNumerator
    {E k p : PolarPoint → ℝ} {x : PolarPoint}
    (hE : DifferentiableAt ℝ E x) (hk : DifferentiableAt ℝ k x)
    (hp : ContDiffAt ℝ 2 p x)
    (hD : 0 < heightDiscriminant (E x) (k x) (p x))
    (hEt : angularPartial E x = 0)
    (hcompat : angularPartial k x = p x + x.1 * radialPartial p x) :
    connectionCurl E k p x =
      inverseDThreeHalves (heightDiscriminant (E x) (k x) (p x)) *
        darbouxNumerator x.1 (E x) (radialPartial E x) (k x) (p x)
          (radialPartial k x) (radialPartial p x) (angularPartial p x) := by
  rw [connectionCurl_expansion hE hk hp hD, hEt, hcompat]
  unfold discriminantVariation connectionB1Variation darbouxNumerator heightQ
  ring

/-- The connection numerator evaluated on an actual height and profile. -/
def polarCurvatureNumerator (w : ℝ → ℝ) (z : PolarPoint → ℝ) (x : PolarPoint) : ℝ :=
  darbouxNumerator x.1 (profileEnergy w x) (radialPartial (profileEnergy w) x)
    (heightRadial z x) (heightAngular z x) (radialPartial (heightRadial z) x)
    (radialPartial (heightAngular z) x) (angularPartial (heightAngular z) x)

/-- The actual coordinate residual; its geometric interpretation is supplied
by the Cartan structure equations, not by its name. -/
def polarCoordinateResidual (w : ℝ → ℝ) (z : PolarPoint → ℝ) (x : PolarPoint) : ℝ :=
  polarCurvatureNumerator w z x * inverseDThreeHalves (polarDiscriminant w z x) / x.1

/-- Section 3's `dα = r N dr ∧ dθ`, for actual smooth height functions. -/
theorem polar_connectionCurl_eq_residual
    {w : ℝ → ℝ} {z : PolarPoint → ℝ} {x : PolarPoint}
    (hw : DifferentiableAt ℝ w x.1) (hz : ContDiffAt ℝ 3 z x)
    (hr : x.1 ≠ 0) (hD : 0 < polarDiscriminant w z x) :
    connectionCurl (profileEnergy w) (heightRadial z) (heightAngular z) x =
      x.1 * polarCoordinateResidual w z x := by
  have hE : DifferentiableAt ℝ (profileEnergy w) x :=
    ((hw.comp x differentiableAt_fst).pow 2).const_add 1
  have hk := (contDiffAt_heightRadial hz (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hp := contDiffAt_heightAngular hz (m := 2) (by norm_num) hr
  have hc := height_compatibility (hz.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)) hr
  have hcompat : angularPartial (heightRadial z) x =
      heightAngular z x + x.1 * radialPartial (heightAngular z) x := by linarith
  rw [connectionCurl_eq_scaledNumerator hE hk hp hD (angularPartial_profileEnergy hw) hcompat]
  unfold polarCoordinateResidual polarCurvatureNumerator polarDiscriminant
  field_simp [hr]

/-- Vanishing of the actual scalar residual is exactly closedness of the
displayed connection, at a positive-discriminant point. -/
theorem polar_connection_closed_iff
    {w : ℝ → ℝ} {z : PolarPoint → ℝ} {x : PolarPoint}
    (hw : DifferentiableAt ℝ w x.1) (hz : ContDiffAt ℝ 3 z x)
    (hr : x.1 ≠ 0) (hD : 0 < polarDiscriminant w z x) :
    connectionCurl (profileEnergy w) (heightRadial z) (heightAngular z) x = 0 ↔
      polarCoordinateResidual w z x = 0 := by
  rw [polar_connectionCurl_eq_residual hw hz hr hD, mul_eq_zero]
  simp [hr]

end ContinuousFlexibility
