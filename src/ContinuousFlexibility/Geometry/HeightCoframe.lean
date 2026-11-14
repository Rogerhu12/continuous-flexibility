module

public import ContinuousFlexibility.Scalar.Cartan
public import ContinuousFlexibility.Geometry.RotatedCoframe

/-!
# The actual remainder coframe as coordinate one-forms

This binds the general one-form calculus to the coframe of `g - dz²`.
In particular, the Cartan premises of the rotation lemmas are proved here,
not assumed for the actual height. Primitive existence is a later step.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility

open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

def heightCoframeOne (w : ℝ → ℝ) (z : PolarPoint → ℝ) : PlaneOneForm :=
  ⟨coframeAField (profileEnergy w) (heightRadial z) (heightAngular z), fun _ => 0⟩

def heightCoframeTwo (_w : ℝ → ℝ) (z : PolarPoint → ℝ) : PlaneOneForm :=
  ⟨coframeBField (heightRadial z) (heightAngular z), coframeCField (heightAngular z)⟩

def heightConnectionForm (w : ℝ → ℝ) (z : PolarPoint → ℝ) : PlaneOneForm :=
  ⟨connectionRadialField (profileEnergy w) (heightRadial z) (heightAngular z),
    connectionAngularField (profileEnergy w) (heightRadial z) (heightAngular z)⟩

theorem heightCoframe_square_sum
    {w : ℝ → ℝ} {z : PolarPoint → ℝ} {x : PolarPoint}
    (hD : 0 < polarDiscriminant w z x) (v : PolarPoint) :
    formValue (heightCoframeOne w z) x v ^ 2 +
        formValue (heightCoframeTwo w z) x v ^ 2 =
      remainderQuadratic x.1 (profileEnergy w x) (heightRadial z x)
        (heightAngular z x) v.1 v.2 := by
  have h := coframe_square_sum (r := x.1) (radialEnergy_pos (w x.1)) hD v.1 v.2
  simpa only [coframeOne_eq_AValue, coframeTwo_eq_BCValue, heightCoframeOne,
    heightCoframeTwo, formValue, coframeAField, coframeBField, coframeCField,
    profileEnergy, zero_mul, add_zero] using h

theorem heightCoframe_wedge
    {w : ℝ → ℝ} {z : PolarPoint → ℝ} {x : PolarPoint}
    (hD : 0 < polarDiscriminant w z x) :
    wedgeCoefficient (heightCoframeOne w z) (heightCoframeTwo w z) x =
      x.1 * Real.sqrt (polarDiscriminant w z x) := by
  have hc := angular_factor_pos_of_discriminant_pos (radialEnergy_pos (w x.1)) hD
  simpa only [heightCoframeOne, heightCoframeTwo, wedgeCoefficient,
    coframeAField, coframeBField, coframeCField, zero_mul, sub_zero, polarDiscriminant] using
    coframeAValue_mul_CValue (r := x.1) hc

theorem heightCoframe_wedge_pos
    {w : ℝ → ℝ} {z : PolarPoint → ℝ} {x : PolarPoint}
    (hr : 0 < x.1) (hD : 0 < polarDiscriminant w z x) :
    0 < wedgeCoefficient (heightCoframeOne w z) (heightCoframeTwo w z) x := by
  rw [heightCoframe_wedge hD]
  exact mul_pos hr (Real.sqrt_pos.mpr hD)

theorem heightCoframe_cartan
    {w : ℝ → ℝ} {z : PolarPoint → ℝ} {x : PolarPoint}
    (hw : DifferentiableAt ℝ w x.1) (hz : ContDiffAt ℝ 2 z x)
    (hr : x.1 ≠ 0) (hD : 0 < polarDiscriminant w z x) :
    exteriorCoefficient (heightCoframeOne w z) x =
        wedgeCoefficient (heightConnectionForm w z) (heightCoframeTwo w z) x ∧
      exteriorCoefficient (heightCoframeTwo w z) x =
        -wedgeCoefficient (heightConnectionForm w z) (heightCoframeOne w z) x := by
  obtain ⟨h1, h2⟩ := polar_cartan_equations hw hz hr hD
  constructor
  · simpa [exteriorCoefficient, wedgeCoefficient, heightCoframeOne,
      heightCoframeTwo, heightConnectionForm] using h1
  · simpa [exteriorCoefficient, wedgeCoefficient, heightCoframeOne,
      heightCoframeTwo, heightConnectionForm, mul_comm] using h2

theorem heightConnection_exterior_eq_residual
    {w : ℝ → ℝ} {z : PolarPoint → ℝ} {x : PolarPoint}
    (hw : DifferentiableAt ℝ w x.1) (hz : ContDiffAt ℝ 3 z x)
    (hr : x.1 ≠ 0) (hD : 0 < polarDiscriminant w z x) :
    exteriorCoefficient (heightConnectionForm w z) x =
      x.1 * polarCoordinateResidual w z x :=
  polar_connectionCurl_eq_residual hw hz hr hD

theorem heightConnection_closed_of_residual_zero
    {w : ℝ → ℝ} {z : PolarPoint → ℝ} {x : PolarPoint}
    (hw : DifferentiableAt ℝ w x.1) (hz : ContDiffAt ℝ 3 z x)
    (hr : x.1 ≠ 0) (hD : 0 < polarDiscriminant w z x)
    (hres : polarCoordinateResidual w z x = 0) :
    exteriorCoefficient (heightConnectionForm w z) x = 0 := by
  rw [heightConnection_exterior_eq_residual hw hz hr hD, hres, mul_zero]

theorem contDiffAt_heightCoframeOne_radial
    {n : ℕ∞ω} {w : ℝ → ℝ} {z : PolarPoint → ℝ} {x : PolarPoint}
    (hw : ContDiffAt ℝ n w x.1) (hz : ContDiffAt ℝ (n + 1) z x)
    (hr : x.1 ≠ 0) (hD : 0 < polarDiscriminant w z x) :
    ContDiffAt ℝ n (heightCoframeOne w z).radial x := by
  have hE : ContDiffAt ℝ n (profileEnergy w) x :=
    contDiffAt_const.add ((hw.comp x contDiffAt_fst).pow 2)
  have hk := contDiffAt_heightRadial hz (m := n) le_rfl
  have hp := contDiffAt_heightAngular hz (m := n) le_rfl hr
  have hcp : ContDiffAt ℝ n (fun y => 1 - heightAngular z y ^ 2) x :=
    contDiffAt_const.sub (hp.pow 2)
  have hd := (hE.mul hcp).sub (hk.pow 2)
  have hc := angular_factor_pos_of_discriminant_pos (radialEnergy_pos (w x.1)) hD
  exact (hd.sqrt hD.ne').div (hcp.sqrt hc.ne')
    (Real.sqrt_pos.mpr hc).ne'

theorem contDiffAt_heightCoframeTwo_radial
    {n : ℕ∞ω} {w : ℝ → ℝ} {z : PolarPoint → ℝ} {x : PolarPoint}
    (hz : ContDiffAt ℝ (n + 1) z x) (hr : x.1 ≠ 0)
    (hD : 0 < polarDiscriminant w z x) :
    ContDiffAt ℝ n (heightCoframeTwo w z).radial x := by
  have hk := contDiffAt_heightRadial hz (m := n) le_rfl
  have hp := contDiffAt_heightAngular hz (m := n) le_rfl hr
  have hcp : ContDiffAt ℝ n (fun y => 1 - heightAngular z y ^ 2) x :=
    contDiffAt_const.sub (hp.pow 2)
  have hc := angular_factor_pos_of_discriminant_pos (radialEnergy_pos (w x.1)) hD
  exact (hk.neg.mul hp).div (hcp.sqrt hc.ne')
    (Real.sqrt_pos.mpr hc).ne'

theorem contDiffAt_heightCoframeTwo_angular
    {n : ℕ∞ω} {w : ℝ → ℝ} {z : PolarPoint → ℝ} {x : PolarPoint}
    (hz : ContDiffAt ℝ (n + 1) z x) (hr : x.1 ≠ 0)
    (hD : 0 < polarDiscriminant w z x) :
    ContDiffAt ℝ n (heightCoframeTwo w z).angular x := by
  have hp := contDiffAt_heightAngular hz (m := n) le_rfl hr
  have hcp : ContDiffAt ℝ n (fun y => 1 - heightAngular z y ^ 2) x :=
    contDiffAt_const.sub (hp.pow 2)
  have hc := angular_factor_pos_of_discriminant_pos (radialEnergy_pos (w x.1)) hD
  exact contDiffAt_fst.mul (hcp.sqrt hc.ne')

/-- When a genuine primitive of the connection has been obtained, the actual
remainder coframe rotates to two closed one-forms. Primitive existence is
not a premise of the final main theorem; it is supplied on suitable domains
by the Poincare step of the development construction. -/
theorem height_rotatedCoframe_closed
    {w : ℝ → ℝ} {z ψ : PolarPoint → ℝ} {x : PolarPoint}
    (hw : DifferentiableAt ℝ w x.1) (hz : ContDiffAt ℝ 2 z x)
    (hr : x.1 ≠ 0) (hD : 0 < polarDiscriminant w z x)
    (hψ : DifferentiableAt ℝ ψ x)
    (hψr : radialPartial ψ x = (heightConnectionForm w z).radial x)
    (hψt : angularPartial ψ x = (heightConnectionForm w z).angular x) :
    exteriorCoefficient (rotatedCoframeOne ψ (heightCoframeOne w z) (heightCoframeTwo w z)) x = 0 ∧
      exteriorCoefficient (rotatedCoframeTwo ψ (heightCoframeOne w z) (heightCoframeTwo w z)) x = 0 := by
  have hE : DifferentiableAt ℝ (profileEnergy w) x :=
    ((hw.comp x differentiableAt_fst).pow 2).const_add 1
  have hk := (contDiffAt_heightRadial hz (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hp := (contDiffAt_heightAngular hz (m := 1) (by norm_num) hr).differentiableAt one_ne_zero
  have hc := angular_factor_pos_of_discriminant_pos (radialEnergy_pos (w x.1)) hD
  have h1r := differentiableAt_coframeAField hE hk hp hD hc
  have h1t : DifferentiableAt ℝ (heightCoframeOne w z).angular x := differentiableAt_const _
  have h2r := differentiableAt_coframeBField hk hp hc
  have h2t := differentiableAt_coframeCField hp hc
  obtain ⟨hcartan1, hcartan2⟩ := heightCoframe_cartan hw hz hr hD
  have hc1 : exteriorCoefficient (heightCoframeOne w z) x =
      wedgeCoefficient (coordinateDifferential ψ) (heightCoframeTwo w z) x := by
    simpa only [wedgeCoefficient, coordinateDifferential, hψr, hψt] using hcartan1
  have hc2 : exteriorCoefficient (heightCoframeTwo w z) x =
      -wedgeCoefficient (coordinateDifferential ψ) (heightCoframeOne w z) x := by
    simpa only [wedgeCoefficient, coordinateDifferential, hψr, hψt] using hcartan2
  exact ⟨rotatedCoframeOne_closed hψ h1r h1t h2r h2t hc1 hc2,
    rotatedCoframeTwo_closed hψ h1r h1t h2r h2t hc1 hc2⟩

end ContinuousFlexibility
