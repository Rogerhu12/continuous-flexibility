module

public import ContinuousFlexibility.Scalar.Connection
public import ContinuousFlexibility.Scalar.CoframeDerivatives

/-!
# Cartan structure equations of the actual remainder coframe

With `η₁=A dr`, `η₂=B dr+C dθ`, the manuscript's convention is
`dη₁=α∧η₂` and `dη₂=-α∧η₁`. The two theorems below prove these
equations for actual differentiable height functions.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility

set_option backward.isDefEq.respectTransparency false

def coframeAField (E k p : PolarPoint → ℝ) (x : PolarPoint) : ℝ :=
  coframeAValue (E x) (k x) (p x)

def coframeBField (k p : PolarPoint → ℝ) (x : PolarPoint) : ℝ :=
  coframeBValue (k x) (p x)

def coframeCField (p : PolarPoint → ℝ) (x : PolarPoint) : ℝ :=
  coframeCValue x.1 (p x)

theorem polar_differentiableAt_div {f g : PolarPoint → ℝ} {x : PolarPoint}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (hg0 : g x ≠ 0) :
    DifferentiableAt ℝ (fun y => f y / g y) x := by
  have hi := (hasDerivAt_inv hg0).hasFDerivAt.comp x hg.hasFDerivAt
  convert (hf.mul hi.differentiableAt) using 1
  funext y
  rfl

theorem differentiableAt_coframeAField
    {E k p : PolarPoint → ℝ} {x : PolarPoint}
    (hE : DifferentiableAt ℝ E x) (hk : DifferentiableAt ℝ k x)
    (hp : DifferentiableAt ℝ p x)
    (hD : 0 < heightDiscriminant (E x) (k x) (p x)) (hc : 0 < 1 - p x ^ 2) :
    DifferentiableAt ℝ (coframeAField E k p) x := by
  have hd : DifferentiableAt ℝ
      (fun y => heightDiscriminant (E y) (k y) (p y)) x :=
    (hE.mul ((hp.pow 2).const_sub 1)).sub (hk.pow 2)
  exact polar_differentiableAt_div (hd.sqrt hD.ne')
    (((hp.pow 2).const_sub 1).sqrt hc.ne') (Real.sqrt_pos.mpr hc).ne'

theorem differentiableAt_coframeBField
    {k p : PolarPoint → ℝ} {x : PolarPoint}
    (hk : DifferentiableAt ℝ k x) (hp : DifferentiableAt ℝ p x)
    (hc : 0 < 1 - p x ^ 2) :
    DifferentiableAt ℝ (coframeBField k p) x :=
  polar_differentiableAt_div (hk.neg.mul hp) (((hp.pow 2).const_sub 1).sqrt hc.ne')
    (Real.sqrt_pos.mpr hc).ne'

theorem differentiableAt_coframeCField
    {p : PolarPoint → ℝ} {x : PolarPoint}
    (hp : DifferentiableAt ℝ p x) (hc : 0 < 1 - p x ^ 2) :
    DifferentiableAt ℝ (coframeCField p) x :=
  differentiableAt_fst.mul (((hp.pow 2).const_sub 1).sqrt hc.ne')

theorem fderiv_coframeAField
    {E k p : PolarPoint → ℝ} {x : PolarPoint}
    (hE : DifferentiableAt ℝ E x) (hk : DifferentiableAt ℝ k x)
    (hp : DifferentiableAt ℝ p x)
    (hD : 0 < heightDiscriminant (E x) (k x) (p x)) (hc : 0 < 1 - p x ^ 2)
    (v : PolarPoint) :
    fderiv ℝ (coframeAField E k p) x v =
      coframeAVariation (E x) (k x) (p x)
        (fderiv ℝ E x v) (fderiv ℝ k x v) (fderiv ℝ p x v) := by
  have hfield : DifferentiableAt ℝ (coframeAField E k p) x :=
    differentiableAt_coframeAField hE hk hp hD hc
  have hcurve := hasDerivAt_coframeAValue
    (hE.hasFDerivAt.hasLineDerivAt v) (hk.hasFDerivAt.hasLineDerivAt v)
    (hp.hasFDerivAt.hasLineDerivAt v)
    (by simpa only [zero_smul, add_zero] using hD)
    (by simpa only [zero_smul, add_zero] using hc)
  simpa only [zero_smul, add_zero] using
    (hfield.hasFDerivAt.hasLineDerivAt v).unique hcurve

theorem fderiv_coframeBField
    {k p : PolarPoint → ℝ} {x : PolarPoint}
    (hk : DifferentiableAt ℝ k x) (hp : DifferentiableAt ℝ p x)
    (hc : 0 < 1 - p x ^ 2) (v : PolarPoint) :
    fderiv ℝ (coframeBField k p) x v =
      coframeBVariation (k x) (p x) (fderiv ℝ k x v) (fderiv ℝ p x v) := by
  have hfield : DifferentiableAt ℝ (coframeBField k p) x :=
    differentiableAt_coframeBField hk hp hc
  have hcurve := hasDerivAt_coframeBValue
    (hk.hasFDerivAt.hasLineDerivAt v) (hp.hasFDerivAt.hasLineDerivAt v)
    (by simpa only [zero_smul, add_zero] using hc)
  simpa only [zero_smul, add_zero] using
    (hfield.hasFDerivAt.hasLineDerivAt v).unique hcurve

theorem fderiv_coframeCField
    {p : PolarPoint → ℝ} {x : PolarPoint}
    (hp : DifferentiableAt ℝ p x) (hc : 0 < 1 - p x ^ 2) (v : PolarPoint) :
    fderiv ℝ (coframeCField p) x v =
      coframeCVariation x.1 (p x) v.1 (fderiv ℝ p x v) := by
  have hfield : DifferentiableAt ℝ (coframeCField p) x :=
    differentiableAt_coframeCField hp hc
  have hfst : DifferentiableAt ℝ (Prod.fst : PolarPoint → ℝ) x := differentiableAt_fst
  have hcurve := hasDerivAt_coframeCValue
    (hfst.hasFDerivAt.hasLineDerivAt v)
    (hp.hasFDerivAt.hasLineDerivAt v)
    (by simpa only [zero_smul, add_zero] using hc)
  simpa only [zero_smul, add_zero, fderiv_fst, ContinuousLinearMap.coe_fst'] using
    (hfield.hasFDerivAt.hasLineDerivAt v).unique hcurve

/-- Algebraic reduction after the actual derivative rules have been applied. -/
theorem cartan_first_algebra {r E k p kt pr pt : ℝ}
    (hD : 0 < heightDiscriminant E k p) (hc : 0 < 1 - p ^ 2)
    (hcompat : kt = p + r * pr) :
    -coframeAVariation E k p 0 kt pt =
      connectionRadialValue E k p pr * coframeCValue r p -
        connectionAngularValue E k p pt * coframeBValue k p := by
  rw [hcompat]
  unfold coframeAVariation discriminantVariation connectionRadialValue
    connectionAngularValue connectionInverseRoot connectionB1 coframeCValue coframeBValue
  field_simp [hc.ne', (Real.sqrt_pos.mpr hc).ne', (Real.sqrt_pos.mpr hD).ne']
  simp only [Real.sq_sqrt hD.le, Real.sq_sqrt hc.le]
  unfold heightDiscriminant
  ring

/-- The second Cartan equation, with the manuscript's orientation convention. -/
theorem cartan_second_algebra {r E k p kt pr pt : ℝ}
    (hD : 0 < heightDiscriminant E k p) (hc : 0 < 1 - p ^ 2)
    (hcompat : kt = p + r * pr) :
    coframeCVariation r p 1 pr - coframeBVariation k p kt pt =
      coframeAValue E k p * connectionAngularValue E k p pt := by
  rw [hcompat]
  unfold coframeCVariation coframeBVariation coframeAValue connectionAngularValue
    connectionInverseRoot connectionB1
  field_simp [hc.ne', (Real.sqrt_pos.mpr hc).ne', (Real.sqrt_pos.mpr hD).ne']
  simp only [Real.sq_sqrt hc.le]
  ring

theorem cartan_first
    {E k p : PolarPoint → ℝ} {x : PolarPoint}
    (hE : DifferentiableAt ℝ E x) (hk : DifferentiableAt ℝ k x)
    (hp : DifferentiableAt ℝ p x)
    (hD : 0 < heightDiscriminant (E x) (k x) (p x)) (hc : 0 < 1 - p x ^ 2)
    (hEt : angularPartial E x = 0)
    (hcompat : angularPartial k x = p x + x.1 * radialPartial p x) :
    -angularPartial (coframeAField E k p) x =
      connectionRadialField E k p x * coframeCField p x -
        connectionAngularField E k p x * coframeBField k p x := by
  change -fderiv ℝ (coframeAField E k p) x (0, 1) = _
  rw [fderiv_coframeAField hE hk hp hD hc]
  change -coframeAVariation (E x) (k x) (p x)
    (angularPartial E x) (angularPartial k x) (angularPartial p x) = _
  rw [hEt]
  exact cartan_first_algebra hD hc hcompat

theorem cartan_second
    {E k p : PolarPoint → ℝ} {x : PolarPoint}
    (hk : DifferentiableAt ℝ k x) (hp : DifferentiableAt ℝ p x)
    (hD : 0 < heightDiscriminant (E x) (k x) (p x)) (hc : 0 < 1 - p x ^ 2)
    (hcompat : angularPartial k x = p x + x.1 * radialPartial p x) :
    radialPartial (coframeCField p) x - angularPartial (coframeBField k p) x =
      coframeAField E k p x * connectionAngularField E k p x := by
  change fderiv ℝ (coframeCField p) x (1, 0) -
    fderiv ℝ (coframeBField k p) x (0, 1) = _
  rw [fderiv_coframeCField hp hc, fderiv_coframeBField hk hp hc]
  exact cartan_second_algebra hD hc hcompat

/-- Both Cartan equations for the actual coframe of `g - dz²`. -/
theorem polar_cartan_equations
    {w : ℝ → ℝ} {z : PolarPoint → ℝ} {x : PolarPoint}
    (hw : DifferentiableAt ℝ w x.1) (hz : ContDiffAt ℝ 2 z x)
    (hr : x.1 ≠ 0) (hD : 0 < polarDiscriminant w z x) :
    let E := profileEnergy w
    let k := heightRadial z
    let p := heightAngular z;
    -angularPartial (coframeAField E k p) x =
        connectionRadialField E k p x * coframeCField p x -
          connectionAngularField E k p x * coframeBField k p x ∧
      radialPartial (coframeCField p) x - angularPartial (coframeBField k p) x =
        coframeAField E k p x * connectionAngularField E k p x := by
  dsimp only
  have hE : DifferentiableAt ℝ (profileEnergy w) x :=
    ((hw.comp x differentiableAt_fst).pow 2).const_add 1
  have hk := (contDiffAt_heightRadial hz (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hp := (contDiffAt_heightAngular hz (m := 1) (by norm_num) hr).differentiableAt one_ne_zero
  have hc := angular_factor_pos_of_discriminant_pos (radialEnergy_pos (w x.1)) hD
  have hcomp := height_compatibility hz hr
  have hcompat : angularPartial (heightRadial z) x =
      heightAngular z x + x.1 * radialPartial (heightAngular z) x := by linarith
  exact ⟨cartan_first hE hk hp hD hc (angularPartial_profileEnergy hw) hcompat,
    cartan_second hk hp hD hc hcompat⟩

/-- Nondegeneracy and orientation of the displayed coframe at positive radius. -/
theorem polar_coframe_determinant_pos
    {w : ℝ → ℝ} {z : PolarPoint → ℝ} {x : PolarPoint}
    (hr : 0 < x.1) (hD : 0 < polarDiscriminant w z x) :
    0 < coframeAField (profileEnergy w) (heightRadial z) (heightAngular z) x *
      coframeCField (heightAngular z) x := by
  have hc := angular_factor_pos_of_discriminant_pos (radialEnergy_pos (w x.1)) hD
  unfold coframeAField coframeCField
  rw [coframeAValue_mul_CValue hc]
  exact mul_pos hr (Real.sqrt_pos.mpr hD)

end ContinuousFlexibility
