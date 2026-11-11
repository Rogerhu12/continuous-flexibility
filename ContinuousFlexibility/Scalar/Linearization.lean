import ContinuousFlexibility.Scalar.LinearizationAlgebra
import Mathlib.Analysis.Calculus.FDeriv.Congr

/-!
# Divergence-form linearization of the actual height residual

The coefficients and all partial derivatives here are evaluated on actual
height and profile functions. The algebraic drift identities are used only
after the spatial derivative and mixed-partial identities have been proved.
-/

noncomputable section

namespace ContinuousFlexibility

open Filter
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

def polarScale (w : ℝ → ℝ) (z : PolarPoint → ℝ) (x : PolarPoint) : ℝ :=
  inverseDThreeHalves (polarDiscriminant w z x)

def polarLinearA (w : ℝ → ℝ) (z : PolarPoint → ℝ) (x : PolarPoint) : ℝ :=
  linearRadial (profileEnergy w x) (heightRadial z x)
    (angularPartial (heightAngular z) x) (polarScale w z x)

def polarLinearB (w : ℝ → ℝ) (z : PolarPoint → ℝ) (x : PolarPoint) : ℝ :=
  linearMixed (profileEnergy w x) (radialPartial (heightAngular z) x) (polarScale w z x)

def polarLinearC (w : ℝ → ℝ) (z : PolarPoint → ℝ) (x : PolarPoint) : ℝ :=
  linearAngular x.1 (profileEnergy w x) (radialPartial (profileEnergy w) x)
    (heightRadial z x) (radialPartial (heightRadial z) x) (polarScale w z x)

def heightLinearizedDivergence (w : ℝ → ℝ) (z η : PolarPoint → ℝ) (x : PolarPoint) : ℝ :=
  radialPartial (fun y => polarLinearA w z y * radialPartial η y +
      polarLinearB w z y * angularPartial η y) x +
    angularPartial (fun y => polarLinearB w z y * radialPartial η y +
      polarLinearC w z y * angularPartial η y) x

private theorem contDiff_profileEnergy_of_smooth {w : ℝ → ℝ} (hw : ContDiff ℝ ∞ w) :
    ContDiff ℝ ∞ (profileEnergy w) := by
  exact contDiff_const.add ((hw.comp contDiff_fst).pow 2)

private theorem differentiableAt_polarScale
    {w : ℝ → ℝ} {z : PolarPoint → ℝ} {x : PolarPoint}
    (hE : DifferentiableAt ℝ (profileEnergy w) x)
    (hk : DifferentiableAt ℝ (heightRadial z) x)
    (hp : DifferentiableAt ℝ (heightAngular z) x)
    (hpos : 0 < polarDiscriminant w z x) :
    DifferentiableAt ℝ (polarScale w z) x := by
  have hd : DifferentiableAt ℝ (polarDiscriminant w z) x :=
    (hE.mul ((hp.pow 2).const_sub 1)).sub (hk.pow 2)
  have hden := hd.mul (hd.sqrt hpos.ne')
  have hi := (hasDerivAt_inv (mul_ne_zero hpos.ne' (Real.sqrt_pos.mpr hpos).ne')).hasFDerivAt.comp x
    hden.hasFDerivAt
  convert hi.differentiableAt using 1
  funext y
  simp only [polarScale, inverseDThreeHalves, Function.comp_apply, Pi.mul_apply, one_div]

private structure LinearizationRegularAt (w : ℝ → ℝ) (z : PolarPoint → ℝ) (x : PolarPoint) : Prop where
  energy : DifferentiableAt ℝ (profileEnergy w) x
  energyRadial : DifferentiableAt ℝ (radialPartial (profileEnergy w)) x
  heightR : DifferentiableAt ℝ (heightRadial z) x
  heightRR : DifferentiableAt ℝ (radialPartial (heightRadial z)) x
  heightT : DifferentiableAt ℝ (heightAngular z) x
  heightTR : DifferentiableAt ℝ (radialPartial (heightAngular z)) x
  heightTT : DifferentiableAt ℝ (angularPartial (heightAngular z)) x
  scale : DifferentiableAt ℝ (polarScale w z) x

private theorem linearizationRegularAt_of_smooth
    {w : ℝ → ℝ} {z : PolarPoint → ℝ} {x : PolarPoint}
    (hw : ContDiff ℝ ∞ w) (hz : ContDiff ℝ ∞ z) (hr : x.1 ≠ 0)
    (hpos : 0 < polarDiscriminant w z x) : LinearizationRegularAt w z x := by
  have he := contDiff_profileEnergy_of_smooth hw
  have hk := contDiffAt_heightRadial (x := x) hz.contDiffAt (m := 2) (by simp)
  have hp := contDiffAt_heightAngular (x := x) hz.contDiffAt (m := 2) (by simp) hr
  have hE := he.differentiable (by simp) x
  have hk0 := hk.differentiableAt two_ne_zero
  have hp0 := hp.differentiableAt two_ne_zero
  exact {
    energy := hE
    energyRadial := (contDiffAt_radialPartial he.contDiffAt (m := 1) (by simp)).differentiableAt one_ne_zero
    heightR := hk0
    heightRR := (contDiffAt_radialPartial hk (m := 1) (by norm_num)).differentiableAt one_ne_zero
    heightT := hp0
    heightTR := (contDiffAt_radialPartial hp (m := 1) (by norm_num)).differentiableAt one_ne_zero
    heightTT := (contDiffAt_angularPartial hp (m := 1) (by norm_num)).differentiableAt one_ne_zero
    scale := differentiableAt_polarScale hE hk0 hp0 hpos }

private theorem fderiv_polarScale
    {w : ℝ → ℝ} {z : PolarPoint → ℝ} {x : PolarPoint}
    (h : LinearizationRegularAt w z x) (hpos : 0 < polarDiscriminant w z x) (v : PolarPoint) :
    fderiv ℝ (polarScale w z) x v =
      -3 * fderiv ℝ (polarDiscriminant w z) x v * polarScale w z x /
        (2 * polarDiscriminant w z x) := by
  have hd : DifferentiableAt ℝ (polarDiscriminant w z) x :=
    (h.energy.mul ((h.heightT.pow 2).const_sub 1)).sub (h.heightR.pow 2)
  have hcurve := hasDerivAt_inverseDThreeHalves (hd.hasFDerivAt.hasLineDerivAt v)
    (by simpa only [zero_smul, add_zero] using hpos)
  simpa only [zero_smul, add_zero, polarScale] using
    (h.scale.hasFDerivAt.hasLineDerivAt v).unique hcurve

private theorem differentiableAt_polarLinearA
    {w : ℝ → ℝ} {z : PolarPoint → ℝ} {x : PolarPoint} (h : LinearizationRegularAt w z x) :
    DifferentiableAt ℝ (polarLinearA w z) x :=
  (h.heightR.add (h.energy.mul h.heightTT)).mul h.scale

private theorem differentiableAt_polarLinearB
    {w : ℝ → ℝ} {z : PolarPoint → ℝ} {x : PolarPoint} (h : LinearizationRegularAt w z x) :
    DifferentiableAt ℝ (polarLinearB w z) x :=
  (h.energy.neg.mul h.heightTR).mul h.scale

private theorem differentiableAt_polarLinearC
    {w : ℝ → ℝ} {z : PolarPoint → ℝ} {x : PolarPoint} (h : LinearizationRegularAt w z x)
    (hr : x.1 ≠ 0) : DifferentiableAt ℝ (polarLinearC w z) x := by
  have hn := ((h.energy.mul h.heightRR).sub
    ((h.energyRadial.mul h.heightR).mul_const ((2 : ℝ)⁻¹))).mul h.scale
  have hi := (hasDerivAt_inv hr).hasFDerivAt.comp x hasFDerivAt_fst
  convert (hn.mul hi.differentiableAt) using 1
  funext y
  rfl

private theorem fderiv_polarLinearA
    {w : ℝ → ℝ} {z : PolarPoint → ℝ} {x : PolarPoint}
    (h : LinearizationRegularAt w z x) (v : PolarPoint) :
    fderiv ℝ (polarLinearA w z) x v =
      (fderiv ℝ (heightRadial z) x v + fderiv ℝ (profileEnergy w) x v *
          angularPartial (heightAngular z) x +
        profileEnergy w x * fderiv ℝ (angularPartial (heightAngular z)) x v) * polarScale w z x +
      heightQ (profileEnergy w x) (heightRadial z x) (angularPartial (heightAngular z) x) *
        fderiv ℝ (polarScale w z) x v := by
  have ha := (h.heightR.hasFDerivAt.add (h.energy.hasFDerivAt.mul h.heightTT.hasFDerivAt)).mul
    h.scale.hasFDerivAt
  change HasFDerivAt (polarLinearA w z) _ x at ha
  rw [ha.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul, heightQ, Pi.add_apply, Pi.mul_apply]
  ring

private theorem fderiv_polarLinearB
    {w : ℝ → ℝ} {z : PolarPoint → ℝ} {x : PolarPoint}
    (h : LinearizationRegularAt w z x) (v : PolarPoint) :
    fderiv ℝ (polarLinearB w z) x v =
      (-fderiv ℝ (profileEnergy w) x v * radialPartial (heightAngular z) x -
        profileEnergy w x * fderiv ℝ (radialPartial (heightAngular z)) x v) * polarScale w z x -
      profileEnergy w x * radialPartial (heightAngular z) x * fderiv ℝ (polarScale w z) x v := by
  have hb := ((h.energy.hasFDerivAt.neg).mul h.heightTR.hasFDerivAt).mul h.scale.hasFDerivAt
  change HasFDerivAt (polarLinearB w z) _ x at hb
  rw [hb.fderiv]
  simp only [add_apply, neg_apply, smul_apply, smul_eq_mul, Pi.mul_apply, Pi.neg_apply]
  ring

private theorem fderiv_polarLinearC
    {w : ℝ → ℝ} {z : PolarPoint → ℝ} {x : PolarPoint}
    (h : LinearizationRegularAt w z x) (hr : x.1 ≠ 0) (v : PolarPoint) :
    fderiv ℝ (polarLinearC w z) x v =
      ((fderiv ℝ (profileEnergy w) x v * radialPartial (heightRadial z) x +
          profileEnergy w x * fderiv ℝ (radialPartial (heightRadial z)) x v -
          (fderiv ℝ (radialPartial (profileEnergy w)) x v * heightRadial z x +
            radialPartial (profileEnergy w) x * fderiv ℝ (heightRadial z) x v) / 2) * polarScale w z x +
        (profileEnergy w x * radialPartial (heightRadial z) x -
          radialPartial (profileEnergy w) x * heightRadial z x / 2) * fderiv ℝ (polarScale w z) x v) / x.1 -
      (profileEnergy w x * radialPartial (heightRadial z) x -
        radialPartial (profileEnergy w) x * heightRadial z x / 2) * polarScale w z x * v.1 / x.1 ^ 2 := by
  have hn := ((h.energy.hasFDerivAt.mul h.heightRR.hasFDerivAt).sub
    ((h.energyRadial.hasFDerivAt.mul h.heightR.hasFDerivAt).mul_const ((2 : ℝ)⁻¹))).mul h.scale.hasFDerivAt
  change HasFDerivAt (fun y => (profileEnergy w y * radialPartial (heightRadial z) y -
    radialPartial (profileEnergy w) y * heightRadial z y / 2) * polarScale w z y) _ x at hn
  change fderiv ℝ (fun y => ((profileEnergy w y * radialPartial (heightRadial z) y -
    radialPartial (profileEnergy w) y * heightRadial z y / 2) * polarScale w z y) / y.1) x v = _
  rw [polar_fderiv_div hn.differentiableAt differentiableAt_fst hr, hn.fderiv]
  simp only [sub_apply, add_apply, smul_apply, smul_eq_mul, fderiv_fst, Pi.mul_apply, Pi.sub_apply,
    ContinuousLinearMap.coe_fst']
  field_simp [hr]
  ring

/-- The angular derivative of the actual radial metric derivative is zero. -/
theorem angularPartial_radial_profileEnergy
    {w : ℝ → ℝ} {x : PolarPoint} (hw : ContDiff ℝ ∞ w) :
    angularPartial (radialPartial (profileEnergy w)) x = 0 := by
  have he := contDiff_profileEnergy_of_smooth hw
  have heq : angularPartial (profileEnergy w) = fun _ => 0 := by
    funext y
    exact angularPartial_profileEnergy (hw.differentiable (by simp) y.1)
  have hm := radial_angular_commute (x := x) (he.contDiffAt.of_le (by simp))
  rw [heq] at hm
  simpa only [radialPartial_const] using hm.symm

/-- Differentiating the actual height compatibility on a nonzero-radius
neighborhood gives the third-jet identity used in the angular drift. -/
theorem angular_radial_heightRadial_identity
    {z : PolarPoint → ℝ} {x : PolarPoint} (hz : ContDiff ℝ ∞ z) (hr : x.1 ≠ 0) :
    angularPartial (radialPartial (heightRadial z)) x =
      2 * radialPartial (heightAngular z) x + x.1 * radialPartial (radialPartial (heightAngular z)) x := by
  have hn : ∀ᶠ y : PolarPoint in 𝓝 x, y.1 ≠ 0 :=
    (isOpen_ne_fun (continuous_fst : Continuous (Prod.fst : PolarPoint → ℝ)) continuous_const).mem_nhds hr
  have hloc : angularPartial (heightRadial z) =ᶠ[𝓝 x]
      (fun y => heightAngular z y + y.1 * radialPartial (heightAngular z) y) := by
    filter_upwards [hn] with y hy
    have hc := height_compatibility (x := y) (hz.contDiffAt.of_le (by simp)) hy
    linarith
  have hp := contDiffAt_heightAngular hz.contDiffAt (m := 2) (by simp) hr
  have hpd := hp.differentiableAt two_ne_zero
  have hpr := (contDiffAt_radialPartial hp (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hk := contDiffAt_heightRadial (x := x) hz.contDiffAt (m := 2) (by simp)
  have hmul : DifferentiableAt ℝ (fun y : PolarPoint => y.1 * radialPartial (heightAngular z) y) x :=
    differentiableAt_fst.mul hpr
  have hval := congrArg (fun L : PolarPoint →L[ℝ] ℝ => L (1, 0)) (hloc.fderiv_eq (𝕜 := ℝ))
  change radialPartial (angularPartial (heightRadial z)) x =
    radialPartial (fun y => heightAngular z y + y.1 * radialPartial (heightAngular z) y) x at hval
  rw [radial_angular_commute hk, radialPartial_add hpd hmul,
    radialPartial_mul differentiableAt_fst hpr, radialPartial_fst] at hval
  calc
    _ = _ := hval
    _ = _ := by ring

/-- The radial first-order coefficient of the actual divergence expression. -/
theorem polarLinear_radial_drift
    {w : ℝ → ℝ} {z : PolarPoint → ℝ} {x : PolarPoint}
    (hw : ContDiff ℝ ∞ w) (hz : ContDiff ℝ ∞ z) (hr : x.1 ≠ 0)
    (hpos : 0 < polarDiscriminant w z x) :
    radialPartial (polarLinearA w z) x + angularPartial (polarLinearB w z) x =
      (radialPartial (heightRadial z) x -
        radialPartial (profileEnergy w) x * angularPartial (heightAngular z) x / 2 +
        3 * polarCurvatureNumerator w z x * heightRadial z x / polarDiscriminant w z x) *
        polarScale w z x := by
  have h := linearizationRegularAt_of_smooth hw hz hr hpos
  have hEt := angularPartial_profileEnergy (x := x) (hw.differentiable (by simp) x.1)
  have hc := height_compatibility (x := x) (hz.contDiffAt.of_le (by simp)) hr
  have hkt : angularPartial (heightRadial z) x =
      heightAngular z x + x.1 * radialPartial (heightAngular z) x := by linarith
  have hp2 := contDiffAt_heightAngular (x := x) hz.contDiffAt (m := 2) (by simp) hr
  have hm := radial_angular_commute hp2
  have hdr : radialPartial (polarDiscriminant w z) x =
      discriminantVariation (profileEnergy w x) (heightRadial z x) (heightAngular z x)
        (radialPartial (profileEnergy w) x) (radialPartial (heightRadial z) x)
        (radialPartial (heightAngular z) x) :=
    radialPartial_polarDiscriminant (hw.differentiable (by simp) x.1) (hz.contDiffAt.of_le (by simp)) hr
  have hdt : angularPartial (polarDiscriminant w z) x =
      discriminantVariation (profileEnergy w x) (heightRadial z x) (heightAngular z x)
        0 (heightAngular z x + x.1 * radialPartial (heightAngular z) x)
        (angularPartial (heightAngular z) x) := by
    rw [angularPartial_polarDiscriminant (hw.differentiable (by simp) x.1)
      (hz.contDiffAt.of_le (by simp)) hr, hkt]
    unfold discriminantVariation
    ring
  have halg := linearization_radial_drift_algebra x.1 (profileEnergy w x)
    (radialPartial (profileEnergy w) x) (heightRadial z x) (heightAngular z x)
    (radialPartial (heightRadial z) x) (radialPartial (heightAngular z) x)
    (angularPartial (heightAngular z) x) (polarScale w z x) hpos.ne'
  simp only [radialPartial, angularPartial] at hEt hkt hm hdr hdt halg ⊢
  simp only [fderiv_polarLinearA h, fderiv_polarLinearB h, fderiv_polarScale h hpos,
    hdr, hdt, hEt, hm]
  convert halg using 1
  all_goals simp only [polarCurvatureNumerator, polarDiscriminant, heightQ,
    radialPartial, angularPartial, discriminantVariation]
  all_goals ring

/-- The angular first-order coefficient of the actual divergence expression. -/
theorem polarLinear_angular_drift
    {w : ℝ → ℝ} {z : PolarPoint → ℝ} {x : PolarPoint}
    (hw : ContDiff ℝ ∞ w) (hz : ContDiff ℝ ∞ z) (hr : x.1 ≠ 0)
    (hpos : 0 < polarDiscriminant w z x) :
    radialPartial (polarLinearB w z) x + angularPartial (polarLinearC w z) x =
      (radialPartial (profileEnergy w) x * heightAngular z x +
        2 * profileEnergy w x * radialPartial (heightAngular z) x +
        3 * polarCurvatureNumerator w z x * profileEnergy w x * heightAngular z x /
          polarDiscriminant w z x) * polarScale w z x / x.1 := by
  apply (eq_div_iff hr).mpr
  have h := linearizationRegularAt_of_smooth hw hz hr hpos
  have hEt := angularPartial_profileEnergy (x := x) (hw.differentiable (by simp) x.1)
  have hErt := angularPartial_radial_profileEnergy (x := x) hw
  have hkt0 := height_compatibility (x := x) (hz.contDiffAt.of_le (by simp)) hr
  have hkt : angularPartial (heightRadial z) x =
      heightAngular z x + x.1 * radialPartial (heightAngular z) x := by linarith
  have hkrt := angular_radial_heightRadial_identity hz hr
  have hdr : radialPartial (polarDiscriminant w z) x =
      discriminantVariation (profileEnergy w x) (heightRadial z x) (heightAngular z x)
        (radialPartial (profileEnergy w) x) (radialPartial (heightRadial z) x)
        (radialPartial (heightAngular z) x) :=
    radialPartial_polarDiscriminant (hw.differentiable (by simp) x.1) (hz.contDiffAt.of_le (by simp)) hr
  have hdt : angularPartial (polarDiscriminant w z) x =
      discriminantVariation (profileEnergy w x) (heightRadial z x) (heightAngular z x)
        0 (heightAngular z x + x.1 * radialPartial (heightAngular z) x)
        (angularPartial (heightAngular z) x) := by
    rw [angularPartial_polarDiscriminant (hw.differentiable (by simp) x.1)
      (hz.contDiffAt.of_le (by simp)) hr, hkt]
    unfold discriminantVariation
    ring
  have halg := linearization_angular_drift_algebra x.1 (profileEnergy w x)
    (radialPartial (profileEnergy w) x) (heightRadial z x) (heightAngular z x)
    (radialPartial (heightRadial z) x) (radialPartial (heightAngular z) x)
    (angularPartial (heightAngular z) x) (polarScale w z x) hpos.ne'
  simp only [radialPartial, angularPartial] at hEt hErt hkt hkrt hdr hdt halg ⊢
  simp only [fderiv_polarLinearB h, fderiv_polarLinearC h hr, fderiv_polarScale h hpos,
    hdr, hdt, hEt, hErt, hkt, hkrt, mul_zero]
  convert halg using 1
  all_goals simp only [polarCurvatureNumerator, polarDiscriminant, radialPartial,
    angularPartial, discriminantVariation]
  all_goals field_simp [hr, hpos.ne']
  all_goals ring

/-- Actual product-rule expansion of a symmetric divergence operator. -/
theorem divergence_expansion_of_coefficients
    {a b c η : PolarPoint → ℝ} {x : PolarPoint}
    (ha : DifferentiableAt ℝ a x) (hb : DifferentiableAt ℝ b x)
    (hc : DifferentiableAt ℝ c x) (hη : ContDiffAt ℝ 2 η x) :
    radialPartial (fun y => a y * radialPartial η y + b y * angularPartial η y) x +
        angularPartial (fun y => b y * radialPartial η y + c y * angularPartial η y) x =
      a x * radialPartial (radialPartial η) x + 2 * b x * angularPartial (radialPartial η) x +
        c x * angularPartial (angularPartial η) x +
        (radialPartial a x + angularPartial b x) * radialPartial η x +
        (radialPartial b x + angularPartial c x) * angularPartial η x := by
  have hηr := (contDiffAt_radialPartial hη (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hηt := (contDiffAt_angularPartial hη (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have har : DifferentiableAt ℝ (fun y => a y * radialPartial η y) x := ha.mul hηr
  have hbt : DifferentiableAt ℝ (fun y => b y * angularPartial η y) x := hb.mul hηt
  have hbr : DifferentiableAt ℝ (fun y => b y * radialPartial η y) x := hb.mul hηr
  have hct : DifferentiableAt ℝ (fun y => c y * angularPartial η y) x := hc.mul hηt
  rw [radialPartial_add har hbt, angularPartial_add hbr hct,
    radialPartial_mul ha hηr, radialPartial_mul hb hηt,
    angularPartial_mul hb hηr, angularPartial_mul hc hηt,
    radial_angular_commute hη]
  ring

/-- The angular second derivative of the height has the correct radial
normalization, proved by the actual quotient rule. -/
theorem angularSecond_eq_radius_mul_heightAngular
    {η : PolarPoint → ℝ} {x : PolarPoint} (hη : ContDiffAt ℝ 2 η x) (hr : x.1 ≠ 0) :
    angularPartial (angularPartial η) x = x.1 * angularPartial (heightAngular η) x := by
  have hηt := (contDiffAt_angularPartial hη (m := 1) (by norm_num)).differentiableAt one_ne_zero
  unfold heightAngular
  rw [angularPartial_div hηt differentiableAt_fst hr, angularPartial_fst]
  field_simp [hr]
  ring

/-- The actual divergence agrees with the actual height-direction variation
of the coordinate residual, including the factor of the radius. -/
theorem heightLinearizedDivergence_eq_variation
    {w : ℝ → ℝ} {z η : PolarPoint → ℝ} {x : PolarPoint}
    (hw : ContDiff ℝ ∞ w) (hz : ContDiff ℝ ∞ z) (hη : ContDiff ℝ ∞ η)
    (hr : x.1 ≠ 0) (hpos : 0 < polarDiscriminant w z x) :
    heightLinearizedDivergence w z η x = x.1 * polarResidualVariation w z η x := by
  have h := linearizationRegularAt_of_smooth hw hz hr hpos
  have hη2 : ContDiffAt ℝ 2 η x := hη.contDiffAt.of_le (by simp)
  have hηcompat := height_compatibility hη2 hr
  have hηrt : angularPartial (radialPartial η) x =
      heightAngular η x + x.1 * radialPartial (heightAngular η) x := by
    change angularPartial (heightRadial η) x = _
    linarith
  have hηt : angularPartial η x = x.1 * heightAngular η x := by
    unfold heightAngular
    field_simp [hr]
  have hηtt := angularSecond_eq_radius_mul_heightAngular hη2 hr
  unfold heightLinearizedDivergence
  rw [divergence_expansion_of_coefficients (differentiableAt_polarLinearA h)
      (differentiableAt_polarLinearB h) (differentiableAt_polarLinearC h hr) hη2,
    polarLinear_radial_drift hw hz hr hpos, polarLinear_angular_drift hw hz hr hpos,
    hηrt, hηt, hηtt]
  have halg := linearization_expanded_algebra x.1 (profileEnergy w x)
    (radialPartial (profileEnergy w) x) (heightRadial z x) (heightAngular z x)
    (radialPartial (heightRadial z) x) (radialPartial (heightAngular z) x)
    (angularPartial (heightAngular z) x) (polarScale w z x)
    (heightRadial η x) (heightAngular η x) (radialPartial (heightRadial η) x)
    (radialPartial (heightAngular η) x) (angularPartial (heightAngular η) x) hr hpos.ne'
  convert halg using 1
  all_goals simp only [polarLinearA, polarLinearB, polarLinearC, polarScale,
    polarResidualVariation, polarCurvatureNumeratorVariation, polarCurvatureNumerator,
    polarDiscriminantVariation, polarDiscriminant, heightRadial]
  all_goals field_simp [hr, hpos.ne']

theorem polarResidualVariation_eq_divergence
    {w : ℝ → ℝ} {z η : PolarPoint → ℝ} {x : PolarPoint}
    (hw : ContDiff ℝ ∞ w) (hz : ContDiff ℝ ∞ z) (hη : ContDiff ℝ ∞ η)
    (hr : x.1 ≠ 0) (hpos : 0 < polarDiscriminant w z x) :
    polarResidualVariation w z η x = heightLinearizedDivergence w z η x / x.1 := by
  rw [heightLinearizedDivergence_eq_variation hw hz hη hr hpos]
  exact (mul_div_cancel_left₀ _ hr).symm

/-- The full divergence-form directional linearization of the actual residual. -/
theorem hasDerivAt_polarCoordinateResidual_divergence
    {w : ℝ → ℝ} {z η : PolarPoint → ℝ} {x : PolarPoint}
    (hw : ContDiff ℝ ∞ w) (hz : ContDiff ℝ ∞ z) (hη : ContDiff ℝ ∞ η)
    (hr : x.1 ≠ 0) (hpos : 0 < polarDiscriminant w z x) :
    HasDerivAt (fun t => polarCoordinateResidual w (heightFamily z η t) x)
      (heightLinearizedDivergence w z η x / x.1) 0 :=
  (hasDerivAt_polarCoordinateResidual_heightFamily w hz hη hr hpos).congr_deriv
    (polarResidualVariation_eq_divergence hw hz hη hr hpos)

/-- Section 3's `r D_z N η = div(a η_r+b η_θ, b η_r+c η_θ)`,
as a genuine `HasDerivAt` theorem for the affine height family. -/
theorem hasDerivAt_radialScaledResidual_divergence
    {w : ℝ → ℝ} {z η : PolarPoint → ℝ} {x : PolarPoint}
    (hw : ContDiff ℝ ∞ w) (hz : ContDiff ℝ ∞ z) (hη : ContDiff ℝ ∞ η)
    (hr : x.1 ≠ 0) (hpos : 0 < polarDiscriminant w z x) :
    HasDerivAt (fun t => x.1 * polarCoordinateResidual w (heightFamily z η t) x)
      (heightLinearizedDivergence w z η x) 0 := by
  have h := (hasDerivAt_polarCoordinateResidual_divergence hw hz hη hr hpos).const_mul x.1
  apply h.congr_deriv
  field_simp [hr]

end ContinuousFlexibility
