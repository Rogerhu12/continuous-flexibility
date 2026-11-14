module

public import ContinuousFlexibility.Scalar.Connection

/-!
# Actual parameter differentiation of the height residual

The family is the genuine function `z + t η` on coordinate space. We first
prove affinity of its actual spatial partials, then differentiate the
numerator and the inverse-discriminant factor along this family. The final
result is a true `HasDerivAt` statement for the coordinate residual. It is
not yet the divergence-form linearization asserted in the manuscript.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility

open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-- An actual affine family of height functions. -/
def heightFamily (z η : PolarPoint → ℝ) (t : ℝ) (x : PolarPoint) : ℝ := z x + t * η x

@[simp] theorem heightFamily_zero (z η : PolarPoint → ℝ) : heightFamily z η 0 = z := by
  funext x
  simp [heightFamily]

theorem contDiff_heightFamily {z η : PolarPoint → ℝ} {n : ℕ∞ω}
    (hz : ContDiff ℝ n z) (hη : ContDiff ℝ n η) (t : ℝ) :
    ContDiff ℝ n (heightFamily z η t) := hz.add ((contDiff_const (c := t)).mul hη)

theorem radialPartial_heightFamily
    {z η : PolarPoint → ℝ} {x : PolarPoint}
    (hz : DifferentiableAt ℝ z x) (hη : DifferentiableAt ℝ η x) (t : ℝ) :
    radialPartial (heightFamily z η t) x = radialPartial z x + t * radialPartial η x := by
  unfold heightFamily
  rw [radialPartial_add hz (hη.const_mul t),
    radialPartial_mul (differentiableAt_const t) hη, radialPartial_const]
  ring

theorem angularPartial_heightFamily
    {z η : PolarPoint → ℝ} {x : PolarPoint}
    (hz : DifferentiableAt ℝ z x) (hη : DifferentiableAt ℝ η x) (t : ℝ) :
    angularPartial (heightFamily z η t) x = angularPartial z x + t * angularPartial η x := by
  unfold heightFamily
  rw [angularPartial_add hz (hη.const_mul t),
    angularPartial_mul (differentiableAt_const t) hη, angularPartial_const]
  ring

/-- This is an equality of actual functions, so it may subsequently be
differentiated in the spatial variables. -/
theorem heightRadial_heightFamily
    {z η : PolarPoint → ℝ} (hz : Differentiable ℝ z) (hη : Differentiable ℝ η) (t : ℝ) :
    heightRadial (heightFamily z η t) = heightFamily (heightRadial z) (heightRadial η) t := by
  funext x
  exact radialPartial_heightFamily (hz x) (hη x) t

/-- The normalized angular derivative is affine even as a global function;
its subsequent spatial derivative is taken only at nonzero radius. -/
theorem heightAngular_heightFamily
    {z η : PolarPoint → ℝ} (hz : Differentiable ℝ z) (hη : Differentiable ℝ η) (t : ℝ) :
    heightAngular (heightFamily z η t) = heightFamily (heightAngular z) (heightAngular η) t := by
  funext x
  unfold heightAngular
  rw [angularPartial_heightFamily (hz x) (hη x)]
  unfold heightFamily
  ring

private theorem smooth_heightRadial_diff
    {z : PolarPoint → ℝ} {x : PolarPoint} (hz : ContDiff ℝ ∞ z) :
    DifferentiableAt ℝ (heightRadial z) x :=
  (contDiffAt_heightRadial hz.contDiffAt (m := 1) (by simp)).differentiableAt one_ne_zero

private theorem smooth_heightAngular_diff
    {z : PolarPoint → ℝ} {x : PolarPoint} (hz : ContDiff ℝ ∞ z) (hr : x.1 ≠ 0) :
    DifferentiableAt ℝ (heightAngular z) x :=
  (contDiffAt_heightAngular hz.contDiffAt (m := 1) (by simp) hr).differentiableAt one_ne_zero

theorem radialPartial_heightRadial_heightFamily
    {z η : PolarPoint → ℝ} {x : PolarPoint}
    (hz : ContDiff ℝ ∞ z) (hη : ContDiff ℝ ∞ η) (t : ℝ) :
    radialPartial (heightRadial (heightFamily z η t)) x =
      radialPartial (heightRadial z) x + t * radialPartial (heightRadial η) x := by
  rw [heightRadial_heightFamily (hz.differentiable (by simp)) (hη.differentiable (by simp))]
  exact radialPartial_heightFamily (smooth_heightRadial_diff hz) (smooth_heightRadial_diff hη) t

theorem angularPartial_heightRadial_heightFamily
    {z η : PolarPoint → ℝ} {x : PolarPoint}
    (hz : ContDiff ℝ ∞ z) (hη : ContDiff ℝ ∞ η) (t : ℝ) :
    angularPartial (heightRadial (heightFamily z η t)) x =
      angularPartial (heightRadial z) x + t * angularPartial (heightRadial η) x := by
  rw [heightRadial_heightFamily (hz.differentiable (by simp)) (hη.differentiable (by simp))]
  exact angularPartial_heightFamily (smooth_heightRadial_diff hz) (smooth_heightRadial_diff hη) t

theorem radialPartial_heightAngular_heightFamily
    {z η : PolarPoint → ℝ} {x : PolarPoint}
    (hz : ContDiff ℝ ∞ z) (hη : ContDiff ℝ ∞ η) (hr : x.1 ≠ 0) (t : ℝ) :
    radialPartial (heightAngular (heightFamily z η t)) x =
      radialPartial (heightAngular z) x + t * radialPartial (heightAngular η) x := by
  rw [heightAngular_heightFamily (hz.differentiable (by simp)) (hη.differentiable (by simp))]
  exact radialPartial_heightFamily (smooth_heightAngular_diff hz hr) (smooth_heightAngular_diff hη hr) t

theorem angularPartial_heightAngular_heightFamily
    {z η : PolarPoint → ℝ} {x : PolarPoint}
    (hz : ContDiff ℝ ∞ z) (hη : ContDiff ℝ ∞ η) (hr : x.1 ≠ 0) (t : ℝ) :
    angularPartial (heightAngular (heightFamily z η t)) x =
      angularPartial (heightAngular z) x + t * angularPartial (heightAngular η) x := by
  rw [heightAngular_heightFamily (hz.differentiable (by simp)) (hη.differentiable (by simp))]
  exact angularPartial_heightFamily (smooth_heightAngular_diff hz hr) (smooth_heightAngular_diff hη hr) t

private theorem hasDerivAt_affineValue (a b t : ℝ) :
    HasDerivAt (fun s => a + s * b) b t := by
  have h := (hasDerivAt_const t a).add ((hasDerivAt_id t).mul_const b)
  change HasDerivAt (fun s => a + s * b) (0 + 1 * b) t at h
  simpa only [zero_add, one_mul] using h

theorem hasDerivAt_heightRadial_heightFamily
    {z η : PolarPoint → ℝ} (hz : ContDiff ℝ ∞ z) (hη : ContDiff ℝ ∞ η)
    (x : PolarPoint) (t : ℝ) :
    HasDerivAt (fun s => heightRadial (heightFamily z η s) x) (heightRadial η x) t := by
  simp_rw [heightRadial_heightFamily (hz.differentiable (by simp)) (hη.differentiable (by simp))]
  exact hasDerivAt_affineValue _ _ _

theorem hasDerivAt_heightAngular_heightFamily
    {z η : PolarPoint → ℝ} (hz : ContDiff ℝ ∞ z) (hη : ContDiff ℝ ∞ η)
    (x : PolarPoint) (t : ℝ) :
    HasDerivAt (fun s => heightAngular (heightFamily z η s) x) (heightAngular η x) t := by
  simp_rw [heightAngular_heightFamily (hz.differentiable (by simp)) (hη.differentiable (by simp))]
  exact hasDerivAt_affineValue _ _ _

theorem hasDerivAt_radialPartial_heightRadial_heightFamily
    {z η : PolarPoint → ℝ} {x : PolarPoint}
    (hz : ContDiff ℝ ∞ z) (hη : ContDiff ℝ ∞ η) (t : ℝ) :
    HasDerivAt (fun s => radialPartial (heightRadial (heightFamily z η s)) x)
      (radialPartial (heightRadial η) x) t := by
  simp_rw [radialPartial_heightRadial_heightFamily hz hη]
  exact hasDerivAt_affineValue _ _ _

theorem hasDerivAt_radialPartial_heightAngular_heightFamily
    {z η : PolarPoint → ℝ} {x : PolarPoint}
    (hz : ContDiff ℝ ∞ z) (hη : ContDiff ℝ ∞ η) (hr : x.1 ≠ 0) (t : ℝ) :
    HasDerivAt (fun s => radialPartial (heightAngular (heightFamily z η s)) x)
      (radialPartial (heightAngular η) x) t := by
  simp_rw [radialPartial_heightAngular_heightFamily hz hη hr]
  exact hasDerivAt_affineValue _ _ _

theorem hasDerivAt_angularPartial_heightAngular_heightFamily
    {z η : PolarPoint → ℝ} {x : PolarPoint}
    (hz : ContDiff ℝ ∞ z) (hη : ContDiff ℝ ∞ η) (hr : x.1 ≠ 0) (t : ℝ) :
    HasDerivAt (fun s => angularPartial (heightAngular (heightFamily z η s)) x)
      (angularPartial (heightAngular η) x) t := by
  simp_rw [angularPartial_heightAngular_heightFamily hz hη hr]
  exact hasDerivAt_affineValue _ _ _

/-- The numerator's parameter derivative with fixed metric coefficients. -/
def darbouxNumeratorVariation (r E Er k p kr pr pt dk dp dkr dpr dpt : ℝ) : ℝ :=
  (dk + E * dpt) * kr + heightQ E k pt * dkr - 2 * E * r * pr * dpr +
    Er * p * dp - Er / 2 * (dk * pt + k * dpt)

/-- A genuine derivative for arbitrary differentiable curves of the five
height jets. Their identification with spatial jets follows below. -/
theorem hasDerivAt_darbouxNumerator
    {k p kr pr pt : ℝ → ℝ} {dk dp dkr dpr dpt t : ℝ} (r E Er : ℝ)
    (hk : HasDerivAt k dk t) (hp : HasDerivAt p dp t)
    (hkr : HasDerivAt kr dkr t) (hpr : HasDerivAt pr dpr t)
    (hpt : HasDerivAt pt dpt t) :
    HasDerivAt (fun s => darbouxNumerator r E Er (k s) (p s) (kr s) (pr s) (pt s))
      (darbouxNumeratorVariation r E Er (k t) (p t) (kr t) (pr t) (pt t)
        dk dp dkr dpr dpt) t := by
  have hq := hk.add (hpt.const_mul E)
  have hlast := ((hasDerivAt_const t (1 : ℝ)).sub (hp.pow 2)).add (hk.mul hpt)
  have h := ((hq.mul hkr).sub ((hpr.pow 2).const_mul (E * r))).sub (hlast.const_mul (Er / 2))
  apply h.congr_deriv
  simp only [darbouxNumeratorVariation, heightQ, Pi.add_apply]
  ring

/-- Derivative of the discriminant of the actual height family. -/
def polarDiscriminantVariation (w : ℝ → ℝ) (z η : PolarPoint → ℝ) (x : PolarPoint) : ℝ :=
  -2 * profileEnergy w x * heightAngular z x * heightAngular η x -
    2 * heightRadial z x * heightRadial η x

/-- The numerator variation with every jet supplied by a real spatial derivative. -/
def polarCurvatureNumeratorVariation (w : ℝ → ℝ) (z η : PolarPoint → ℝ)
    (x : PolarPoint) : ℝ :=
  darbouxNumeratorVariation x.1 (profileEnergy w x) (radialPartial (profileEnergy w) x)
    (heightRadial z x) (heightAngular z x) (radialPartial (heightRadial z) x)
    (radialPartial (heightAngular z) x) (angularPartial (heightAngular z) x)
    (heightRadial η x) (heightAngular η x) (radialPartial (heightRadial η) x)
    (radialPartial (heightAngular η) x) (angularPartial (heightAngular η) x)

theorem hasDerivAt_polarDiscriminant_heightFamily
    (w : ℝ → ℝ) {z η : PolarPoint → ℝ}
    (hz : ContDiff ℝ ∞ z) (hη : ContDiff ℝ ∞ η) (x : PolarPoint) :
    HasDerivAt (fun t => polarDiscriminant w (heightFamily z η t) x)
      (polarDiscriminantVariation w z η x) 0 := by
  have h := hasDerivAt_heightDiscriminant (hasDerivAt_const 0 (profileEnergy w x))
    (hasDerivAt_heightRadial_heightFamily hz hη x 0)
    (hasDerivAt_heightAngular_heightFamily hz hη x 0)
  simpa [polarDiscriminant, discriminantVariation, polarDiscriminantVariation] using h

theorem hasDerivAt_polarCurvatureNumerator_heightFamily
    (w : ℝ → ℝ) {z η : PolarPoint → ℝ} {x : PolarPoint}
    (hz : ContDiff ℝ ∞ z) (hη : ContDiff ℝ ∞ η) (hr : x.1 ≠ 0) :
    HasDerivAt (fun t => polarCurvatureNumerator w (heightFamily z η t) x)
      (polarCurvatureNumeratorVariation w z η x) 0 := by
  have h := hasDerivAt_darbouxNumerator x.1 (profileEnergy w x) (radialPartial (profileEnergy w) x)
    (hasDerivAt_heightRadial_heightFamily hz hη x 0)
    (hasDerivAt_heightAngular_heightFamily hz hη x 0)
    (hasDerivAt_radialPartial_heightRadial_heightFamily (x := x) hz hη 0)
    (hasDerivAt_radialPartial_heightAngular_heightFamily (x := x) hz hη hr 0)
    (hasDerivAt_angularPartial_heightAngular_heightFamily (x := x) hz hη hr 0)
  simpa only [heightFamily_zero, polarCurvatureNumerator, polarCurvatureNumeratorVariation] using h

/-- Differentiating `D^(-3/2)` along an actual positive-discriminant curve. -/
theorem hasDerivAt_inverseDThreeHalves {D : ℝ → ℝ} {dD t : ℝ}
    (hD : HasDerivAt D dD t) (hpos : 0 < D t) :
    HasDerivAt (fun s => inverseDThreeHalves (D s))
      (-3 * dD * inverseDThreeHalves (D t) / (2 * D t)) t := by
  have h := (hasDerivAt_inverse_sqrt hD hpos).div hD hpos.ne'
  have hcoeff :
      ((-dD * inverseDThreeHalves (D t) / 2) * D t -
        (1 / Real.sqrt (D t)) * dD) / D t ^ 2 =
      -3 * dD * inverseDThreeHalves (D t) / (2 * D t) := by
    unfold inverseDThreeHalves
    field_simp [hpos.ne', (Real.sqrt_pos.mpr hpos).ne']
    ring
  convert h.congr_deriv hcoeff using 1
  funext s
  simp only [inverseDThreeHalves, Pi.div_apply, div_eq_mul_inv, mul_inv_rev, one_mul]

/-- The first variation of the actual coordinate residual at fixed profile. -/
def polarResidualVariation (w : ℝ → ℝ) (z η : PolarPoint → ℝ) (x : PolarPoint) : ℝ :=
  (polarCurvatureNumeratorVariation w z η x * inverseDThreeHalves (polarDiscriminant w z x) -
    3 * polarCurvatureNumerator w z x * polarDiscriminantVariation w z η x *
      inverseDThreeHalves (polarDiscriminant w z x) / (2 * polarDiscriminant w z x)) / x.1

/-- The true directional derivative of the scalar residual along `z+tη`.
This theorem does not yet assert a divergence-form representation. -/
theorem hasDerivAt_polarCoordinateResidual_heightFamily
    (w : ℝ → ℝ) {z η : PolarPoint → ℝ} {x : PolarPoint}
    (hz : ContDiff ℝ ∞ z) (hη : ContDiff ℝ ∞ η) (hr : x.1 ≠ 0)
    (hpos : 0 < polarDiscriminant w z x) :
    HasDerivAt (fun t => polarCoordinateResidual w (heightFamily z η t) x)
      (polarResidualVariation w z η x) 0 := by
  have hnum := hasDerivAt_polarCurvatureNumerator_heightFamily w hz hη hr
  have hdisc := hasDerivAt_polarDiscriminant_heightFamily w hz hη x
  have hscale := hasDerivAt_inverseDThreeHalves hdisc (by simpa using hpos)
  have h := (hnum.mul hscale).div_const x.1
  apply h.congr_deriv
  simp only [heightFamily_zero]
  unfold polarResidualVariation
  ring

end ContinuousFlexibility
