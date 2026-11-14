module

public import ContinuousFlexibility.Radial.FourierModes
public import ContinuousFlexibility.Scalar.Normalization
public import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# The actual radial height as a zero-residual base point

The height is the real function `h ∘ Prod.fst`, with `h' = w`.
Its actual polar derivatives give discriminant one and zero numerator.
The genuine parameter derivative and removable normalized residual are
then identified with the actual two-dimensional radial Jacobi operator.
-/

@[expose] public section

namespace ContinuousFlexibility.Radial

noncomputable section

open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

def radialHeightField (h : ℝ → ℝ) (x : PolarPoint) : ℝ := h x.1

theorem contDiff_radialHeightField {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) :
    ContDiff ℝ ∞ (radialHeightField h) := hh.comp contDiff_fst

theorem radialPartial_radialHeightField {h : ℝ → ℝ} {x : PolarPoint}
    (hh : DifferentiableAt ℝ h x.1) :
    radialPartial (radialHeightField h) x = deriv h x.1 := by
  have hf := hh.hasFDerivAt.comp x hasFDerivAt_fst
  change HasFDerivAt (radialHeightField h) _ x at hf
  unfold radialPartial
  rw [hf.fderiv]
  change fderiv ℝ h x.1 1 = deriv h x.1
  rw [fderiv_eq_deriv_mul, mul_one]

theorem angularPartial_radialHeightField {h : ℝ → ℝ} {x : PolarPoint}
    (hh : DifferentiableAt ℝ h x.1) :
    angularPartial (radialHeightField h) x = 0 := by
  have hf := hh.hasFDerivAt.comp x hasFDerivAt_fst
  change HasFDerivAt (radialHeightField h) _ x at hf
  unfold angularPartial
  rw [hf.fderiv]
  change fderiv ℝ h x.1 0 = 0
  simp

theorem heightRadial_radialHeightField {h w : ℝ → ℝ}
    (hhw : ∀ r, HasDerivAt h (w r) r) :
    heightRadial (radialHeightField h) = radialHeightField w := by
  funext x
  change radialPartial (radialHeightField h) x = w x.1
  rw [radialPartial_radialHeightField (hhw x.1).differentiableAt, (hhw x.1).deriv]

theorem heightAngular_radialHeightField {h w : ℝ → ℝ}
    (hhw : ∀ r, HasDerivAt h (w r) r) :
    heightAngular (radialHeightField h) = fun _ => 0 := by
  funext x
  unfold heightAngular
  rw [angularPartial_radialHeightField (hhw x.1).differentiableAt, zero_div]

theorem polarDiscriminant_radialHeightField {h w : ℝ → ℝ}
    (hhw : ∀ r, HasDerivAt h (w r) r) (x : PolarPoint) :
    polarDiscriminant w (radialHeightField h) x = 1 := by
  unfold polarDiscriminant
  rw [heightRadial_radialHeightField hhw, heightAngular_radialHeightField hhw]
  exact heightDiscriminant_radial (w x.1)

/-- The base numerator is zero because its actual height derivative is the
actual profile, rather than because the numerator was assumed zero. -/
theorem polarCurvatureNumerator_radialHeightField {h w : ℝ → ℝ}
    (hhw : ∀ r, HasDerivAt h (w r) r) {x : PolarPoint}
    (hw : DifferentiableAt ℝ w x.1) :
    polarCurvatureNumerator w (radialHeightField h) x = 0 := by
  unfold polarCurvatureNumerator
  rw [heightRadial_radialHeightField hhw, heightAngular_radialHeightField hhw,
    radialPartial_radialHeightField hw, radialPartial_const, angularPartial_const,
    radialPartial_profileEnergy hw]
  simp only [profileEnergy, radialHeightField, darbouxNumerator, heightQ, radialEnergy]
  ring

theorem polarCoordinateResidual_radialHeightField {h w : ℝ → ℝ}
    (hhw : ∀ r, HasDerivAt h (w r) r) {x : PolarPoint}
    (hw : DifferentiableAt ℝ w x.1) :
    polarCoordinateResidual w (radialHeightField h) x = 0 := by
  unfold polarCoordinateResidual
  rw [polarCurvatureNumerator_radialHeightField hhw hw, zero_mul, zero_div]

/-- Restricting a genuine Fréchet derivative to a radial coordinate line. -/
theorem hasDerivAt_radialSlice {f : PolarPoint → ℝ} {x : PolarPoint}
    (hf : DifferentiableAt ℝ f x) :
    HasDerivAt (fun r => f (r, x.2)) (radialPartial f x) x.1 := by
  have hp : HasDerivAt (fun r : ℝ => (r, x.2)) (1, 0) x.1 :=
    (hasDerivAt_id x.1).prodMk (hasDerivAt_const x.1 x.2)
  have h := hf.hasFDerivAt.comp_hasDerivAt x.1 hp
  simpa only [Function.comp_def, Prod.eta, radialPartial] using h

theorem hasDerivAt_angularSlice {f : PolarPoint → ℝ} {x : PolarPoint}
    (hf : DifferentiableAt ℝ f x) :
    HasDerivAt (fun θ => f (x.1, θ)) (angularPartial f x) x.2 := by
  have hp : HasDerivAt (fun θ : ℝ => (x.1, θ)) (0, 1) x.2 :=
    (hasDerivAt_const x.2 x.1).prodMk (hasDerivAt_id x.2)
  have h := hf.hasFDerivAt.comp_hasDerivAt x.2 hp
  simpa only [Function.comp_def, Prod.eta, angularPartial] using h

/-- This bridges the two conventions used in the scalar and radial modules:
actual Fréchet partials and actual derivatives of coordinate slices. -/
theorem radialPDE_eq_polar_jets {w : ℝ → ℝ} {η : PolarPoint → ℝ} {x : PolarPoint}
    (hw : DifferentiableAt ℝ w x.1) (hη : ContDiff ℝ ∞ η) :
    radialPDE w (fun r θ => η (r, θ)) x.1 x.2 =
      deriv w x.1 * radialPartial η x + w x.1 * radialPartial (radialPartial η) x +
        deriv w x.1 / x.1 * angularPartial (angularPartial η) x := by
  have hdη (y : PolarPoint) : DifferentiableAt ℝ η y := hη.differentiable (by simp) y
  have hdr (y : PolarPoint) : DifferentiableAt ℝ (radialPartial η) y :=
    (contDiffAt_radialPartial hη.contDiffAt (m := 1) (by simp)).differentiableAt one_ne_zero
  have hdt (y : PolarPoint) : DifferentiableAt ℝ (angularPartial η) y :=
    (contDiffAt_angularPartial hη.contDiffAt (m := 1) (by simp)).differentiableAt one_ne_zero
  have hrad : deriv (fun r => η (r, x.2)) = (fun r => radialPartial η (r, x.2)) := by
    funext r
    exact (hasDerivAt_radialSlice (x := (r, x.2)) (hdη _)).deriv
  have hang : deriv (fun θ => η (x.1, θ)) = (fun θ => angularPartial η (x.1, θ)) := by
    funext θ
    exact (hasDerivAt_angularSlice (x := (x.1, θ)) (hdη _)).deriv
  have hr₂ := hasDerivAt_radialSlice (hdr x)
  rw [← hrad] at hr₂
  have ht₂ := hasDerivAt_angularSlice (hdt x)
  rw [← hang] at ht₂
  have hf := hw.hasDerivAt.mul hr₂
  rw [(hasDerivAt_radialSlice (hdη x)).deriv] at hf
  change HasDerivAt (fun t => w t * deriv (fun r => η (r, x.2)) t)
    (deriv w x.1 * radialPartial η x + w x.1 * radialPartial (radialPartial η) x) x.1 at hf
  unfold radialPDE
  change deriv (fun t => w t * deriv (fun r => η (r, x.2)) t) x.1 +
    deriv w x.1 / x.1 * deriv (deriv (fun θ => η (x.1, θ))) x.2 = _
  rw [hf.deriv, ht₂.deriv]

/-- The angular derivative of `η_θ/r` uses the true second angular partial. -/
theorem angularPartial_heightAngular_eq {η : PolarPoint → ℝ} {x : PolarPoint}
    (hη : ContDiff ℝ ∞ η) (hr : x.1 ≠ 0) :
    angularPartial (heightAngular η) x = angularPartial (angularPartial η) x / x.1 := by
  have hdt : DifferentiableAt ℝ (angularPartial η) x :=
    (contDiffAt_angularPartial hη.contDiffAt (m := 1) (by simp)).differentiableAt one_ne_zero
  unfold heightAngular
  rw [angularPartial_div hdt differentiableAt_fst hr, angularPartial_fst]
  field_simp [hr]
  ring

/-- At the actual radial base, the true numerator variation is exactly the
two-dimensional radial Jacobi expression, including the source convention. -/
theorem polarCurvatureNumeratorVariation_radialHeightField
    {h w : ℝ → ℝ} {η : PolarPoint → ℝ} {x : PolarPoint}
    (hhw : ∀ r, HasDerivAt h (w r) r) (hw : DifferentiableAt ℝ w x.1)
    (hη : ContDiff ℝ ∞ η) (hr : x.1 ≠ 0) :
    polarCurvatureNumeratorVariation w (radialHeightField h) η x =
      radialPDE w (fun r θ => η (r, θ)) x.1 x.2 := by
  rw [radialPDE_eq_polar_jets hw hη]
  unfold polarCurvatureNumeratorVariation darbouxNumeratorVariation
  rw [heightRadial_radialHeightField hhw, heightAngular_radialHeightField hhw,
    radialPartial_radialHeightField hw, radialPartial_const, angularPartial_const,
    radialPartial_profileEnergy hw, angularPartial_heightAngular_eq hη hr]
  simp only [profileEnergy, radialHeightField, heightRadial, heightQ, radialEnergy]
  ring

theorem polarResidualVariation_radialHeightField
    {h w : ℝ → ℝ} {η : PolarPoint → ℝ} {x : PolarPoint}
    (hhw : ∀ r, HasDerivAt h (w r) r) (hw : DifferentiableAt ℝ w x.1)
    (hη : ContDiff ℝ ∞ η) (hr : x.1 ≠ 0) :
    polarResidualVariation w (radialHeightField h) η x =
      radialPDE w (fun r θ => η (r, θ)) x.1 x.2 / x.1 := by
  unfold polarResidualVariation
  rw [polarCurvatureNumerator_radialHeightField hhw hw,
    polarDiscriminant_radialHeightField hhw, inverseDThreeHalves_one,
    polarCurvatureNumeratorVariation_radialHeightField hhw hw hη hr]
  ring

/-- The actual parameter derivative at the radial height is `r⁻¹ ℒ_w η`. -/
theorem hasDerivAt_radialHeightResidual
    {h w : ℝ → ℝ} {η : PolarPoint → ℝ} {x : PolarPoint}
    (hh : ContDiff ℝ ∞ h) (hhw : ∀ r, HasDerivAt h (w r) r)
    (hw : DifferentiableAt ℝ w x.1) (hη : ContDiff ℝ ∞ η) (hr : x.1 ≠ 0) :
    HasDerivAt (fun q => polarCoordinateResidual w (heightFamily (radialHeightField h) η q) x)
      (radialPDE w (fun r θ => η (r, θ)) x.1 x.2 / x.1) 0 := by
  have hp : 0 < polarDiscriminant w (radialHeightField h) x := by
    rw [polarDiscriminant_radialHeightField hhw]
    norm_num
  exact (hasDerivAt_polarCoordinateResidual_heightFamily w
    (contDiff_radialHeightField hh) hη hr hp).congr_deriv
      (polarResidualVariation_radialHeightField hhw hw hη hr)

/-- The removable normalized residual at zero is the actual radial PDE,
with the vanishing base numerator proved above rather than postulated. -/
theorem normalizedHeightResidual_radialHeightField_zero
    {h w : ℝ → ℝ} {η : PolarPoint → ℝ} {x : PolarPoint}
    (hhw : ∀ r, HasDerivAt h (w r) r) (hw : DifferentiableAt ℝ w x.1)
    (hη : ContDiff ℝ ∞ η) (hr : x.1 ≠ 0) :
    normalizedHeightResidual w (radialHeightField h) η 0 x =
      radialPDE w (fun r θ => η (r, θ)) x.1 x.2 := by
  rw [normalizedHeightResidual_zero, polarResidualVariation_radialHeightField hhw hw hη hr]
  field_simp [hr]

end

end ContinuousFlexibility.Radial
