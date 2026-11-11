import ContinuousFlexibility.Scalar.Conservation
import ContinuousFlexibility.Scalar.Normalization
import ContinuousFlexibility.Radial.RadialHeight
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Conservation of the actual normalized height source

The nonzero-parameter source inherits conservation from the actual height
connection. At parameter zero the radial Jacobi operator is the exterior
derivative of an actual flux one-form. Thus the removable value satisfies
the same compatibility condition, without interchanging a parameter limit
and an integral or postulating zero mean.
-/

noncomputable section

namespace ContinuousFlexibility

open Set MeasureTheory
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

/-- The radial Jacobi flux, in the exterior-derivative convention
`dα = (∂r αθ - ∂θ αr) dr ∧ dθ`. -/
def radialJacobiFlux (w : ℝ → ℝ) (η : PolarPoint → ℝ) : PlaneOneForm :=
  ⟨fun x => -(deriv w x.1 / x.1) * angularPartial η x,
   fun x => w x.1 * radialPartial η x⟩

theorem contDiffAt_radialJacobiFlux
    {w : ℝ → ℝ} {η : PolarPoint → ℝ} {x : PolarPoint}
    (hw : ContDiffAt ℝ ∞ w x.1) (hη : ContDiffAt ℝ ∞ η x) (hr : x.1 ≠ 0) :
    ContDiffAt ℝ 1 (radialJacobiFlux w η).radial x ∧
      ContDiffAt ℝ 1 (radialJacobiFlux w η).angular x := by
  have hdw : ContDiffAt ℝ 1 (deriv w) x.1 := hw.derivWithin (by simp)
  constructor
  · exact (((hdw.comp x contDiffAt_fst).div contDiffAt_fst hr).neg).mul
      (contDiffAt_angularPartial hη (by simp))
  · exact ((hw.of_le (by simp)).comp x contDiffAt_fst).mul
      (contDiffAt_radialPartial hη (by simp))

/-- The flux identity uses actual spatial partials and the actual radial
PDE, rather than freely specified second jets. -/
theorem radialJacobiFlux_exterior_eq_radialPDE
    {w : ℝ → ℝ} {η : PolarPoint → ℝ} {x : PolarPoint}
    (hw : ContDiffAt ℝ ∞ w x.1) (hη : ContDiff ℝ ∞ η) (hr : x.1 ≠ 0) :
    exteriorCoefficient (radialJacobiFlux w η) x =
      Radial.radialPDE w (fun r θ => η (r, θ)) x.1 x.2 := by
  have hdw : DifferentiableAt ℝ (deriv w) x.1 :=
    (hw.derivWithin (m := 1) (by simp)).differentiableAt one_ne_zero
  have hcoef : DifferentiableAt ℝ (fun r => deriv w r / r) x.1 :=
    hdw.div differentiableAt_id hr
  have hcoeff : DifferentiableAt ℝ (fun y : PolarPoint => deriv w y.1 / y.1) x :=
    hcoef.comp x differentiableAt_fst
  have hcoeft : angularPartial (fun y : PolarPoint => deriv w y.1 / y.1) x = 0 :=
    Radial.angularPartial_radialHeightField hcoef
  have hwf : DifferentiableAt ℝ (fun y : PolarPoint => w y.1) x :=
    (hw.differentiableAt (by simp)).comp x differentiableAt_fst
  have hwfr : radialPartial (fun y : PolarPoint => w y.1) x = deriv w x.1 :=
    Radial.radialPartial_radialHeightField (hw.differentiableAt (by simp))
  have hηr : DifferentiableAt ℝ (radialPartial η) x :=
    (contDiffAt_radialPartial hη.contDiffAt (m := 1) (by simp)).differentiableAt one_ne_zero
  have hηθ : DifferentiableAt ℝ (angularPartial η) x :=
    (contDiffAt_angularPartial hη.contDiffAt (m := 1) (by simp)).differentiableAt one_ne_zero
  have hprod : DifferentiableAt ℝ
      (fun y : PolarPoint => (deriv w y.1 / y.1) * angularPartial η y) x :=
    hcoeff.mul hηθ
  have hneg : (fun y : PolarPoint => -(deriv w y.1 / y.1) * angularPartial η y) =
      (fun y => (-1 : ℝ) * ((deriv w y.1 / y.1) * angularPartial η y)) := by
    funext y
    ring
  rw [Radial.radialPDE_eq_polar_jets (hw.differentiableAt (by simp)) hη]
  unfold exteriorCoefficient radialJacobiFlux
  dsimp only
  rw [radialPartial_mul hwf hηr, hwfr,
    hneg, angularPartial_mul (differentiableAt_const (-1 : ℝ)) hprod,
    angularPartial_const, angularPartial_mul hcoeff hηθ, hcoeft]
  ring

/-- Periodicity and zero endpoint profile give conservation of the actual
radial Jacobi operator. No endpoint condition on the height is needed. -/
theorem integral_mean_radialPDE_eq_zero
    {w : ℝ → ℝ} {η : PolarPoint → ℝ} {a b T : ℝ}
    (hw : ∀ r ∈ uIcc a b, ContDiffAt ℝ ∞ w r)
    (hη : ContDiff ℝ ∞ η)
    (hr : ∀ r ∈ uIcc a b, r ≠ 0)
    (hperiod : Function.Periodic η (0, T)) (hwa : w a = 0) (hwb : w b = 0) :
    (∫ r in a..b, (1 / T) * ∫ θ in 0..T,
      Radial.radialPDE w (fun r θ => η (r, θ)) r θ) = 0 := by
  have hflux := fun x (hx : x ∈ uIcc a b ×ˢ uIcc 0 T) =>
    contDiffAt_radialJacobiFlux (hw x.1 hx.1) hη.contDiffAt (hr x.1 hx.1)
  have hp : ∀ r ∈ uIcc a b,
      (radialJacobiFlux w η).radial (r, T) = (radialJacobiFlux w η).radial (r, 0) := by
    intro r _
    have ht := periodic_angularPartial hperiod (r, 0)
    simp only [Prod.mk_add_mk, add_zero, zero_add] at ht
    simp only [radialJacobiFlux, ht]
  have hb : ∀ θ ∈ uIcc 0 T,
      (radialJacobiFlux w η).angular (b, θ) = (radialJacobiFlux w η).angular (a, θ) := by
    intro θ _
    simp [radialJacobiFlux, hwa, hwb]
  have hi := integral_exteriorCoefficient_eq_zero
    (fun x hx => (hflux x hx).1) (fun x hx => (hflux x hx).2) hp hb
  rw [intervalIntegral.integral_const_mul]
  have heq : (∫ r in a..b, ∫ θ in 0..T,
      Radial.radialPDE w (fun r θ => η (r, θ)) r θ) = 0 := by
    convert hi using 1
    apply intervalIntegral.integral_congr
    intro r hrr
    apply intervalIntegral.integral_congr
    intro θ _
    exact (radialJacobiFlux_exterior_eq_radialPDE (x := (r, θ))
      (hw r hrr) hη (hr r hrr)).symm
  rw [heq, mul_zero]

/-- The actual radial base makes the normalized source genuinely smooth
through parameter zero. Here `w = h'`, so no extra differentiability or
discriminant hypothesis is needed beyond the smooth primitive and height. -/
theorem contDiffAt_normalizedHeightResidual_radialHeight_zero
    {h w : ℝ → ℝ} {η : PolarPoint → ℝ} {x : PolarPoint}
    (hh : ContDiff ℝ ∞ h) (hhw : ∀ r, HasDerivAt h (w r) r)
    (hη : ContDiff ℝ ∞ η) (hr : x.1 ≠ 0) :
    ContDiffAt ℝ ∞
      (fun q => normalizedHeightResidual w (Radial.radialHeightField h) η q x) 0 := by
  have h2 : ContDiff ℝ 2 h := hh.of_le (by simp)
  have heq : w = deriv h := funext (fun r => (hhw r).deriv.symm)
  have hw : DifferentiableAt ℝ w x.1 := by
    rw [heq]
    exact h2.differentiable_deriv_two x.1
  apply contDiffAt_normalizedHeightResidual_of_residual_zero w
    (Radial.contDiff_radialHeightField hh) hη hr
  · rw [Radial.polarDiscriminant_radialHeightField hhw]
    norm_num
  · exact Radial.polarCoordinateResidual_radialHeightField hhw hw

/-- At any nonzero parameter, conservation follows directly from the
connection of the actual trial height and its first boundary jets. -/
theorem integral_mean_normalizedHeightResidual_eq_zero_of_ne_zero
    {w : ℝ → ℝ} {z η : PolarPoint → ℝ} {a b T q : ℝ} (hq : q ≠ 0)
    (hw : ∀ x ∈ uIcc a b ×ˢ uIcc 0 T, ContDiffAt ℝ ∞ w x.1)
    (hz : ∀ x ∈ uIcc a b ×ˢ uIcc 0 T, ContDiffAt ℝ ∞ (heightFamily z η q) x)
    (hr : ∀ x ∈ uIcc a b ×ˢ uIcc 0 T, x.1 ≠ 0)
    (hD : ∀ x ∈ uIcc a b ×ˢ uIcc 0 T,
      0 < polarDiscriminant w (heightFamily z η q) x)
    (hperiod : Function.Periodic (heightFamily z η q) (0, T))
    (hwa : w a = 0) (hwb : w b = 0)
    (hka : ∀ θ ∈ uIcc 0 T, heightRadial (heightFamily z η q) (a, θ) = 0)
    (hpa : ∀ θ ∈ uIcc 0 T, heightAngular (heightFamily z η q) (a, θ) = 0)
    (hkb : ∀ θ ∈ uIcc 0 T, heightRadial (heightFamily z η q) (b, θ) = 0)
    (hpb : ∀ θ ∈ uIcc 0 T, heightAngular (heightFamily z η q) (b, θ) = 0) :
    (∫ r in a..b, (1 / T) * ∫ θ in 0..T,
      normalizedHeightResidual w z η q (r, θ)) = 0 := by
  simp_rw [normalizedHeightResidual_of_ne_zero w z η _ hq,
    intervalIntegral.integral_div, ← mul_div_assoc]
  rw [intervalIntegral.integral_div,
    integral_mean_heightResidual_eq_zero_of_boundary_jets
      hw hz hr hD hperiod hwa hwb hka hpa hkb hpb, zero_div]

/-- The actual normalized source at a radial zero-residual base has zero
mean at every parameter, including its genuine removable value at zero.
Positivity is needed only for the current trial height. The endpoint
conditions are the actual first partials of the perturbation. -/
theorem integral_mean_normalizedHeightResidual_radialHeight_eq_zero
    {h w : ℝ → ℝ} {η : PolarPoint → ℝ} {a b T q : ℝ}
    (hh : ContDiff ℝ ∞ h) (hhw : ∀ r, HasDerivAt h (w r) r)
    (hw : ∀ r ∈ uIcc a b, ContDiffAt ℝ ∞ w r) (hη : ContDiff ℝ ∞ η)
    (hr : ∀ r ∈ uIcc a b, r ≠ 0)
    (hD : ∀ x ∈ uIcc a b ×ˢ uIcc 0 T,
      0 < polarDiscriminant w (heightFamily (Radial.radialHeightField h) η q) x)
    (hperiod : Function.Periodic η (0, T)) (hwa : w a = 0) (hwb : w b = 0)
    (hka : ∀ θ ∈ uIcc 0 T, heightRadial η (a, θ) = 0)
    (hpa : ∀ θ ∈ uIcc 0 T, heightAngular η (a, θ) = 0)
    (hkb : ∀ θ ∈ uIcc 0 T, heightRadial η (b, θ) = 0)
    (hpb : ∀ θ ∈ uIcc 0 T, heightAngular η (b, θ) = 0) :
    (∫ r in a..b, (1 / T) * ∫ θ in 0..T,
      normalizedHeightResidual w (Radial.radialHeightField h) η q (r, θ)) = 0 := by
  by_cases hq : q = 0
  · subst q
    convert integral_mean_radialPDE_eq_zero hw hη hr hperiod hwa hwb using 1
    apply intervalIntegral.integral_congr
    intro r hrr
    change (1 / T) * (∫ θ in 0..T,
      normalizedHeightResidual w (Radial.radialHeightField h) η 0 (r, θ)) =
      (1 / T) * (∫ θ in 0..T, Radial.radialPDE w (fun r θ => η (r, θ)) r θ)
    apply congrArg (fun s : ℝ => (1 / T) * s)
    apply intervalIntegral.integral_congr
    intro θ _
    exact Radial.normalizedHeightResidual_radialHeightField_zero (x := (r, θ)) hhw
      ((hw r hrr).differentiableAt (by simp)) hη (hr r hrr)
  · have hz := Radial.contDiff_radialHeightField hh
    have htrial := contDiff_heightFamily hz hη q
    have hp : Function.Periodic (heightFamily (Radial.radialHeightField h) η q) (0, T) := by
      intro x
      simp only [heightFamily, Radial.radialHeightField, Prod.fst_add, add_zero, hperiod x]
    have hdiffz := hz.differentiable (by simp)
    have hdiffη := hη.differentiable (by simp)
    apply integral_mean_normalizedHeightResidual_eq_zero_of_ne_zero hq
      (fun x hx => hw x.1 hx.1) (fun _ _ => htrial.contDiffAt)
      (fun x hx => hr x.1 hx.1) hD hp hwa hwb
    all_goals intro θ hθ
    · rw [heightRadial_heightFamily hdiffz hdiffη,
        Radial.heightRadial_radialHeightField hhw]
      simp [heightFamily, Radial.radialHeightField, hwa, hka θ hθ]
    · rw [heightAngular_heightFamily hdiffz hdiffη,
        Radial.heightAngular_radialHeightField hhw]
      simp [heightFamily, hpa θ hθ]
    · rw [heightRadial_heightFamily hdiffz hdiffη,
        Radial.heightRadial_radialHeightField hhw]
      simp [heightFamily, Radial.radialHeightField, hwb, hkb θ hθ]
    · rw [heightAngular_heightFamily hdiffz hdiffη,
        Radial.heightAngular_radialHeightField hhw]
      simp [heightFamily, hpb θ hθ]

end ContinuousFlexibility
