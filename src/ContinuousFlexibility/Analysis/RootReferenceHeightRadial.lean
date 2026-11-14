import ContinuousFlexibility.Analysis.SeeleyReferenceRadial
import ContinuousFlexibility.Analysis.RootSmoothHeight
import ContinuousFlexibility.Analysis.PositiveReferenceCylinder

/-!
# The actual height in the radial reference construction

For the genuine radial reference chart, the angular-product denominator
is exactly one. The actual root height is consequently the inverse
square root of a times the derivative of the actual scalar coordinate.
This identifies the endpoint height used by scalar interpolation; no
equation for an arbitrarily extended height is assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-- Angular independence of the actual odd coefficient makes its
angular derivative zero; the extended reference angle has derivative one. -/
theorem rootAngularProduct_eq_one_of_reference_radial
    {G : ℝ × ℝ × ℝ → ℝ}
    (hχ : ∀ r, 0 ≤ r → ∀ θ,
      rootOddCoefficient G (r, θ) = rootOddCoefficient G (r, 0))
    (hφ : ∀ r, 0 ≤ r → ∀ θ, rootEven G (r, θ) = θ)
    {p : PolarPoint} (hχdiff : DifferentiableAt ℝ (extendedRootOddCoefficient G) p) :
    rootAngularProduct G p = 1 := by
  have hφeq : extendedRootEven G = (fun q : PolarPoint => q.2) :=
    funext (fun q => extendedRootEven_eq_angle_of_halfPlane hφ q.1 q.2)
  have hφder : angularPartial (extendedRootEven G) p = 1 := by
    rw [hφeq]
    have hs : HasFDerivAt (fun q : PolarPoint => q.2)
        (ContinuousLinearMap.snd ℝ ℝ ℝ) p := hasFDerivAt_snd
    unfold angularPartial
    rw [hs.fderiv]
    simp only [ContinuousLinearMap.coe_snd']
  have hχder : angularPartial (extendedRootOddCoefficient G) p = 0 := by
    have hline : HasDerivAt (fun η : ℝ => (p.1, η)) (0, 1) p.2 :=
      (hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2)
    have hd := hχdiff.hasFDerivAt.comp_hasDerivAt p.2 hline
    have he : extendedRootOddCoefficient G ∘ (fun η : ℝ => (p.1, η)) =
        (fun _ : ℝ => extendedRootOddCoefficient G (p.1, 0)) :=
      funext (fun η => seeleyPeriodicExtension_angle_independent hχ p.1 η)
    rw [he] at hd
    simpa only [angularPartial] using hd.unique (hasDerivAt_const p.2 _)
  rw [rootAngularProduct, hφder, hχder]
  norm_num

/-- This is an equality with the actual ordinary derivative of the
extended scalar radial coordinate, including on the reflected side. -/
theorem rootSmoothHeight_eq_reference_radial_formula
    {G : ℝ × ℝ × ℝ → ℝ} (a : PolarPoint → ℝ)
    (hχ : ∀ r, 0 ≤ r → ∀ θ,
      rootOddCoefficient G (r, θ) = rootOddCoefficient G (r, 0))
    (hφ : ∀ r, 0 ≤ r → ∀ θ, rootEven G (r, θ) = θ)
    {p : PolarPoint}
    (hχdiff : DifferentiableAt ℝ (extendedRootOddCoefficient G) p)
    (hYdiff : DifferentiableAt ℝ
      (fun r => extendedRootRadialCoordinate G (r, 0)) p.1) :
    rootSmoothHeight a G p =
      (Real.sqrt (a p *
        deriv (fun r => extendedRootRadialCoordinate G (r, 0)) p.1))⁻¹ := by
  have hchart : extendedRootEvenOddChart G =
      positiveReferenceCylinderChart
        (fun r => extendedRootRadialCoordinate G (r, 0)) :=
    funext (fun q => extendedRootEvenOddChart_radial_of_halfPlane hχ hφ q.1 q.2)
  have hJ : planeJacobian (extendedRootEvenOddChart G) p =
      deriv (fun r => extendedRootRadialCoordinate G (r, 0)) p.1 := by
    rw [hchart]
    exact planeJacobian_positiveReferenceCylinderChart hYdiff
  simp only [rootSmoothHeight, rootHeightFactor, hJ,
    rootAngularProduct_eq_one_of_reference_radial hχ hφ hχdiff, div_one]

/-- Angular independence of the physical leading coefficient now
identifies the full endpoint height with its actual zero-angle slice. -/
theorem rootSmoothHeight_reference_angle_independent
    {G : ℝ × ℝ × ℝ → ℝ} {a : PolarPoint → ℝ}
    (hχ : ∀ r, 0 ≤ r → ∀ θ,
      rootOddCoefficient G (r, θ) = rootOddCoefficient G (r, 0))
    (hφ : ∀ r, 0 ≤ r → ∀ θ, rootEven G (r, θ) = θ)
    {r : ℝ}
    (hχdiff : ∀ θ : ℝ, DifferentiableAt ℝ (extendedRootOddCoefficient G) (r, θ))
    (hYdiff : DifferentiableAt ℝ
      (fun x => extendedRootRadialCoordinate G (x, 0)) r)
    (ha : ∀ θ : ℝ, a (r, θ) = a (r, 0)) (θ : ℝ) :
    rootSmoothHeight a G (r, θ) = rootSmoothHeight a G (r, 0) := by
  rw [rootSmoothHeight_eq_reference_radial_formula a hχ hφ (hχdiff θ) hYdiff,
    rootSmoothHeight_eq_reference_radial_formula a hχ hφ (hχdiff 0) hYdiff, ha θ]

end ContinuousFlexibility.Analysis

