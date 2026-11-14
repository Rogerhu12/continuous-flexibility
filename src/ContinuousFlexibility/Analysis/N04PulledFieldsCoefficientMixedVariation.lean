module

public import ContinuousFlexibility.Analysis.N04PulledFieldsCoefficientVariation

/-!
# The mixed scalar and height response of the radial coefficient

The height increment at the reference state need not vanish.  Differentiating
the actual scalar-parameter derivative once in a height direction removes
that reference increment and gives the same nonzero radial response.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements ContinuousFlexibility.Radial
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-- The mixed derivative is independent of the pre-existing height increment.
Both derivatives are derivatives of the actual coefficient function. -/
theorem n04PulledFields_hasDerivAt_radialCoefficient_mixedHeight
    {h w : ℝ → ℝ} {u v : PolarPoint → ℝ} {x : PolarPoint}
    (hh : ContDiff ℝ ∞ h) (hhw : ∀ r, HasDerivAt h (w r) r)
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) (hr : x.1 ≠ 0) (t : ℝ) :
    HasDerivAt
      (fun s => deriv (fun q => polarLinearA w
        (heightFamily (radialHeightField h) (heightFamily u v s) q) x) 0)
      ((1 + 3 * w x.1 ^ 2) * heightRadial v x +
        profileEnergy w x * angularPartial (heightAngular v) x) t := by
  have heq :
      (fun s => deriv (fun q => polarLinearA w
        (heightFamily (radialHeightField h) (heightFamily u v s) q) x) 0) =
      (fun s => (1 + 3 * w x.1 ^ 2) * heightRadial (heightFamily u v s) x +
        profileEnergy w x * angularPartial (heightAngular (heightFamily u v s)) x) := by
    funext s
    exact (n04PulledFields_hasDerivAt_radialCoefficient hh hhw
      (contDiff_heightFamily hu hv s) hr).deriv
  rw [heq]
  exact ((hasDerivAt_heightRadial_heightFamily hu hv x t).const_mul _).add
    ((hasDerivAt_angularPartial_heightAngular_heightFamily hu hv hr t).const_mul _)

/-- A radial height test detects a nonzero mixed coefficient response even
when the state already carries a nonzero angular height increment. -/
theorem n04PulledFields_hasDerivAt_radialCoefficient_mixedRadialHeight
    {h w f : ℝ → ℝ} {u : PolarPoint → ℝ} {x : PolarPoint}
    (hh : ContDiff ℝ ∞ h) (hhw : ∀ r, HasDerivAt h (w r) r)
    (hu : ContDiff ℝ ∞ u) (hf : ContDiff ℝ ∞ f) (hr : x.1 ≠ 0) (t : ℝ) :
    HasDerivAt
      (fun s => deriv (fun q => polarLinearA w
        (heightFamily (radialHeightField h)
          (heightFamily u (radialHeightField f) s) q) x) 0)
      ((1 + 3 * w x.1 ^ 2) * deriv f x.1) t := by
  have hff (r : ℝ) : HasDerivAt f (deriv f r) r :=
    (hf.differentiable (by simp) r).hasDerivAt
  apply (n04PulledFields_hasDerivAt_radialCoefficient_mixedHeight hh hhw hu
    (contDiff_radialHeightField hf) hr t).congr_deriv
  rw [heightAngular_radialHeightField hff, angularPartial_const,
    heightRadial_radialHeightField hff]
  simp only [radialHeightField, mul_zero, add_zero]

end ContinuousFlexibility.Analysis
