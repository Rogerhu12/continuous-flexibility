module

public import ContinuousFlexibility.Analysis.PrincipalCoefficientPullback

/-!
# Principal density under a positive change of the radial differential

This is a pointwise formula for two actual coordinate maps. It applies to
the root coordinate once its actual derivative has been computed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

theorem planeJacobian_of_scaled_radial_differential
    {F G : PolarPoint → PolarPoint} {x : PolarPoint} {s : ℝ}
    (hr : fderiv ℝ G x (1, 0) =
      (s * (fderiv ℝ F x (1, 0)).1, (fderiv ℝ F x (1, 0)).2))
    (hθ : fderiv ℝ G x (0, 1) =
      (s * (fderiv ℝ F x (0, 1)).1, (fderiv ℝ F x (0, 1)).2)) :
    planeJacobian G x = s * planeJacobian F x := by
  simp only [planeJacobian, hr, hθ]
  ring

/-- A positive scale s of the radial differential multiplies the radial
density by s, leaves its mixed entry fixed, and divides its angular entry
by s. -/
theorem coordinatePrincipalDensity_of_scaled_radial_differential
    (A : SymmetricCoefficients) (h : PolarPoint → ℝ)
    {F G : PolarPoint → PolarPoint} {x : PolarPoint} {s : ℝ}
    (hs : 0 < s) (hJ : planeJacobian F x ≠ 0)
    (hr : fderiv ℝ G x (1, 0) =
      (s * (fderiv ℝ F x (1, 0)).1, (fderiv ℝ F x (1, 0)).2))
    (hθ : fderiv ℝ G x (0, 1) =
      (s * (fderiv ℝ F x (0, 1)).1, (fderiv ℝ F x (0, 1)).2)) :
    (coordinatePrincipalDensity A G h).a x =
        s * (coordinatePrincipalDensity A F h).a x ∧
      (coordinatePrincipalDensity A G h).b x =
        (coordinatePrincipalDensity A F h).b x ∧
      (coordinatePrincipalDensity A G h).c x =
        (coordinatePrincipalDensity A F h).c x / s := by
  have hAbs : |planeJacobian G x| = s * |planeJacobian F x| := by
    rw [planeJacobian_of_scaled_radial_differential hr hθ, abs_mul, abs_of_pos hs]
  have hs0 := ne_of_gt hs
  have hJ0 := abs_ne_zero.mpr hJ
  simp only [coordinatePrincipalDensity, coefficientQuadratic, hAbs, hr, hθ]
  refine ⟨?_, ?_, ?_⟩ <;> field_simp [hs0, hJ0] <;> ring

end ContinuousFlexibility.Analysis
