import ContinuousFlexibility.Analysis.PrincipalCoefficientPullback

/-!
# One radial affine normalization for both endpoint charts

The same formula covers radial reflection and translation. Its derivative
and Jacobian are actual derivatives, so the principal density identities
can be used with either endpoint's canonical coordinate.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements
open scoped ContDiff

/-- Translate and, when the slope is -1, reflect the radial output. -/
def radialAffineChart (o s : ℝ) (F : PolarPoint → PolarPoint) (x : PolarPoint) :
    PolarPoint := (s * (F x).1 + o, (F x).2)

theorem fderiv_radialAffineChart_apply
    {F : PolarPoint → PolarPoint} {x : PolarPoint}
    (hF : DifferentiableAt ℝ F x) (o s : ℝ) (v : PolarPoint) :
    fderiv ℝ (radialAffineChart o s F) x v =
      (s * (fderiv ℝ F x v).1, (fderiv ℝ F x v).2) := by
  have hd := ((hF.hasFDerivAt.fst.const_mul s).add_const o).prodMk hF.hasFDerivAt.snd
  unfold radialAffineChart
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    ContinuousLinearMap.smul_apply, smul_eq_mul]

theorem planeJacobian_radialAffineChart
    {F : PolarPoint → PolarPoint} {x : PolarPoint}
    (hF : DifferentiableAt ℝ F x) (o s : ℝ) :
    planeJacobian (radialAffineChart o s F) x = s * planeJacobian F x := by
  simp only [planeJacobian, fderiv_radialAffineChart_apply hF]
  ring

/-- Unit radial slopes preserve the diagonal entries and multiply the
mixed entry by the slope. This treats both endpoint orientations at once. -/
theorem coordinatePrincipalDensity_radialAffineChart
    (A : SymmetricCoefficients) (h : PolarPoint → ℝ)
    {F : PolarPoint → PolarPoint} {x : PolarPoint}
    (hF : DifferentiableAt ℝ F x) (o s : ℝ) (hs : s ^ 2 = 1) :
    (coordinatePrincipalDensity A (radialAffineChart o s F) h).a x =
        (coordinatePrincipalDensity A F h).a x ∧
      (coordinatePrincipalDensity A (radialAffineChart o s F) h).b x =
        s * (coordinatePrincipalDensity A F h).b x ∧
      (coordinatePrincipalDensity A (radialAffineChart o s F) h).c x =
        (coordinatePrincipalDensity A F h).c x := by
  have habs : |s| = 1 := by nlinarith [sq_abs s, abs_nonneg s]
  have hJ : |planeJacobian (radialAffineChart o s F) x| = |planeJacobian F x| := by
    rw [planeJacobian_radialAffineChart hF, abs_mul, habs, one_mul]
  refine ⟨?_, ?_, ?_⟩
  · calc
      _ = s ^ 2 * (coordinatePrincipalDensity A F h).a x := by
        simp only [coordinatePrincipalDensity, coefficientQuadratic, hJ,
          fderiv_radialAffineChart_apply hF]
        ring
      _ = _ := by rw [hs, one_mul]
  · simp only [coordinatePrincipalDensity, hJ, fderiv_radialAffineChart_apply hF]
    ring
  · simp only [coordinatePrincipalDensity, hJ, fderiv_radialAffineChart_apply hF]

end ContinuousFlexibility.Analysis
