import ContinuousFlexibility.Analysis.PositiveReferenceCylinder
import ContinuousFlexibility.Analysis.WholePositiveCanonicalFields
import ContinuousFlexibility.Analysis.WholePositiveReferenceGauge

/-!
# The actual principal field under a fixed radial reference gauge

The radial postcomposition multiplies the three actual principal entries
by H^2 Y', H^2 and H^2/Y', respectively. The formulas are evaluated at
the same true inverse point. They do not assume coefficient matching or
a transformation rule for independent prescribed jets.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements
open scoped ContDiff

theorem coordinatePrincipalDensity_radial_postcompose
    {A : SymmetricCoefficients} {F : PolarPoint → PolarPoint}
    {h : PolarPoint → ℝ} {Y H : ℝ → ℝ} {p : PolarPoint}
    (hF : DifferentiableAt ℝ F p)
    (hY : DifferentiableAt ℝ Y (F p).1)
    (hYpos : 0 < deriv Y (F p).1) (hJ : planeJacobian F p ≠ 0) :
    let B := coordinatePrincipalDensity A F h
    let V := coordinatePrincipalDensity A (positiveReferenceCylinderChart Y ∘ F)
      (fun q => H (F q).1 * h q)
    V.a p = H (F p).1 ^ 2 * deriv Y (F p).1 * B.a p ∧
      V.b p = H (F p).1 ^ 2 * B.b p ∧
      V.c p = H (F p).1 ^ 2 / deriv Y (F p).1 * B.c p := by
  have hd : HasFDerivAt (fun q : PolarPoint => Y q.1)
      (deriv Y (F p).1 • ContinuousLinearMap.fst ℝ ℝ ℝ) (F p) :=
    hY.hasDerivAt.comp_hasFDerivAt (F p) hasFDerivAt_fst
  have hψ : HasFDerivAt (positiveReferenceCylinderChart Y)
      ((deriv Y (F p).1 • ContinuousLinearMap.fst ℝ ℝ ℝ).prod
        (ContinuousLinearMap.snd ℝ ℝ ℝ)) (F p) :=
    hd.prodMk hasFDerivAt_snd
  have hcomp := hψ.comp p hF.hasFDerivAt
  have hdet : planeJacobian (positiveReferenceCylinderChart Y ∘ F) p =
      deriv Y (F p).1 * planeJacobian F p := by
    rw [planeJacobian_comp hF hψ.differentiableAt,
      planeJacobian_positiveReferenceCylinderChart hY]
  dsimp only
  simp only [coordinatePrincipalDensity, coefficientQuadratic, hdet,
    hcomp.fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    smul_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', smul_eq_mul, abs_mul, abs_of_pos hYpos]
  constructor
  · field_simp [hYpos.ne', abs_ne_zero.mpr hJ]
    <;> ring
  constructor
  · field_simp [hYpos.ne', abs_ne_zero.mpr hJ]
    <;> ring
  · field_simp [hYpos.ne', abs_ne_zero.mpr hJ]
    <;> ring

/-- The fixed reference inverse changes the evaluation point once.
The relative transport and reciprocal height remain exactly the old
whole-positive fields. -/
theorem wholePositiveReferenceGauge_principal_formula
    (A : SymmetricCoefficients) {τ σ : PolarPoint → PolarPoint}
    {Q : PolarPoint → ℝ} {Y H : ℝ → ℝ} {l r c d : ℝ}
    (hgeometry : WholePositiveChartGeometry σ τ (wholePositiveChartHeight σ Q) l r c d)
    (hY : ContDiff ℝ ∞ Y) (hYpos : ∀ x, 0 < deriv Y x) (p : PolarPoint) :
    let χ := positiveReferenceCylinderInverse Y
    let B := wholePositiveCanonicalCoefficients A τ σ Q
    let V := inverseChartPrincipalCoefficients A
      (wholePositiveReferenceGaugeChart (positiveReferenceCylinderChart Y) σ)
      (wholePositiveReferenceGaugeInverse τ χ)
      (wholePositiveReferenceGaugeHeight (fun q : PolarPoint => H q.1) σ Q)
    V.a p = H (χ p).1 ^ 2 * deriv Y (χ p).1 * B.a (χ p) ∧
      V.b p = H (χ p).1 ^ 2 * B.b (χ p) ∧
      V.c p = H (χ p).1 ^ 2 / deriv Y (χ p).1 * B.c (χ p) := by
  let χ := positiveReferenceCylinderInverse Y
  have he := coordinatePrincipalDensity_radial_postcompose
    (A := A) (F := σ) (h := wholePositiveChartHeight σ Q) (H := H)
    (p := τ (χ p)) (hgeometry.chart_smooth.differentiable (by simp) _)
    (hY.differentiable (by simp) _) (hYpos _)
    (hgeometry.jacobian_positive _).ne'
  have hinverse : σ (τ (χ p)) = χ p := hgeometry.right_inverse (χ p)
  dsimp only at he
  rw [hinverse] at he
  dsimp only [wholePositiveReferenceGaugeChart, wholePositiveReferenceGaugeInverse,
    wholePositiveReferenceGaugeHeight, wholePositiveCanonicalCoefficients,
    inverseChartPrincipalCoefficients, Function.comp_apply]
  exact he

end ContinuousFlexibility.Analysis
