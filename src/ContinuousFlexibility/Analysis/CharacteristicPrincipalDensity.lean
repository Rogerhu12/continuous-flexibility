import ContinuousFlexibility.Analysis.PrincipalCoefficientPullback

/-!
# Actual characteristic travel coordinates and their principal density

The two first integrals satisfy the actual transport equations for the
speeds d+v and d-v. The differential of their half-difference and
half-sum gives a positive Jacobian and the diagonal wave density.
No coordinate transformation law is assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-- Travel and angular coordinates obtained from the two first integrals. -/
def characteristicTravelChart (U V : PolarPoint → ℝ) (x : PolarPoint) : PolarPoint :=
  ((1 / 2 : ℝ) * (V x - U x), (1 / 2 : ℝ) * (U x + V x))

theorem fderiv_characteristicTravelChart_apply
    {U V : PolarPoint → ℝ} {x : PolarPoint}
    (hU : DifferentiableAt ℝ U x) (hV : DifferentiableAt ℝ V x)
    (q : PolarPoint) :
    fderiv ℝ (characteristicTravelChart U V) x q =
      ((1 / 2 : ℝ) * (fderiv ℝ V x q - fderiv ℝ U x q),
        (1 / 2 : ℝ) * (fderiv ℝ U x q + fderiv ℝ V x q)) := by
  have hd := ((hV.hasFDerivAt.fun_sub hU.hasFDerivAt).const_mul (1 / 2 : ℝ)).prodMk
    ((hU.hasFDerivAt.fun_add hV.hasFDerivAt).const_mul (1 / 2 : ℝ))
  unfold characteristicTravelChart
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply, smul_eq_mul]

/-- The determinant is computed from the two actual characteristic
equations, with no derivative of the speeds required. -/
theorem planeJacobian_characteristicTravelChart
    {U V : PolarPoint → ℝ} {x : PolarPoint} {d v : ℝ}
    (hU : DifferentiableAt ℝ U x) (hV : DifferentiableAt ℝ V x)
    (hUr : radialPartial U x = -(d + v) * angularPartial U x)
    (hVr : radialPartial V x = -(d - v) * angularPartial V x) :
    planeJacobian (characteristicTravelChart U V) x =
      v * angularPartial U x * angularPartial V x := by
  simp only [radialPartial, angularPartial] at hUr hVr ⊢
  simp only [planeJacobian, fderiv_characteristicTravelChart_apply hU hV, hUr, hVr]
  ring

theorem planeJacobian_characteristicTravelChart_pos
    {U V : PolarPoint → ℝ} {x : PolarPoint} {d v : ℝ}
    (hU : DifferentiableAt ℝ U x) (hV : DifferentiableAt ℝ V x)
    (hUr : radialPartial U x = -(d + v) * angularPartial U x)
    (hVr : radialPartial V x = -(d - v) * angularPartial V x)
    (hv : 0 < v) (hUθ : 0 < angularPartial U x) (hVθ : 0 < angularPartial V x) :
    0 < planeJacobian (characteristicTravelChart U V) x := by
  rw [planeJacobian_characteristicTravelChart hU hV hUr hVr]
  exact mul_pos (mul_pos hv hUθ) hVθ

/-- The actual density in characteristic coordinates is the scalar
h² a v times diag(1,-1), including its mixed coefficient. -/
theorem coordinatePrincipalDensity_characteristicTravelChart
    (A : SymmetricCoefficients) (h : PolarPoint → ℝ)
    {U V : PolarPoint → ℝ} {x : PolarPoint} {d v : ℝ}
    (hU : DifferentiableAt ℝ U x) (hV : DifferentiableAt ℝ V x)
    (hUr : radialPartial U x = -(d + v) * angularPartial U x)
    (hVr : radialPartial V x = -(d - v) * angularPartial V x)
    (hb : A.b x = A.a x * d) (hc : A.c x = A.a x * (d ^ 2 - v ^ 2))
    (hv : 0 < v) (hUθ : 0 < angularPartial U x) (hVθ : 0 < angularPartial V x) :
    (coordinatePrincipalDensity A (characteristicTravelChart U V) h).a x =
        h x ^ 2 * A.a x * v ∧
      (coordinatePrincipalDensity A (characteristicTravelChart U V) h).b x = 0 ∧
      (coordinatePrincipalDensity A (characteristicTravelChart U V) h).c x =
        -(h x ^ 2 * A.a x * v) := by
  have hJ := planeJacobian_characteristicTravelChart hU hV hUr hVr
  have hJpos := planeJacobian_characteristicTravelChart_pos hU hV hUr hVr hv hUθ hVθ
  have hAbs : |planeJacobian (characteristicTravelChart U V) x| =
      v * angularPartial U x * angularPartial V x := (abs_of_pos hJpos).trans hJ
  have hv0 := ne_of_gt hv
  have hu0 := ne_of_gt hUθ
  have hw0 := ne_of_gt hVθ
  simp only [radialPartial, angularPartial] at hUr hVr hu0 hw0 hAbs
  simp only [coordinatePrincipalDensity, coefficientQuadratic,
    hAbs, fderiv_characteristicTravelChart_apply hU hV, hUr, hVr, hb, hc]
  refine ⟨?_, ?_, ?_⟩
  · field_simp [hv0, hu0, hw0]
    <;> ring
  · field_simp [hv0, hu0, hw0]
    <;> ring
  · field_simp [hv0, hu0, hw0]
    <;> ring

end ContinuousFlexibility.Analysis
