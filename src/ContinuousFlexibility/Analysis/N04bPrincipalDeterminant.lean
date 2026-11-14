module

public import ContinuousFlexibility.Analysis.PrincipalCoefficientPullback

/-!
# The determinant of the actual transformed principal density

In two dimensions the two Jacobian factors in the determinant cancel the
square of the density denominator. Consequently a height-conjugated
coordinate change multiplies the physical determinant by the fourth power
of the actual height factor. This is an algebraic identity for the genuine
derivative of the chart, and does not assume a transformation law.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements

/-- The determinant of a symmetric two-dimensional congruence. -/
theorem n04b_symmetric_congruence_determinant (a b c p q r s : ℝ) :
    (a * p ^ 2 + 2 * b * p * q + c * q ^ 2) *
        (a * r ^ 2 + 2 * b * r * s + c * s ^ 2) -
      (a * p * r + b * (p * s + q * r) + c * q * s) ^ 2 =
      (p * s - q * r) ^ 2 * (a * c - b ^ 2) := by
  ring

/-- The actual coordinate principal density has no residual Jacobian in
its determinant. Only the fourth power of the height factor remains. -/
theorem n04b_coordinatePrincipalDensity_determinant
    (A : SymmetricCoefficients) (F : PolarPoint → PolarPoint)
    (h : PolarPoint → ℝ) (x : PolarPoint)
    (hJ : planeJacobian F x ≠ 0) :
    (coordinatePrincipalDensity A F h).a x *
        (coordinatePrincipalDensity A F h).c x -
      (coordinatePrincipalDensity A F h).b x ^ 2 =
      h x ^ 4 * (A.a x * A.c x - A.b x ^ 2) := by
  have hratio :
      (h x ^ 2 / |planeJacobian F x|) ^ 2 * planeJacobian F x ^ 2 =
        h x ^ 4 := by
    rw [div_pow, sq_abs, div_mul_cancel₀ _ (pow_ne_zero 2 hJ)]
    ring
  calc
    _ = (h x ^ 2 / |planeJacobian F x|) ^ 2 *
        planeJacobian F x ^ 2 * (A.a x * A.c x - A.b x ^ 2) := by
      unfold coordinatePrincipalDensity coefficientQuadratic planeJacobian
      ring
    _ = _ := by rw [hratio]

/-- A genuine Tricomi principal density forces the chart's radial
coordinate to be minus the rescaled physical determinant. -/
theorem n04b_radialCoordinate_of_normalForm
    (A : SymmetricCoefficients) (F : PolarPoint → PolarPoint)
    (h : PolarPoint → ℝ) (x : PolarPoint)
    (hJ : planeJacobian F x ≠ 0)
    (ha : (coordinatePrincipalDensity A F h).a x = 1)
    (hb : (coordinatePrincipalDensity A F h).b x = 0)
    (hc : (coordinatePrincipalDensity A F h).c x = -(F x).1) :
    (F x).1 = -(h x ^ 4 * (A.a x * A.c x - A.b x ^ 2)) := by
  have hd := n04b_coordinatePrincipalDensity_determinant A F h x hJ
  rw [ha, hb, hc, one_mul, zero_pow two_ne_zero, sub_zero] at hd
  linarith

/-- A physical determinant root must be sent to the actual canonical
turning boundary whenever the normal-form identity holds there. -/
theorem n04b_radialCoordinate_zero_of_determinant_zero
    (A : SymmetricCoefficients) (F : PolarPoint → PolarPoint)
    (h : PolarPoint → ℝ) (x : PolarPoint)
    (hJ : planeJacobian F x ≠ 0)
    (ha : (coordinatePrincipalDensity A F h).a x = 1)
    (hb : (coordinatePrincipalDensity A F h).b x = 0)
    (hc : (coordinatePrincipalDensity A F h).c x = -(F x).1)
    (hroot : A.a x * A.c x - A.b x ^ 2 = 0) :
    (F x).1 = 0 := by
  rw [n04b_radialCoordinate_of_normalForm A F h x hJ ha hb hc,
    hroot, mul_zero, neg_zero]

end ContinuousFlexibility.Analysis
