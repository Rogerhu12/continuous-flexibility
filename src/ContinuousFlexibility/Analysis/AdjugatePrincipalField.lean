module

public import ContinuousFlexibility.Analysis.CoordinatePrincipalDeterminant

/-!
# A forward-only effective principal field

The adjugate of the actual derivative gives a physical principal field
without evaluating a prescribed inverse at any boundary point. Its
regularity at a closed endpoint follows directly from the forward chart
and height there. Its determinant is an algebraic identity in those
actual first derivatives.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-- The reverse principal density written using only the forward chart:
adj(DF) A(F x) adj(DF)ᵀ divided by h(x)² |det DF(x)|. -/
def adjugateCoordinatePrincipalCoefficients (A : SymmetricCoefficients)
    (F : PolarPoint → PolarPoint) (h : PolarPoint → ℝ) : SymmetricCoefficients where
  a x := (1 / (h x ^ 2 * |planeJacobian F x|)) *
    coefficientQuadratic A (F x)
      ((fderiv ℝ F x (0, 1)).2, -(fderiv ℝ F x (0, 1)).1)
  b x := (1 / (h x ^ 2 * |planeJacobian F x|)) *
    (A.a (F x) * (fderiv ℝ F x (0, 1)).2 * (-(fderiv ℝ F x (1, 0)).2) +
      A.b (F x) * ((fderiv ℝ F x (0, 1)).2 * (fderiv ℝ F x (1, 0)).1 +
        (-(fderiv ℝ F x (0, 1)).1) * (-(fderiv ℝ F x (1, 0)).2)) +
      A.c (F x) * (-(fderiv ℝ F x (0, 1)).1) * (fderiv ℝ F x (1, 0)).1)
  c x := (1 / (h x ^ 2 * |planeJacobian F x|)) *
    coefficientQuadratic A (F x)
      (-(fderiv ℝ F x (1, 0)).2, (fderiv ℝ F x (1, 0)).1)

/-- Pointwise infinite smoothness at an endpoint is enough for the
forward-only field. No common smoothness neighborhood is assumed. -/
theorem contDiffAt_adjugateCoordinatePrincipalCoefficients
    {A : SymmetricCoefficients} {F : PolarPoint → PolarPoint}
    {h : PolarPoint → ℝ} {x : PolarPoint}
    (ha : ContDiffAt ℝ ∞ A.a (F x)) (hb : ContDiffAt ℝ ∞ A.b (F x))
    (hc : ContDiffAt ℝ ∞ A.c (F x)) (hF : ContDiffAt ℝ ∞ F x)
    (hh : ContDiffAt ℝ ∞ h x) (hJ : planeJacobian F x ≠ 0) (hh0 : h x ≠ 0) :
    ContDiffAt ℝ ∞ (adjugateCoordinatePrincipalCoefficients A F h).a x ∧
      ContDiffAt ℝ ∞ (adjugateCoordinatePrincipalCoefficients A F h).b x ∧
      ContDiffAt ℝ ∞ (adjugateCoordinatePrincipalCoefficients A F h).c x := by
  have hr : ContDiffAt ℝ ∞ (fun p => fderiv ℝ F p (1, 0)) x :=
    (hF.fderiv_right (by simp)).clm_apply contDiffAt_const
  have ht : ContDiffAt ℝ ∞ (fun p => fderiv ℝ F p (0, 1)) x :=
    (hF.fderiv_right (by simp)).clm_apply contDiffAt_const
  have hdet : ContDiffAt ℝ ∞ (planeJacobian F) x :=
    (hr.fst.mul ht.snd).sub (hr.snd.mul ht.fst)
  have hscale : ContDiffAt ℝ ∞ (fun p => 1 / (h p ^ 2 * |planeJacobian F p|)) x :=
    contDiffAt_const.fun_div ((hh.pow 2).mul (hdet.abs hJ))
      (mul_ne_zero (pow_ne_zero 2 hh0) (abs_ne_zero.mpr hJ))
  have hAa := ha.comp x hF
  have hAb := hb.comp x hF
  have hAc := hc.comp x hF
  have htwo : ContDiffAt ℝ ∞ (fun _ : PolarPoint => (2 : ℝ)) x := contDiffAt_const
  dsimp only [adjugateCoordinatePrincipalCoefficients, coefficientQuadratic]
  refine ⟨hscale.mul ?_, hscale.mul ?_, hscale.mul ?_⟩
  · exact ((hAa.mul (ht.snd.pow 2)).add
      (((htwo.mul hAb).mul ht.snd).mul ht.fst.neg)).add
        (hAc.mul (ht.fst.neg.pow 2))
  · exact (((hAa.mul ht.snd).mul hr.snd.neg).add
      (hAb.mul ((ht.snd.mul hr.fst).add (ht.fst.neg.mul hr.snd.neg)))).add
        ((hAc.mul ht.fst.neg).mul hr.fst)
  · exact ((hAa.mul (hr.snd.neg.pow 2)).add
      (((htwo.mul hAb).mul hr.snd.neg).mul hr.fst)).add
        (hAc.mul (hr.fst.pow 2))

private theorem adjugate_principal_det_scalar (a b c p q r s k : ℝ) :
    (k * (a * s ^ 2 + 2 * b * s * (-q) + c * (-q) ^ 2)) *
        (k * (a * (-r) ^ 2 + 2 * b * (-r) * p + c * p ^ 2)) -
      (k * (a * s * (-r) + b * (s * p + (-q) * (-r)) + c * (-q) * p)) ^ 2 =
      k ^ 2 * (p * s - r * q) ^ 2 * (a * c - b ^ 2) := by
  ring

/-- The determinant formula is valid at every nondegenerate forward
chart point, including the closed physical endpoints. -/
theorem adjugateCoordinatePrincipalCoefficients_determinant
    (A : SymmetricCoefficients) (F : PolarPoint → PolarPoint)
    (h : PolarPoint → ℝ) (x : PolarPoint)
    (hJ : planeJacobian F x ≠ 0) (hh0 : h x ≠ 0) :
    (adjugateCoordinatePrincipalCoefficients A F h).a x *
          (adjugateCoordinatePrincipalCoefficients A F h).c x -
        (adjugateCoordinatePrincipalCoefficients A F h).b x ^ 2 =
      (A.a (F x) * A.c (F x) - A.b (F x) ^ 2) / h x ^ 4 := by
  dsimp only [adjugateCoordinatePrincipalCoefficients, coefficientQuadratic]
  rw [adjugate_principal_det_scalar]
  change (1 / (h x ^ 2 * |planeJacobian F x|)) ^ 2 * planeJacobian F x ^ 2 *
      (A.a (F x) * A.c (F x) - A.b (F x) ^ 2) = _
  have hs : (1 / (h x ^ 2 * |planeJacobian F x|)) ^ 2 *
      planeJacobian F x ^ 2 = 1 / h x ^ 4 := by
    simp only [div_pow, one_pow, mul_pow, sq_abs]
    field_simp [hh0, hJ]
    <;> ring
  rw [hs]
  ring

end ContinuousFlexibility.Analysis
