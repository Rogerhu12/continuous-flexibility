import ContinuousFlexibility.Scalar.FormPullback
import Mathlib.LinearAlgebra.Basis.Fin
import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Measure conversion for canonical sources

The physical source factor is the height factor divided by the absolute
Jacobian.  This file connects the coordinate definition of that Jacobian
with the determinant in the change-of-variables theorem and proves the
resulting pairing formula.  The formula does not assume integrability:
the change-of-variables theorem treats both integrals with the same
totalized Bochner-integral convention.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory

/-- The coordinate formula is the determinant of the actual Fréchet
derivative, in the ordered basis `(1, 0), (0, 1)`. -/
theorem planeJacobian_eq_fderiv_det (F : PolarPoint → PolarPoint) (x : PolarPoint) :
    planeJacobian F x = (fderiv ℝ F x).det := by
  rw [← LinearMap.det_toMatrix (Basis.finTwoProd ℝ)]
  simp only [Matrix.det_fin_two, LinearMap.toMatrix_apply,
    Basis.finTwoProd_zero, Basis.finTwoProd_one, Basis.coe_finTwoProd_repr,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  unfold planeJacobian
  ring

/-- Replacing the half-open angular period by the open period only removes
a null boundary line. -/
theorem polarStrip_Ioc_ae_eq_Ioo (a b c d : ℝ) :
    (Ioo a b ×ˢ Ioc c d : Set PolarPoint) =ᵐ[volume] (Ioo a b ×ˢ Ioo c d) := by
  exact set_prod_ae_eq Filter.EventuallyEq.rfl Ioo_ae_eq_Ioc.symm

/-- Source and unknown factors cancel under a genuine coordinate change.
Only the geometric data on the integration domain are used. -/
theorem integral_pairing_eq_canonical_of_image
    {F G : PolarPoint → PolarPoint} {h : PolarPoint → ℝ}
    {U V : Set PolarPoint} (hU : MeasurableSet U)
    (hF : ∀ x ∈ U, DifferentiableAt ℝ F x)
    (hinv : ∀ x ∈ U, G (F x) = x) (himage : F '' U = V)
    (hh : ∀ x ∈ U, h x ≠ 0)
    (hJ : ∀ x ∈ U, planeJacobian F x ≠ 0)
    (u f : PolarPoint → ℝ) :
    (∫ x in U, u x * f x) =
      ∫ y in V, (u (G y) / h (G y)) *
        (h (G y) * f (G y) / |planeJacobian F (G y)|) := by
  have hi : InjOn F U := by
    intro x hx y hy hxy
    calc
      x = G (F x) := (hinv x hx).symm
      _ = G (F y) := congrArg G hxy
      _ = y := hinv y hy
  have hd : ∀ x ∈ U, HasFDerivWithinAt F (fderiv ℝ F x) U x :=
    fun x hx => (hF x hx).hasFDerivAt.hasFDerivWithinAt
  have hc := integral_image_eq_integral_abs_det_fderiv_smul
    (volume : Measure PolarPoint) hU hd hi
    (fun y => (u (G y) / h (G y)) *
      (h (G y) * f (G y) / |planeJacobian F (G y)|))
  rw [himage] at hc
  rw [hc]
  apply setIntegral_congr_fun hU
  intro x hx
  rw [hinv x hx, ← planeJacobian_eq_fderiv_det]
  simp only [smul_eq_mul]
  field_simp [hh x hx, abs_ne_zero.mpr (hJ x hx)] <;> ring

end ContinuousFlexibility.Analysis
