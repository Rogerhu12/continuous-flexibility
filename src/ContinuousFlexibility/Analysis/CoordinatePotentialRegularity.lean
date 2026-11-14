module

public import ContinuousFlexibility.Analysis.CoordinateOperatorConstruction
public import ContinuousFlexibility.Analysis.PointwiseCylinderJets

/-!
# Smoothness of the actual transformed potential

The potential is the height times its actual divergence, divided by the
nonzero absolute Jacobian, and then composed with the actual inverse.
All smoothness statements are pointwise and do not choose a common
neighborhood of infinite order.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

theorem contDiffAt_divergenceOperator
    {A : SymmetricCoefficients} {u : PolarPoint → ℝ} {x : PolarPoint}
    (ha : ContDiffAt ℝ ∞ A.a x) (hb : ContDiffAt ℝ ∞ A.b x)
    (hc : ContDiffAt ℝ ∞ A.c x) (hu : ContDiffAt ℝ ∞ u x) :
    ContDiffAt ℝ ∞ (divergenceOperator A u) x := by
  have hr : ContDiffAt ℝ ∞ (radialPartial u) x :=
    (hu.fderiv_right (by simp)).clm_apply contDiffAt_const
  have ht : ContDiffAt ℝ ∞ (angularPartial u) x :=
    (hu.fderiv_right (by simp)).clm_apply contDiffAt_const
  have hfluxr := (ha.mul hr).add (hb.mul ht)
  have hfluxt := (hb.mul hr).add (hc.mul ht)
  exact ((hfluxr.fderiv_right (by simp)).clm_apply
    (contDiffAt_const (c := ((1, 0) : PolarPoint)))).add
      ((hfluxt.fderiv_right (by simp)).clm_apply
        (contDiffAt_const (c := ((0, 1) : PolarPoint))))

theorem contDiffAt_inverseChartPotential
    {A : SymmetricCoefficients} {F G : PolarPoint → PolarPoint}
    {h : PolarPoint → ℝ} {p : PolarPoint}
    (ha : ContDiffAt ℝ ∞ A.a (G p)) (hb : ContDiffAt ℝ ∞ A.b (G p))
    (hc : ContDiffAt ℝ ∞ A.c (G p))
    (hF : ContDiffAt ℝ ∞ F (G p)) (hG : ContDiffAt ℝ ∞ G p)
    (hh : ContDiffAt ℝ ∞ h (G p)) (hJ : planeJacobian F (G p) ≠ 0) :
    ContDiffAt ℝ ∞ (inverseChartPotential A F G h) p := by
  have hr : ContDiffAt ℝ ∞ (fun y => fderiv ℝ F y (1, 0)) (G p) :=
    (hF.fderiv_right (by simp)).clm_apply contDiffAt_const
  have ht : ContDiffAt ℝ ∞ (fun y => fderiv ℝ F y (0, 1)) (G p) :=
    (hF.fderiv_right (by simp)).clm_apply contDiffAt_const
  have hdet : ContDiffAt ℝ ∞ (planeJacobian F) (G p) :=
    (hr.fst.mul ht.snd).sub (hr.snd.mul ht.fst)
  have hv : ContDiffAt ℝ ∞
      (fun y => h y * divergenceOperator A h y / |planeJacobian F y|) (G p) :=
    (hh.mul (contDiffAt_divergenceOperator ha hb hc hh)).fun_div
      (hdet.abs hJ) (abs_ne_zero.mpr hJ)
  exact hv.fun_comp p hG

end ContinuousFlexibility.Analysis
