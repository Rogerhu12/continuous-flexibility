module

public import ContinuousFlexibility.Analysis.DivergenceConjugation

/-!
# The actual flux under a coordinate change

A divergence operator is the exterior derivative of its flux one-form.
Pulling back this actual form gives the principal density transformation,
including the orientation factor of the Jacobian.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements Filter
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

/-- The one-form whose exterior derivative is the actual divergence. -/
def divergenceFlux (A : SymmetricCoefficients) (u : PolarPoint → ℝ) : PlaneOneForm where
  radial x := -(A.b x * radialPartial u x + A.c x * angularPartial u x)
  angular x := A.a x * radialPartial u x + A.b x * angularPartial u x

theorem exteriorCoefficient_divergenceFlux
    (A : SymmetricCoefficients) (u : PolarPoint → ℝ) (x : PolarPoint) :
    exteriorCoefficient (divergenceFlux A u) x = divergenceOperator A u x := by
  simp only [exteriorCoefficient, divergenceFlux, divergenceOperator,
    radialPartial, angularPartial, fderiv_fun_neg, neg_apply]
  ring

theorem differentiableAt_divergenceFlux
    {A : SymmetricCoefficients} {u : PolarPoint → ℝ} {x : PolarPoint}
    (ha : DifferentiableAt ℝ A.a x) (hb : DifferentiableAt ℝ A.b x)
    (hc : DifferentiableAt ℝ A.c x) (hu : ContDiffAt ℝ 2 u x) :
    DifferentiableAt ℝ (divergenceFlux A u).radial x ∧
      DifferentiableAt ℝ (divergenceFlux A u).angular x := by
  have hr := (contDiffAt_radialPartial hu (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have ht := (contDiffAt_angularPartial hu (m := 1) (by norm_num)).differentiableAt one_ne_zero
  exact ⟨((hb.fun_mul hr).fun_add (hc.fun_mul ht)).fun_neg,
    (ha.fun_mul hr).fun_add (hb.fun_mul ht)⟩

/-- The value identity is algebra after the genuine chain rule. It holds
with either orientation and uses the actual derivative of the chart. -/
theorem pullback_divergenceFlux_of_density
    {A B : SymmetricCoefficients} {F : PolarPoint → PolarPoint}
    {h W : PolarPoint → ℝ} {x : PolarPoint}
    (hF : DifferentiableAt ℝ F x) (hW : DifferentiableAt ℝ W (F x))
    (ha : B.a (F x) = (coordinatePrincipalDensity A F h).a x)
    (hb : B.b (F x) = (coordinatePrincipalDensity A F h).b x)
    (hc : B.c (F x) = (coordinatePrincipalDensity A F h).c x) :
    (pullbackPlaneOneForm F (divergenceFlux B W)).radial x =
        (planeJacobian F x / |planeJacobian F x|) *
          (divergenceFlux (heightWeightedCoefficients A h) (fun y => W (F y))).radial x ∧
      (pullbackPlaneOneForm F (divergenceFlux B W)).angular x =
        (planeJacobian F x / |planeJacobian F x|) *
          (divergenceFlux (heightWeightedCoefficients A h) (fun y => W (F y))).angular x := by
  have hd (v : PolarPoint) :
      fderiv ℝ (fun y => W (F y)) x v =
        (fderiv ℝ F x v).1 * radialPartial W (F x) +
          (fderiv ℝ F x v).2 * angularPartial W (F x) := by
    rw [fderiv_fun_comp x hW hF, ContinuousLinearMap.comp_apply]
    exact polarCLM_apply_decompose (fderiv ℝ W (F x)) (fderiv ℝ F x v)
  constructor <;>
    simp only [pullbackPlaneOneForm, PlaneOneForm.toCLM_apply, formValue,
      divergenceFlux, ha, hb, hc, coordinatePrincipalDensity,
      coefficientQuadratic, heightWeightedCoefficients,
      radialPartial, angularPartial, hd, planeJacobian] <;> ring

/-- At a nondegenerate C² point the actual orientation factor is constant
on a neighborhood. No orientation convention is imposed on the chart. -/
theorem exists_eventually_jacobian_ratio_const
    {F : PolarPoint → PolarPoint} {x : PolarPoint}
    (hF : ContDiffAt ℝ 2 F x) (hJ : planeJacobian F x ≠ 0) :
    ∃ σ : ℝ, σ ≠ 0 ∧
      ∀ᶠ y in 𝓝 x, planeJacobian F y / |planeJacobian F y| = σ := by
  have hDF : ContinuousAt (fderiv ℝ F) x :=
    (hF.fderiv_right (m := 1) (by norm_num)).continuousAt
  have hr := hDF.clm_apply (continuousAt_const (y := ((1, 0) : PolarPoint)))
  have ht := hDF.clm_apply (continuousAt_const (y := ((0, 1) : PolarPoint)))
  have hJc : ContinuousAt (planeJacobian F) x := by
    exact (hr.fst.mul ht.snd).sub (hr.snd.mul ht.fst)
  rcases lt_or_gt_of_ne hJ with hn | hp
  · refine ⟨-1, by norm_num, ?_⟩
    have he : ∀ᶠ y in 𝓝 x, planeJacobian F y < 0 :=
      hJc.eventually (isOpen_Iio.mem_nhds hn)
    filter_upwards [he] with y hy
    rw [abs_of_neg hy, div_neg, div_self hy.ne]
  · refine ⟨1, one_ne_zero, ?_⟩
    have he : ∀ᶠ y in 𝓝 x, 0 < planeJacobian F y :=
      hJc.eventually (isOpen_Ioi.mem_nhds hp)
    filter_upwards [he] with y hy
    rw [abs_of_pos hy, div_self hy.ne']

end ContinuousFlexibility.Analysis
