module

public import ContinuousFlexibility.Analysis.DivergenceFluxPullback

/-!
# Full coordinate identity for the actual conjugated operator

The principal density is identified on a neighborhood from actual fields.
Exterior differentiation of the actual pulled-back flux then gives the
divergence transformation. The height product rule produces the potential.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements Filter
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

/-- A local identity of the actual principal densities determines the full
divergence transformation, with the absolute Jacobian in either orientation. -/
theorem divergence_coordinate_change_of_density
    {A B : SymmetricCoefficients} {F : PolarPoint → PolarPoint}
    {h W : PolarPoint → ℝ} {x : PolarPoint}
    (ha : DifferentiableAt ℝ A.a x) (hb : DifferentiableAt ℝ A.b x)
    (hc : DifferentiableAt ℝ A.c x)
    (hF : ContDiffAt ℝ 2 F x) (hh : ContDiffAt ℝ 2 h x)
    (hBa : DifferentiableAt ℝ B.a (F x))
    (hBb : DifferentiableAt ℝ B.b (F x))
    (hBc : DifferentiableAt ℝ B.c (F x))
    (hW : ContDiff ℝ ∞ W) (hJ : planeJacobian F x ≠ 0)
    (hDensity : ∀ᶠ y in 𝓝 x,
      B.a (F y) = (coordinatePrincipalDensity A F h).a y ∧
      B.b (F y) = (coordinatePrincipalDensity A F h).b y ∧
      B.c (F y) = (coordinatePrincipalDensity A F h).c y) :
    divergenceOperator (heightWeightedCoefficients A h) (fun y => W (F y)) x /
        |planeJacobian F x| =
      divergenceOperator B W (F x) := by
  obtain ⟨σ, hσ, hOrientation⟩ := exists_eventually_jacobian_ratio_const hF hJ
  have hWeighted := differentiableAt_heightWeightedCoefficients ha hb hc
    (hh.differentiableAt (by norm_num))
  have hv : ContDiffAt ℝ 2 (fun y => W (F y)) x :=
    (hW.contDiffAt.of_le (by simp)).comp x hF
  let α := divergenceFlux (heightWeightedCoefficients A h) (fun y => W (F y))
  have hα : DifferentiableAt ℝ α.radial x ∧ DifferentiableAt ℝ α.angular x :=
    differentiableAt_divergenceFlux hWeighted.1 hWeighted.2.1 hWeighted.2.2 hv
  have hβ := differentiableAt_divergenceFlux hBa hBb hBc
    (hW.contDiffAt.of_le (show (2 : ℕ∞ω) ≤ ∞ by simp))
  have he : ∀ᶠ y in 𝓝 x,
      (pullbackPlaneOneForm F (divergenceFlux B W)).radial y = σ * α.radial y ∧
      (pullbackPlaneOneForm F (divergenceFlux B W)).angular y = σ * α.angular y := by
    filter_upwards [hDensity, hOrientation, hF.eventually (by norm_num)] with y hD ho hFy
    have hp := pullback_divergenceFlux_of_density
      (hFy.differentiableAt (by norm_num)) (hW.differentiable (by simp) (F y))
      hD.1 hD.2.1 hD.2.2
    simpa only [ho] using hp
  have her : (pullbackPlaneOneForm F (divergenceFlux B W)).radial =ᶠ[𝓝 x]
      (fun y => σ * α.radial y) := he.mono (fun _ hy => hy.1)
  have hea : (pullbackPlaneOneForm F (divergenceFlux B W)).angular =ᶠ[𝓝 x]
      (fun y => σ * α.angular y) := he.mono (fun _ hy => hy.2)
  have hExterior :
      exteriorCoefficient (pullbackPlaneOneForm F (divergenceFlux B W)) x =
        σ * exteriorCoefficient α x := by
    simp only [exteriorCoefficient, radialPartial, angularPartial]
    rw [hea.fderiv_eq, her.fderiv_eq]
    simp only [polar_directional_mul (differentiableAt_const σ) hα.2,
      polar_directional_mul (differentiableAt_const σ) hα.1,
      fderiv_const_apply, ContinuousLinearMap.zero_apply, zero_mul, zero_add]
    ring
  have hTransform := exteriorCoefficient_pullbackPlaneOneForm hF hβ.1 hβ.2
  rw [exteriorCoefficient_divergenceFlux] at hTransform
  have hRelation :
      σ * divergenceOperator (heightWeightedCoefficients A h) (fun y => W (F y)) x =
        divergenceOperator B W (F x) * planeJacobian F x := by
    calc
      _ = σ * exteriorCoefficient α x := by
        rw [show exteriorCoefficient α x =
          divergenceOperator (heightWeightedCoefficients A h) (fun y => W (F y)) x
          from exteriorCoefficient_divergenceFlux _ _ _]
      _ = _ := hExterior.symm.trans hTransform
  have hAbs : |planeJacobian F x| ≠ 0 := abs_ne_zero.mpr hJ
  have hσJ : σ * |planeJacobian F x| = planeJacobian F x :=
    ((div_eq_iff hAbs).mp hOrientation.self_of_nhds).symm
  apply (div_eq_iff hAbs).mpr
  apply mul_left_cancel₀ hσ
  calc
    _ = divergenceOperator B W (F x) * planeJacobian F x := hRelation
    _ = divergenceOperator B W (F x) * (σ * |planeJacobian F x|) :=
      congrArg (fun r : ℝ => divergenceOperator B W (F x) * r) hσJ.symm
    _ = _ := by ring

/-- The complete conjugated operator identity, including the actual
height-generated potential. -/
theorem heightCoordinateOperator_of_density
    {A B : SymmetricCoefficients} {F : PolarPoint → PolarPoint}
    {h W : PolarPoint → ℝ} {x : PolarPoint}
    (ha : DifferentiableAt ℝ A.a x) (hb : DifferentiableAt ℝ A.b x)
    (hc : DifferentiableAt ℝ A.c x)
    (hF : ContDiffAt ℝ 2 F x) (hh : ContDiffAt ℝ 2 h x)
    (hBa : DifferentiableAt ℝ B.a (F x))
    (hBb : DifferentiableAt ℝ B.b (F x))
    (hBc : DifferentiableAt ℝ B.c (F x))
    (hW : ContDiff ℝ ∞ W) (hJ : planeJacobian F x ≠ 0)
    (hDensity : ∀ᶠ y in 𝓝 x,
      B.a (F y) = (coordinatePrincipalDensity A F h).a y ∧
      B.b (F y) = (coordinatePrincipalDensity A F h).b y ∧
      B.c (F y) = (coordinatePrincipalDensity A F h).c y) :
    h x * divergenceOperator A (fun y => h y * W (F y)) x /
        |planeJacobian F x| =
      divergenceOperator B W (F x) +
        (h x * divergenceOperator A h x / |planeJacobian F x|) * W (F x) := by
  have hv : ContDiffAt ℝ 2 (fun y => W (F y)) x :=
    (hW.contDiffAt.of_le (by simp)).comp x hF
  rw [heightConjugation_divergence ha hb hc hh hv, add_div,
    divergence_coordinate_change_of_density ha hb hc hF hh hBa hBb hBc hW hJ hDensity]
  ring

end ContinuousFlexibility.Analysis
