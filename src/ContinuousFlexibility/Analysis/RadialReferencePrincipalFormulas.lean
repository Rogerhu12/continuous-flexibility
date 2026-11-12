import ContinuousFlexibility.Analysis.PositiveReferenceCylinder
import ContinuousFlexibility.Analysis.CoordinateOperatorConstruction
import ContinuousFlexibility.Radial.RadialHeight

/-!
# Principal and potential formulas for a genuine radial reference chart

The Jacobian and principal field are computed from the actual derivative
of the cylindrical map. The potential uses the actual coefficient germs
at the physical point. Its radial formula therefore requires no equation
for the total coefficient fields outside that neighborhood.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped Topology ContDiff

theorem coordinatePrincipalDensity_radial_cylinder
    {A : SymmetricCoefficients} {Y H : ℝ → ℝ} {p : PolarPoint}
    (hY : DifferentiableAt ℝ Y p.1) :
    let B := coordinatePrincipalDensity A (positiveReferenceCylinderChart Y)
      (fun q : PolarPoint => H q.1)
    B.a p = H p.1 ^ 2 / |deriv Y p.1| * (A.a p * deriv Y p.1 ^ 2) ∧
      B.b p = H p.1 ^ 2 / |deriv Y p.1| * (A.b p * deriv Y p.1) ∧
      B.c p = H p.1 ^ 2 / |deriv Y p.1| * A.c p := by
  have hd : HasFDerivAt (fun q : PolarPoint => Y q.1)
      (deriv Y p.1 • ContinuousLinearMap.fst ℝ ℝ ℝ) p :=
    hY.hasDerivAt.comp_hasFDerivAt p hasFDerivAt_fst
  have hF : HasFDerivAt (positiveReferenceCylinderChart Y)
      ((deriv Y p.1 • ContinuousLinearMap.fst ℝ ℝ ℝ).prod
        (ContinuousLinearMap.snd ℝ ℝ ℝ)) p :=
    hd.prodMk hasFDerivAt_snd
  simp only [coordinatePrincipalDensity, coefficientQuadratic,
    planeJacobian_positiveReferenceCylinderChart hY, hF.fderiv,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    smul_eq_mul, mul_one, mul_zero, zero_mul, zero_pow (by decide : 2 ≠ 0),
    one_pow, add_zero, zero_add, and_self]

theorem divergenceOperator_radial_height_of_coefficient_germs
    {A : SymmetricCoefficients} {w H : ℝ → ℝ} {p : PolarPoint}
    (hw : ContDiff ℝ ∞ w) (hH : ContDiff ℝ ∞ H)
    (ha : A.a =ᶠ[𝓝 p] (fun q : PolarPoint => w q.1))
    (hb : A.b =ᶠ[𝓝 p] (fun _ : PolarPoint => (0 : ℝ))) :
    divergenceOperator A (fun q : PolarPoint => H q.1) p =
      deriv (fun r => w r * deriv H r) p.1 := by
  have hr (q : PolarPoint) :
      radialPartial (fun y : PolarPoint => H y.1) q = deriv H q.1 :=
    Radial.radialPartial_radialHeightField (hH.differentiable (by simp) q.1)
  have hθ (q : PolarPoint) :
      angularPartial (fun y : PolarPoint => H y.1) q = 0 :=
    Radial.angularPartial_radialHeightField (hH.differentiable (by simp) q.1)
  have hrad :
      (fun q => A.a q * radialPartial (fun y : PolarPoint => H y.1) q +
        A.b q * angularPartial (fun y : PolarPoint => H y.1) q) =ᶠ[𝓝 p]
      (fun q : PolarPoint => w q.1 * deriv H q.1) := by
    filter_upwards [ha] with q hqa
    rw [hr q, hθ q, hqa, mul_zero, add_zero]
  have hang :
      (fun q => A.b q * radialPartial (fun y : PolarPoint => H y.1) q +
        A.c q * angularPartial (fun y : PolarPoint => H y.1) q) =ᶠ[𝓝 p]
      (fun _ : PolarPoint => (0 : ℝ)) := by
    filter_upwards [hb] with q hqb
    rw [hqb, hθ q, zero_mul, mul_zero, add_zero]
  have hflux : DifferentiableAt ℝ (fun r => w r * deriv H r) p.1 :=
    (hw.mul (contDiff_infty_iff_deriv.mp hH).2).differentiable (by simp) p.1
  calc
    divergenceOperator A (fun q : PolarPoint => H q.1) p =
        radialPartial (fun q : PolarPoint => w q.1 * deriv H q.1) p +
          angularPartial (fun _ : PolarPoint => (0 : ℝ)) p := by
      exact congrArg₂ (fun a b : ℝ => a + b)
        (congrArg (fun D : PolarPoint →L[ℝ] ℝ => D (1, 0))
          (hrad.fderiv_eq (𝕜 := ℝ)))
        (congrArg (fun D : PolarPoint →L[ℝ] ℝ => D (0, 1))
          (hang.fderiv_eq (𝕜 := ℝ)))
    _ = deriv (fun r => w r * deriv H r) p.1 := by
      rw [show radialPartial (fun q : PolarPoint => w q.1 * deriv H q.1) p =
        deriv (fun r => w r * deriv H r) p.1 from
          Radial.radialPartial_radialHeightField hflux]
      simp only [angularPartial_const, add_zero]

theorem inverseChartPotential_radial_cylinder
    {A : SymmetricCoefficients} {w Y H : ℝ → ℝ} {p : PolarPoint}
    (hw : ContDiff ℝ ∞ w) (hH : ContDiff ℝ ∞ H)
    (hY : DifferentiableAt ℝ Y (Function.invFun Y p.1))
    (hYpos : 0 < deriv Y (Function.invFun Y p.1))
    (ha : A.a =ᶠ[𝓝 (positiveReferenceCylinderInverse Y p)]
      (fun q : PolarPoint => w q.1))
    (hb : A.b =ᶠ[𝓝 (positiveReferenceCylinderInverse Y p)]
      (fun _ : PolarPoint => (0 : ℝ))) :
    inverseChartPotential A (positiveReferenceCylinderChart Y)
      (positiveReferenceCylinderInverse Y) (fun q : PolarPoint => H q.1) p =
        H (Function.invFun Y p.1) *
          deriv (fun r => w r * deriv H r) (Function.invFun Y p.1) /
            deriv Y (Function.invFun Y p.1) := by
  have hdiv := divergenceOperator_radial_height_of_coefficient_germs hw hH ha hb
  have hJ : planeJacobian (positiveReferenceCylinderChart Y)
      (positiveReferenceCylinderInverse Y p) = deriv Y (Function.invFun Y p.1) :=
    planeJacobian_positiveReferenceCylinderChart
      (p := positiveReferenceCylinderInverse Y p) hY
  unfold inverseChartPotential
  rw [hdiv, hJ, abs_of_pos hYpos]

end ContinuousFlexibility.Analysis
