import ContinuousFlexibility.Analysis.CircleAveragedCompositionTame
import ContinuousFlexibility.Analysis.CircleDifferentialOperators
import ContinuousFlexibility.Statements.Nonlinear

/-!
# The actual bilinear chart error in N02

Products, angular differentiation, fixed shifted composition, and the
unit-interval average all act in the supplied weighted circle model.
Their composition realizes the prescribed bilinear error exactly.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open ContinuousFlexibility.Analysis MeasureTheory
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

section CircleOperators

variable {D : ReferenceData} {T : MaterialData} {γ : ℝ} {S : CircleModelData}

def circleEvenLinear (hS : IsCircleModel T γ S) : S.Space →ₗ[ℝ] S.Space :=
  circleReturnLinear hS (fun _ => 0)

theorem circleEvenLinear_decode (hS : IsCircleModel T γ S)
    (u : S.Space) (m : ℕ) (θ : ℝ) :
    S.decode (circleEvenLinear hS u) m θ = evenPart (S.decode u m) θ := by
  simpa only [circleEvenLinear, circleReturnShift, circleReturnEven, add_zero, evenPart] using
    circleReturnLinear_decode hS (fun _ => 0) u m θ

def circleOddLinear (hS : IsCircleModel T γ S) : S.Space →ₗ[ℝ] S.Space :=
  LinearMap.id - circleEvenLinear hS

theorem circleOddLinear_decode (hS : IsCircleModel T γ S)
    (u : S.Space) (m : ℕ) (θ : ℝ) :
    S.decode (circleOddLinear hS u) m θ = oddPart (S.decode u m) θ := by
  change S.decode (u - circleEvenLinear hS u) m θ = _
  rw [map_sub]
  simp only [Pi.sub_apply, circleEvenLinear_decode, evenPart, oddPart]
  ring

def circleChartErrorBilinear
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (travel : ℕ → ℝ) (e : S.Space) :
    S.Space →ₗ[ℝ] S.Space →ₗ[ℝ] S.Space :=
  let P := circleProductBilinear hS hT hD hγ
  let Dθ := circleDerivativeLinear hS
  let A := circleAverageComposeLinear hS hT hD hγ travel e
  let V := circleShiftedChartComposeLinear hS hT hD hγ travel e
  (P.compl₂ (A.comp Dθ)).compr₂ₛₗ (circleEvenLinear hS) -
    P.compl₁₂ Dθ ((circleOddLinear hS).comp V)

theorem circleChartErrorBilinear_decode
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (travel : ℕ → ℝ) (e r v : S.Space) (m : ℕ) (θ : ℝ) :
    S.decode (circleChartErrorBilinear hS hT hD hγ travel e r v) m θ =
      evenPart (fun t => S.decode r m t *
        ∫ a in (0 : ℝ)..1, deriv (S.decode v m)
          (t + travel m + a * S.decode e m t)) θ -
      deriv (S.decode r m) θ *
        oddPart (fun t => S.decode v m (t + travel m + S.decode e m t)) θ := by
  change S.decode
    (circleEvenLinear hS (circleProductBilinear hS hT hD hγ r
      (circleAverageComposeLinear hS hT hD hγ travel e (circleDerivativeLinear hS v))) -
      circleProductBilinear hS hT hD hγ (circleDerivativeLinear hS r)
        (circleOddLinear hS (circleShiftedChartComposeLinear hS hT hD hγ travel e v))) m θ = _
  simp only [map_sub, Pi.sub_apply, circleEvenLinear_decode, circleProductBilinear_decode,
    circleAverageComposeLinear_decode, circleDerivativeLinear_decode, circleOddLinear_decode,
    circleShiftedChartComposeLinear_decode, evenPart, oddPart]

end CircleOperators

section ActualError

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}

def actualChartError (hS : IsPhysicalSpaces D T S)
    (hT : IsMaterialData D T) (hD : IsAccumulatingProfile D)
    (C : NonlinearGeometryData S) (e : CircleSpace S) :
    CircleSpace S →ₗ[ℝ] CircleSpace S →ₗ[ℝ] CircleSpace S :=
  circleChartErrorBilinear (hS.2.1 (3 / 4 : ℝ)) hT hD
    (by norm_num : (0 : ℝ) < 3 / 4) C.travel e

theorem actualChartError_decode (hS : IsPhysicalSpaces D T S)
    (hT : IsMaterialData D T) (hD : IsAccumulatingProfile D)
    (C : NonlinearGeometryData S) (z : AnnularState S × ℝ) (e : CircleSpace S)
    (he : (S.circle (3 / 4 : ℝ)).decode e = returnResidualField S C z)
    (r v : CircleSpace S) (m : ℕ) (θ : ℝ) :
    (S.circle (3 / 4 : ℝ)).decode (actualChartError hS hT hD C e r v) m θ =
      circleChartError S C z r v m θ := by
  simpa only [actualChartError, circleChartError, he] using
    circleChartErrorBilinear_decode (hS.2.1 (3 / 4 : ℝ)) hT hD
      (by norm_num : (0 : ℝ) < 3 / 4) C.travel e r v m θ

end ActualError

end ContinuousFlexibility.Statements
