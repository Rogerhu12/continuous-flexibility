import ContinuousFlexibility.Analysis.N02ChartError
import ContinuousFlexibility.Analysis.TameElementaryCalculus

/-!
# The circle projections used by the actual return residual

The even and odd projections, and the chart coordinate of a sector
parameter, are continuous linear maps with zero derivative loss. Their
smooth tame towers therefore describe the actual decoded coordinates.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis

section Circle

variable {T : MaterialData} {γ : ℝ} {H : CircleModelData}

def circleEvenContinuousLinear (hH : IsCircleModel T γ H) :
    H.Space →L[ℝ] H.Space := circleReturnContinuousLinear hH (fun _ => 0)

theorem circleEvenContinuousLinear_apply (hH : IsCircleModel T γ H) (u : H.Space) :
    circleEvenContinuousLinear hH u = circleEvenLinear hH u := rfl

theorem circleEvenLinear_tame (hH : IsCircleModel T γ H) :
    IsTameLinear H.grading H.grading (circleEvenLinear hH) 0 0 :=
  circleReturnLinear_tame hH (fun _ => 0)

def circleOddContinuousLinear (hH : IsCircleModel T γ H) :
    H.Space →L[ℝ] H.Space :=
  ContinuousLinearMap.id ℝ H.Space - circleEvenContinuousLinear hH

theorem circleOddContinuousLinear_apply (hH : IsCircleModel T γ H) (u : H.Space) :
    circleOddContinuousLinear hH u = circleOddLinear hH u := rfl

theorem circleOddLinear_tame (hH : IsCircleModel T γ H) :
    IsTameLinear H.grading H.grading (circleOddLinear hH) 0 0 := by
  simpa only [circleOddLinear, max_self] using
    (IsTameLinear.id H.grading).sub
      (gradedSeminorm_monotone (fun n => H.level n) H.bond) (circleEvenLinear_tame hH)

theorem smoothTameOn_circleEvenLinear (hH : IsCircleModel T γ H) :
    SmoothTameOn H.grading H.grading univ (circleEvenLinear hH) :=
  smoothTameOn_continuousLinear (circleEvenContinuousLinear hH) (circleEvenLinear_tame hH)

theorem smoothTameOn_circleOddLinear (hH : IsCircleModel T γ H) :
    SmoothTameOn H.grading H.grading univ (circleOddLinear hH) :=
  smoothTameOn_continuousLinear (circleOddContinuousLinear hH) (circleOddLinear_tame hH)

end Circle

local instance n01CircleLinearTameStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

/-- The genuine chart perturbation coordinate of a sector parameter. -/
def sectorChartContinuousLinear (S : PhysicalSpacesData) :
    (StateDirections S × ℝ) →L[ℝ] CircleSpace S where
  toFun z := z.1.val.2.2.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := (continuous_subtype_val.comp continuous_fst).snd.snd.snd

theorem sectorChartContinuousLinear_apply (S : PhysicalSpacesData)
    (z : StateDirections S × ℝ) : sectorChartContinuousLinear S z = z.1.val.2.2.2 := rfl

theorem sectorParameter_chart_grading_le (S : PhysicalSpacesData) (n : ℕ)
    (z : StateDirections S × ℝ) :
    (S.circle (3 / 4 : ℝ)).grading n z.1.val.2.2.2 ≤
      pairGrading (sectorGrading S) realGrading n z := by
  have hη : 0 ≤ heightPairGrading S n z.1.val.1 := apply_nonneg _ _
  have hν : 0 ≤ realGrading n z.1.val.2.1 := apply_nonneg _ _
  have hκ : 0 ≤ (S.circle (3 / 4 : ℝ)).grading n z.1.val.2.2.1 := apply_nonneg _ _
  have hq : 0 ≤ realGrading n z.2 := apply_nonneg _ _
  change (S.circle (3 / 4 : ℝ)).grading n z.1.val.2.2.2 ≤
    (heightPairGrading S n z.1.val.1 + (realGrading n z.1.val.2.1 +
      ((S.circle (3 / 4 : ℝ)).grading n z.1.val.2.2.1 +
        (S.circle (3 / 4 : ℝ)).grading n z.1.val.2.2.2))) + realGrading n z.2
  linarith only [hη, hν, hκ, hq]

theorem sectorChartContinuousLinear_tame (S : PhysicalSpacesData) :
    IsTameLinear (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading (sectorChartContinuousLinear S).toLinearMap 0 0 := by
  intro n _
  refine ⟨1, fun z => ?_⟩
  simpa only [NNReal.coe_one, one_mul, Nat.add_zero,
    ContinuousLinearMap.coe_coe, sectorChartContinuousLinear_apply] using
      sectorParameter_chart_grading_le S n z

theorem smoothTameOn_sectorChart (S : PhysicalSpacesData) :
    SmoothTameOn (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading univ
      (fun z : StateDirections S × ℝ => z.1.val.2.2.2) :=
  smoothTameOn_continuousLinear (sectorChartContinuousLinear S)
    (sectorChartContinuousLinear_tame S)

end ContinuousFlexibility.Statements
