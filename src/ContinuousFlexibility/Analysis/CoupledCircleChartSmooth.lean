import ContinuousFlexibility.Analysis.CoupledCircleCompositionSmoothTame
import ContinuousFlexibility.Analysis.NeighborhoodCircleChartsState
import ContinuousFlexibility.Analysis.SolveNewtonBridge
import ContinuousFlexibility.Analysis.SolveReturnEquations

/-!
# Smooth tameness of the given N02 chart increment

The actual chart coordinate is a linear projection of the sector
parameter, since the reference chart is zero. Global circle composition
therefore supplies a smooth tame map on the original grading. The N02
decoding identity identifies this map with the supplied chart increment;
no replacement of the return-equation data is made.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

private def coupledCircleChartInput (S : PhysicalSpacesData) :
    ((StateDirections S × ℝ) × CircleSpace S) →L[ℝ] CircleSpace S × CircleSpace S :=
  let chart : AnnularState S →L[ℝ] CircleSpace S :=
    (ContinuousLinearMap.snd ℝ (CircleSpace S) (CircleSpace S)).comp
      ((ContinuousLinearMap.snd ℝ ℝ (CircleSpace S × CircleSpace S)).comp
        (ContinuousLinearMap.snd ℝ (HeightPair S)
          (ℝ × (CircleSpace S × CircleSpace S))))
  let parameter := (ContinuousLinearMap.fst ℝ (StateDirections S) ℝ).comp
    (ContinuousLinearMap.fst ℝ (StateDirections S × ℝ) (CircleSpace S))
  ((chart.comp (stateSectorSubmodule S).subtypeL).comp parameter).prod
    (ContinuousLinearMap.snd ℝ (StateDirections S × ℝ) (CircleSpace S))

private theorem coupledCircleChartInput_apply (S : PhysicalSpacesData)
    (z : (StateDirections S × ℝ) × CircleSpace S) :
    coupledCircleChartInput S z = (z.1.1.val.2.2.2, z.2) := rfl

private theorem coupledCircleChartInput_grading_le (S : PhysicalSpacesData)
    (n : ℕ) (z : (StateDirections S × ℝ) × CircleSpace S) :
    pairGrading (S.circle (3 / 4 : ℝ)).grading (S.circle (3 / 4 : ℝ)).grading n
        (coupledCircleChartInput S z) ≤
      pairGrading (pairGrading (sectorGrading S) realGrading)
        (S.circle (3 / 4 : ℝ)).grading n z := by
  rw [coupledCircleChartInput_apply]
  change (S.circle (3 / 4 : ℝ)).grading n z.1.1.val.2.2.2 +
      (S.circle (3 / 4 : ℝ)).grading n z.2 ≤
    (sectorGrading S n z.1.1 + realGrading n z.1.2) +
      (S.circle (3 / 4 : ℝ)).grading n z.2
  have hc : (S.circle (3 / 4 : ℝ)).grading n z.1.1.val.2.2.2 ≤
      sectorGrading S n z.1.1 :=
    neighborhoodStateGrading_chart_le S n z.1.1.val
  exact add_le_add
    (hc.trans (le_add_of_nonneg_right (apply_nonneg (realGrading n) z.1.2))) le_rfl

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {base loss : ℕ} {ε : ℝ}

/-- The prescribed chart increment of any return equation satisfying N02
has its genuine joint smooth tame dependence on the original sector domain. -/
theorem coupled_chartIncrement_smoothTameOn
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S)
    (h1 : N01Properties D T S C base loss ε)
    (h2 : N02Properties D T S C R base ε) :
    SmoothTameOn
      (pairGrading (pairGrading (sectorGrading S) realGrading)
        (S.circle (3 / 4 : ℝ)).grading)
      (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε ε ×ˢ univ)
      (fun z : (StateDirections S × ℝ) × CircleSpace S =>
        R.chartIncrement (liftSectorParameter S C z.1) z.2) := by
  let hM := hS.2.1 (3 / 4 : ℝ)
  have hγ : (0 : ℝ) < 3 / 4 := by norm_num
  have hI : HasInterpolation (S.circle (3 / 4 : ℝ)).grading :=
    (hS.2.2.2.2.1 (3 / 4 : ℝ)).2.2
  have hcomp := coupled_circleComposition_smoothTameOn hD hT hγ hM hI
  have hpre := solve_smoothTameOn_precomp hcomp (coupledCircleChartInput S)
    (p := pairGrading (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading)
    (A := 1) le_rfl (fun n z => by
      simpa only [one_mul] using coupledCircleChartInput_grading_le S n z)
  rw [Set.preimage_univ] at hpre
  have hres : SmoothTameOn (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε ε)
      (fun z => R.residual (liftSectorParameter S C z)) :=
    h2.2.2.2.2.2.2.2.2.2.2
  have hU : IsOpen (sectorNeighborhood S base ε ε ×ˢ
      (univ : Set (CircleSpace S))) := hres.choose.open_domain.prod isOpen_univ
  apply smoothTameOn_congr (smoothTameOn_mono hpre hU (subset_univ _))
  intro z hz
  have hRef : referenceStateConditions D S C := h1.2.2.1
  have hchart : (liftSectorParameter S C z.1).1.2.2.2 = z.1.1.val.2.2.2 := by
    change C.referenceState.2.2.2 + z.1.1.val.2.2.2 = z.1.1.val.2.2.2
    rw [hRef.2.2.2.2.1, zero_add]
  apply hM.2.2.2.2.2.1
  funext m θ
  change (S.circle (3 / 4 : ℝ)).decode
      (coupledCircleKernel hD hT hγ hM hI 0 0
        (coupledCircleChartInput S z).1 (coupledCircleChartInput S z).2 Fin.elim0) m θ = _
  rw [coupledCircleChartInput_apply, coupledCircleKernel_decode_apply]
  have he := h2.2.2.2.2.2.1 (liftSectorParameter S C z.1)
    (liftSectorParameter_mem_stateNeighborhood hz.1 le_rfl)
    (hRef.liftSectorParameter_sector z.1) z.2 m θ
  simpa only [iteratedDeriv_zero, Fin.prod_univ_zero, mul_one,
    stateLeftChart, hchart] using he.symm

end ContinuousFlexibility.Statements
