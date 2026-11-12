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
set_option backward.isDefEq.respectTransparency.types false

private theorem coupled_chart_pair_bound
    {E F H : Type*}
    [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    [TopologicalSpace H] [AddCommGroup H] [Module ℝ H]
    (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ F) (r : ℕ → Seminorm ℝ H)
    (n : ℕ) (z : (E × F) × H) (w : H × H) (u : H)
    (hw : w = (u, z.2)) (hu : r n u ≤ p n z.1.1) :
    pairGrading r r n w ≤ pairGrading (pairGrading p q) r n z := by
  rw [hw]
  change r n u + r n z.2 ≤ (p n z.1.1 + q n z.1.2) + r n z.2
  exact add_le_add (hu.trans (le_add_of_nonneg_right (apply_nonneg (q n) z.1.2))) le_rfl

private theorem coupled_chart_last_add
    {E F H I : Type*} [Add E] [Add F] [Add H] [AddZeroClass I]
    (x y : E × (F × (H × I))) (hx : x.2.2.2 = 0) :
    (x + y).2.2.2 = y.2.2.2 := by
  change x.2.2.2 + y.2.2.2 = y.2.2.2
  rw [hx, zero_add]

private theorem coupled_chart_precomp_univ
    {X Y Z : Type*}
    [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]
    [TopologicalSpace Z] [AddCommGroup Z] [Module ℝ Z]
    {p : ℕ → Seminorm ℝ X} {q : ℕ → Seminorm ℝ Y} {r : ℕ → Seminorm ℝ Z}
    {f : Y → Z} (hf : SmoothTameOn q r univ f) (L : X →L[ℝ] Y)
    (hL : ∀ n x, q n (L x) ≤ p n x) :
    SmoothTameOn p r univ (fun x => f (L x)) := by
  have h := solve_smoothTameOn_precomp hf L (p := p) (A := 1) le_rfl
    (fun n x => (hL n x).trans_eq (one_mul _).symm)
  simpa only [Set.preimage_univ, Function.comp_def] using h

private abbrev coupledChartParameterGrading (S : PhysicalSpacesData) :=
  pairGrading (sectorGrading S) realGrading

private abbrev coupledChartInputGrading (S : PhysicalSpacesData) :=
  pairGrading (coupledChartParameterGrading S) (S.circle (3 / 4 : ℝ)).grading

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
  have h := coupled_chart_pair_bound (sectorGrading S) realGrading
    (S.circle (3 / 4 : ℝ)).grading n z (coupledCircleChartInput S z) z.1.1.val.2.2.2
    (coupledCircleChartInput_apply S z) (neighborhoodStateGrading_chart_le S n z.1.1.val)
  exact h

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {base loss : ℕ} {ε : ℝ}

private theorem coupled_chartComposition_smoothTameOn
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hγ : (0 : ℝ) < 3 / 4)
    (hM : IsCircleModel T (3 / 4 : ℝ) (S.circle (3 / 4 : ℝ)))
    (hI : HasInterpolation (S.circle (3 / 4 : ℝ)).grading) :
    SmoothTameOn (coupledChartInputGrading S) (S.circle (3 / 4 : ℝ)).grading univ
      (fun z : (StateDirections S × ℝ) × CircleSpace S =>
        coupledCircleKernel hD hT hγ hM hI 0 0 z.1.1.val.2.2.2 z.2 Fin.elim0) := by
  have hcomp := coupled_circleComposition_smoothTameOn hD hT hγ hM hI
  have hpre := coupled_chart_precomp_univ
    (X := (StateDirections S × ℝ) × CircleSpace S)
    (Y := CircleSpace S × CircleSpace S) (Z := CircleSpace S)
    (p := coupledChartInputGrading S)
    (q := pairGrading (S.circle (3 / 4 : ℝ)).grading (S.circle (3 / 4 : ℝ)).grading)
    (r := (S.circle (3 / 4 : ℝ)).grading)
    (f := fun w : CircleSpace S × CircleSpace S =>
      coupledCircleKernel hD hT hγ hM hI 0 0 w.1 w.2 Fin.elim0)
    hcomp (coupledCircleChartInput S) (coupledCircleChartInput_grading_le S)
  have h := smoothTameOn_congr hpre (fun z _ =>
    congrArg (fun w : CircleSpace S × CircleSpace S =>
      coupledCircleKernel hD hT hγ hM hI 0 0 w.1 w.2 Fin.elim0)
      (coupledCircleChartInput_apply S z))
  exact h

private theorem coupled_chartIncrement_eq_composition
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hγ : (0 : ℝ) < 3 / 4)
    (hM : IsCircleModel T (3 / 4 : ℝ) (S.circle (3 / 4 : ℝ)))
    (hI : HasInterpolation (S.circle (3 / 4 : ℝ)).grading)
    (hRef : referenceStateConditions D S C)
    (h2 : N02Properties D T S C R base ε)
    (z : StateDirections S × ℝ) (hz : z ∈ sectorNeighborhood S base ε ε)
    (v : CircleSpace S) :
    coupledCircleKernel hD hT hγ hM hI 0 0 z.1.val.2.2.2 v Fin.elim0 =
      R.chartIncrement (liftSectorParameter S C z) v := by
  have hchart : (liftSectorParameter S C z).1.2.2.2 = z.1.val.2.2.2 :=
    coupled_chart_last_add C.referenceState z.1.val hRef.2.2.2.2.1
  apply hM.2.2.2.2.2.1
  funext m θ
  have he := h2.2.2.2.2.2.1 (liftSectorParameter S C z)
    (liftSectorParameter_mem_stateNeighborhood hz le_rfl)
    (hRef.liftSectorParameter_sector z) v m θ
  have hangle : stateLeftChart S (liftSectorParameter S C z).1 m θ =
      θ + (S.circle (3 / 4 : ℝ)).decode z.1.val.2.2.2 m θ :=
    congrArg (fun ψ : CircleSpace S => θ + (S.circle (3 / 4 : ℝ)).decode ψ m θ) hchart
  exact (coupled_circleComposition_decode hD hT hγ hM hI z.1.val.2.2.2 v m θ).trans
    ((congrArg (fun t : ℝ => (S.circle (3 / 4 : ℝ)).decode v m t) hangle).symm.trans he.symm)

/-- The prescribed chart increment of any return equation satisfying N02
has its genuine joint smooth tame dependence on the original sector domain. -/
theorem coupled_chartIncrement_smoothTameOn
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S)
    (h1 : N01Properties D T S C base loss ε)
    (h2 : N02Properties D T S C R base ε) :
    SmoothTameOn (coupledChartInputGrading S)
      (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε ε ×ˢ univ)
      (fun z : (StateDirections S × ℝ) × CircleSpace S =>
        R.chartIncrement (liftSectorParameter S C z.1) z.2) := by
  let hM : IsCircleModel T (3 / 4 : ℝ) (S.circle (3 / 4 : ℝ)) := hS.2.1 (3 / 4 : ℝ)
  have hγ : (0 : ℝ) < 3 / 4 := by norm_num
  have hI : HasInterpolation (S.circle (3 / 4 : ℝ)).grading :=
    (hS.2.2.2.2.1 (3 / 4 : ℝ)).2.2
  have hcomp := coupled_chartComposition_smoothTameOn (S := S) hD hT hγ hM hI
  have hres := h2.2.2.2.2.2.2.2.2.2.2
  have hU : IsOpen (sectorNeighborhood S base ε ε ×ˢ
      (univ : Set (CircleSpace S))) := hres.choose.open_domain.prod isOpen_univ
  have hrestricted := smoothTameOn_mono hcomp hU (subset_univ _)
  have h := smoothTameOn_congr
    (f := fun z : (StateDirections S × ℝ) × CircleSpace S =>
      coupledCircleKernel hD hT hγ hM hI 0 0 z.1.1.val.2.2.2 z.2 Fin.elim0)
    (g := fun z : (StateDirections S × ℝ) × CircleSpace S =>
      R.chartIncrement (liftSectorParameter S C z.1) z.2)
    hrestricted (fun z hz => coupled_chartIncrement_eq_composition (S := S)
      hD hT hγ hM hI h1.2.2.1 h2 z.1 hz.1 z.2)
  exact h

end ContinuousFlexibility.Statements
