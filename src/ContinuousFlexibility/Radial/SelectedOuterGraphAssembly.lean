import ContinuousFlexibility.Radial.SelectedOuterWeakAssembly
import ContinuousFlexibility.Radial.SelectedOuterTraceAssembly

/-!
# The constructed bounded exterior operator satisfies the frozen graph

Every input below is a proved property of the two actual regional
operators. Neither a matching realization nor a separated-graph right
inverse is assumed. The scalar component is set to zero by construction.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory Real
open scoped Topology ContDiff
open ContinuousFlexibility.Statements ContinuousFlexibility.Analysis

theorem radialOuterPairOperator_graph {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D) (M : RadialMatchingData D)
    (ha : D.a < M.innerLeft) (hm : M.innerLeft < M.innerRight) (hb : M.innerRight < D.b)
    (hlam : ∀ i, 0 < M.boundaryScale i)
    (R : ∀ right : Bool,
      Lp ℝ 2 ((radialHilbertMeasure D).restrict
        (radialTailInterval D right (if right then M.innerRight else M.innerLeft))) →L[ℝ]
      Lp ℝ 2 ((radialHilbertMeasure D).restrict
        (radialTailInterval D right (if right then M.innerRight else M.innerLeft))))
    (hweak : ∀ right, RadialTailWeakPairing D hD right
      (if right then M.innerRight else M.innerLeft) M.frequency (R right))
    (hregular : ∀ right,
      let i : Fin 2 := if right then 1 else 0
      RadialTailRegularResponse D right (if right then M.innerRight else M.innerLeft)
        (M.boundaryScale i) (M.A i i, M.B i i) (R right))
    (F : RadialModePair D) :
    ModeOuterSeparatedGraph D M
      (radialOuterPairOperator D M.innerLeft M.innerRight (R false) (R true) F) F := by
  classical
  let G := radialOuterPairOperator D M.innerLeft M.innerRight (R false) (R true)
  have hdata (right : Bool) := hregular right
    (l2Restrict (radialHilbertMeasure D)
      (radialTailInterval D right (if right then M.innerRight else M.innerLeft)) F.1)
  choose u he hu hRobin using hdata
  let v := radialOuterGlue M.innerLeft M.innerRight (u false) (u true)
  have hv : ContDiffOn ℝ 1 v (Ioc D.a M.innerLeft ∪ Ico M.innerRight D.b) :=
    radialOuterGlue_contDiffOn hm (hu false) (hu true)
  have hve (right : Bool) : EqOn v (u right)
      (radialTailHalf D right (if right then M.innerRight else M.innerLeft)) := by
    cases right
    · intro r hr
      exact (radialOuterGlue_left_germ hm hr.2 (u false) (u true)).eq_of_nhds
    · intro r hr
      exact (radialOuterGlue_right_germ hm hr.1 (u false) (u true)).eq_of_nhds
  have hsum : ((G F).1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
      fun r => (Ioo D.a M.innerLeft).indicator (u false) r +
        (Ioo M.innerRight D.b).indicator (u true) r := by
    filter_upwards [Lp.coeFn_add
      (radialTailZeroExtendOperator D false M.innerLeft (R false) F.1)
      (radialTailZeroExtendOperator D true M.innerRight (R true) F.1),
      radialTailZeroExtendOperator_ae (he false), radialTailZeroExtendOperator_ae (he true)]
      with r hr hL hR
    change (radialTailZeroExtendOperator D false M.innerLeft (R false) F.1 : ℝ → ℝ) r =
      (Ioo D.a M.innerLeft).indicator (u false) r at hL
    change (radialTailZeroExtendOperator D true M.innerRight (R true) F.1 : ℝ → ℝ) r =
      (Ioo M.innerRight D.b).indicator (u true) r at hR
    change (radialTailZeroExtendOperator D false M.innerLeft (R false) F.1 +
      radialTailZeroExtendOperator D true M.innerRight (R true) F.1) r = _
    rw [hr, Pi.add_apply, hL, hR]
  have heq := radialOuterPairOperator_weak hD hB ha hm hb (hweak false) (hweak true) F
  apply matching_outerGraph_of_representative hD ha hb (u := v) heq rfl
  · filter_upwards [hsum.restrict,
      ae_restrict_mem (measurableSet_Ioo.union measurableSet_Ioo)] with r hr hri
    rw [hr]
    rcases hri with hL | hR
    · have hn : r ∉ Ioo M.innerRight D.b := fun hh =>
        (not_lt.mpr (hL.2.le.trans hm.le)) hh.1
      rw [indicator_of_mem hL, indicator_of_notMem hn, add_zero]
      exact (hve false (Ioo_subset_Ioc_self hL)).symm
    · have hn : r ∉ Ioo D.a M.innerLeft := fun hh =>
        (not_lt.mpr (hm.le.trans hR.1.le)) hh.2
      rw [indicator_of_notMem hn, indicator_of_mem hR, zero_add]
      exact (hve true (Ioo_subset_Ico_self hR)).symm
  · filter_upwards [hsum.restrict, ae_restrict_mem measurableSet_Ioo] with r hr hri
    have hL : r ∉ Ioo D.a M.innerLeft := fun hh => lt_asymm hri.1 hh.2
    have hR : r ∉ Ioo M.innerRight D.b := fun hh => lt_asymm hri.2 hh.1
    rw [hr, indicator_of_notMem hL, indicator_of_notMem hR, add_zero]
  · exact hv
  · have hbnd (right : Bool) :
        let i : Fin 2 := if right then 1 else 0
        M.A i i * sqrt (M.boundaryScale i) * v (matchingCut D M i) +
          M.B i i * matchingOuterFlux D M v i = 0 := by
      let i : Fin 2 := if right then 1 else 0
      have hcut : matchingCut D M i = if right then M.innerRight else M.innerLeft := by
        cases right <;> norm_num [i, matchingCut]
      have hve' : EqOn v (u right) (radialTailHalf D right (matchingCut D M i)) := by
        rw [hcut]
        exact hve right
      have hvalue := hve' (radialTailHalf_cut (matchingCut_mem_core_of_geometry ha hm hb i))
      have hderiv := derivWithin_congr hve' hvalue
      have hf := matchingOuterFlux_eq_tailHalf ha hm hb hv right
      change matchingOuterFlux D M v i =
        outerTailSign right * D.w (matchingCut D M i) *
          derivWithin v (radialTailHalf D right (matchingCut D M i)) (matchingCut D M i) /
            sqrt (M.boundaryScale i) at hf
      change M.A i i * sqrt (M.boundaryScale i) * v (matchingCut D M i) +
        M.B i i * matchingOuterFlux D M v i = 0
      rw [hf, hvalue, hderiv]
      have hz := (outerRobin_sqrt_iff (hlam i) (M.A i i, M.B i i)
        (u right (if right then M.innerRight else M.innerLeft))
        (outerTailSign right * D.w (if right then M.innerRight else M.innerLeft) *
          derivWithin (u right)
            (radialTailHalf D right (if right then M.innerRight else M.innerLeft))
            (if right then M.innerRight else M.innerLeft))).mp (hRobin right)
      simpa only [hcut, Prod.fst, Prod.snd, mul_div_assoc] using hz
    intro i
    fin_cases i
    · exact hbnd false
    · exact hbnd true

end ContinuousFlexibility.Radial
