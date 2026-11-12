import ContinuousFlexibility.Radial.SelectedOuterGraphAssembly
import ContinuousFlexibility.Radial.ModeTailCauchySystem

/-!
# Uniqueness in the frozen exterior separated graph

The graph's C1 representative supplies the actual one-sided flux. Its
weak homogeneous equation gives the classical first-order system on each
open tail. The constructed natural-line uniqueness then forces both
components to vanish; the graph already makes the middle component zero.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory Real
open scoped Topology ContDiff
open ContinuousFlexibility.Statements ContinuousFlexibility.Analysis

theorem modeOuterSeparatedGraph_zero {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D) {M : RadialMatchingData D}
    (ha : D.a < M.innerLeft) (hm : M.innerLeft < M.innerRight) (hb : M.innerRight < D.b)
    (hlam : ∀ i, 0 < M.boundaryScale i)
    (hunique : ∀ right : Bool,
      let i : Fin 2 := if right then 1 else 0
      RadialTailCauchyUnique D right (if right then M.innerRight else M.innerLeft)
        ((M.frequency : ℝ) ^ 2) (M.boundaryScale i) (M.A i i, M.B i i))
    {U : RadialModePair D} (hU : ModeOuterSeparatedGraph D M U 0) : U = 0 := by
  obtain ⟨hEq, hscalar, u, hrep, hu, hinner, hboundary⟩ := hU
  have hout (right : Bool) : ∀ r ∈
      radialTailHalf D right (if right then M.innerRight else M.innerLeft), u r = 0 := by
    let i : Fin 2 := if right then 1 else 0
    have hcut : matchingCut D M i = if right then M.innerRight else M.innerLeft := by
      cases right <;> norm_num [i, matchingCut]
    have hcore : (if right then M.innerRight else M.innerLeft) ∈ radialCore D := by
      rw [← hcut]
      exact matchingCut_mem_core_of_geometry ha hm hb i
    have hsub : radialTailInterval D right (if right then M.innerRight else M.innerLeft) ⊆
        matchingOuterRegion D M := by
      cases right
      · exact subset_union_left
      · exact subset_union_right
    have hreg : ContDiffOn ℝ 1 u
        (radialTailHalf D right (if right then M.innerRight else M.innerLeft)) := by
      cases right
      · exact hu.mono subset_union_left
      · exact hu.mono subset_union_right
    apply (hunique right).eq_zero_of_weak hD hB hcore
      (modeLocalEquation_mono hEq hsub) hscalar hrep hreg
    apply (outerRobin_sqrt_iff (hlam i) (M.A i i, M.B i i) _ _).mpr
    have hz := hboundary i
    have hf := matchingOuterFlux_eq_tailHalf ha hm hb hu right
    change matchingOuterFlux D M u i =
      outerTailSign right * D.w (matchingCut D M i) *
        derivWithin u (radialTailHalf D right (matchingCut D M i)) (matchingCut D M i) /
          sqrt (M.boundaryScale i) at hf
    rw [hf] at hz
    simpa only [hcut, Prod.fst, Prod.snd, mul_div_assoc] using hz
  apply Prod.ext
  · apply Lp.ext
    filter_upwards [hrep, (Lp.coeFn_zero ℝ 2 (radialHilbertMeasure D) :
        ⇑(0 : RadialModeL2 D) =ᵐ[radialHilbertMeasure D] 0),
      matching_ae_inner_or_outer hD M] with r hr hz hri
    rw [Prod.fst_zero, hr, hz, Pi.zero_apply]
    rcases hri with hin | hL | hR
    · exact hinner r hin
    · exact hout false r (Ioo_subset_Ioc_self hL)
    · exact hout true r (Ioo_subset_Ico_self hR)
  · exact hscalar

theorem modeOuterSeparatedGraph_sub {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {M : RadialMatchingData D}
    (ha : D.a < M.innerLeft) (hm : M.innerLeft < M.innerRight) (hb : M.innerRight < D.b)
    {U F V H : RadialModePair D}
    (hU : ModeOuterSeparatedGraph D M U F) (hV : ModeOuterSeparatedGraph D M V H) :
    ModeOuterSeparatedGraph D M (U - V) (F - H) := by
  obtain ⟨hEqU, hscalarU, u, hrepU, hu, hinnerU, hboundaryU⟩ := hU
  obtain ⟨hEqV, hscalarV, v, hrepV, hv, hinnerV, hboundaryV⟩ := hV
  refine ⟨modeLocalEquation_sub hD hEqU hEqV, ?_, fun r => u r - v r, ?_,
    hu.sub hv, ?_, ?_⟩
  · simp only [Prod.snd_sub, hscalarU, hscalarV, sub_self]
  · filter_upwards [Lp.coeFn_sub U.1 V.1, hrepU, hrepV] with r hr hur hvr
    simpa only [Prod.fst_sub, Pi.sub_apply, hur, hvr] using hr
  · intro r hr
    dsimp only
    rw [hinnerU r hr, hinnerV r hr, sub_self]
  · intro i
    rw [matchingOuterFlux_sub ha hm hb hu hv]
    linarith only [hboundaryU i, hboundaryV i]

theorem radialOuterPairOperator_unique {D : ReferenceData}
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
    (hunique : ∀ right,
      let i : Fin 2 := if right then 1 else 0
      RadialTailCauchyUnique D right (if right then M.innerRight else M.innerLeft)
        ((M.frequency : ℝ) ^ 2) (M.boundaryScale i) (M.A i i, M.B i i))
    {U F : RadialModePair D} (hU : ModeOuterSeparatedGraph D M U F) :
    radialOuterPairOperator D M.innerLeft M.innerRight (R false) (R true) F = U := by
  have hG := radialOuterPairOperator_graph hD hB M ha hm hb hlam R hweak hregular F
  have hz := modeOuterSeparatedGraph_sub hD ha hm hb hU hG
  rw [sub_self] at hz
  exact (sub_eq_zero.mp (modeOuterSeparatedGraph_zero hD hB ha hm hb hlam hunique hz)).symm

end ContinuousFlexibility.Radial
