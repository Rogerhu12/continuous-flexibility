module

public import ContinuousFlexibility.Radial.MatchingGraphRestrictions
public import Mathlib.Analysis.Calculus.ContDiff.Defs

/-!
# Representatives for the frozen local matching graphs

A representative specified on one matching region and vanishing almost
everywhere on the other gives an actual globally defined representative
in the frozen graph. Endpoint values and one-sided fluxes are preserved.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

theorem matching_indicator_representative {μ : Measure ℝ}
    {f u : ℝ → ℝ} {S T C : Set ℝ}
    (hu : f =ᵐ[μ.restrict S] u)
    (hz : f =ᵐ[μ.restrict T] fun _ => 0)
    (hcover : ∀ᵐ r ∂μ, r ∈ S ∨ r ∈ T)
    (hS : S ⊆ C) (hT : T ⊆ Cᶜ) :
    f =ᵐ[μ] C.indicator u := by
  classical
  filter_upwards [ae_imp_of_ae_restrict hu, ae_imp_of_ae_restrict hz, hcover]
    with r hU hZ hr
  rcases hr with hr | hr
  · rw [Set.indicator_of_mem (hS hr), hU hr]
  · rw [Set.indicator_of_notMem (hT hr), hZ hr]

theorem matching_sourceInner_representative {D : ReferenceData}
    {M : RadialMatchingData D} (hM : MatchingLocalRealizations D M)
    {U : RadialModePair D} {u : ℝ → ℝ}
    (hu : (U.1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] u) :
    (((M.sourceInner U).1 : ℝ → ℝ) =ᵐ[(radialHilbertMeasure D).restrict
      (Ioo M.innerLeft M.innerRight)] u) ∧
    (((M.sourceInner U).1 : ℝ → ℝ) =ᵐ[(radialHilbertMeasure D).restrict
      (matchingOuterRegion D M)] fun _ => 0) := by
  have hs := (hM.2.2.2.1 U).2.2.1
  constructor
  · filter_upwards [hs.restrict, hu.restrict, ae_restrict_mem measurableSet_Ioo]
      with r hsrc hrep hr
    rw [hsrc, if_pos hr, hrep]
  · have hmeas : MeasurableSet (matchingOuterRegion D M) :=
      measurableSet_Ioo.union measurableSet_Ioo
    filter_upwards [hs.restrict, ae_restrict_mem hmeas] with r hsrc hr
    rw [hsrc, if_neg (matchingOuterRegion_not_mem_inner hr)]

theorem matching_sourceOuter_representative {D : ReferenceData}
    {M : RadialMatchingData D} (hM : MatchingLocalRealizations D M)
    {U : RadialModePair D} {u : ℝ → ℝ}
    (hu : (U.1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] u) :
    (((M.sourceOuter U).1 : ℝ → ℝ) =ᵐ[(radialHilbertMeasure D).restrict
      (matchingOuterRegion D M)] u) ∧
    (((M.sourceOuter U).1 : ℝ → ℝ) =ᵐ[(radialHilbertMeasure D).restrict
      (Ioo M.innerLeft M.innerRight)] fun _ => 0) := by
  have hs := (hM.2.2.2.1 U).2.2.2
  constructor
  · have hmeas : MeasurableSet (matchingOuterRegion D M) :=
      measurableSet_Ioo.union measurableSet_Ioo
    filter_upwards [hs.restrict, hu.restrict, ae_restrict_mem hmeas]
      with r hsrc hrep hr
    rw [hsrc, if_neg (matchingOuterRegion_not_mem_inner hr), hrep]
  · filter_upwards [hs.restrict, ae_restrict_mem measurableSet_Ioo] with r hsrc hr
    rw [hsrc, if_pos hr]

theorem matching_innerGraph_of_representative {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {M : RadialMatchingData D}
    (hm : M.innerLeft < M.innerRight) {U F : RadialModePair D} {u : ℝ → ℝ}
    (hEq : ModeLocalEquation D M.frequency (Ioo M.innerLeft M.innerRight) U F)
    (hrow : if M.frequency = 2 then
      (∫ r in D.a..D.b, referenceColumn D r * U.1 r) = F.2
      else U.2 = 0 ∧ F.2 = 0)
    (hu : (U.1 : ℝ → ℝ) =ᵐ[(radialHilbertMeasure D).restrict
      (Ioo M.innerLeft M.innerRight)] u)
    (hz : (U.1 : ℝ → ℝ) =ᵐ[(radialHilbertMeasure D).restrict
      (matchingOuterRegion D M)] fun _ => 0)
    (hreg : ContDiffOn ℝ 1 u (Icc M.innerLeft M.innerRight))
    (hleft : u M.innerLeft = 0) (hright : u M.innerRight = 0) :
    ModeInnerDirichletGraph D M U F := by
  classical
  let v : ℝ → ℝ := (Icc M.innerLeft M.innerRight).indicator u
  have hout : matchingOuterRegion D M ⊆ (Icc M.innerLeft M.innerRight)ᶜ := by
    intro r hr hc
    rcases hr with hL | hR
    · exact (not_lt_of_ge hc.1) hL.2
    · exact (not_lt_of_ge hc.2) hR.1
  refine ⟨hEq, hrow, v,
    matching_indicator_representative hu hz (matching_ae_inner_or_outer hD M)
      Ioo_subset_Icc_self hout, ?_, ?_, ?_, ?_⟩
  · exact hreg.congr (fun r hr => Set.indicator_of_mem hr u)
  · intro r hr
    exact Set.indicator_of_notMem (hout hr) u
  · change (Icc M.innerLeft M.innerRight).indicator u M.innerLeft = 0
    have hl : M.innerLeft ∈ Icc M.innerLeft M.innerRight := ⟨le_rfl, hm.le⟩
    rw [Set.indicator_of_mem hl, hleft]
  · change (Icc M.innerLeft M.innerRight).indicator u M.innerRight = 0
    have hr : M.innerRight ∈ Icc M.innerLeft M.innerRight := ⟨hm.le, le_rfl⟩
    rw [Set.indicator_of_mem hr, hright]

theorem matchingOuterRegion_closure {D : ReferenceData}
    {M : RadialMatchingData D} (ha : D.a < M.innerLeft) (hb : M.innerRight < D.b) :
    closure (matchingOuterRegion D M) =
      Icc D.a M.innerLeft ∪ Icc M.innerRight D.b := by
  rw [matchingOuterRegion, closure_union, closure_Ioo ha.ne, closure_Ioo hb.ne]

theorem matchingCut_mem_outerClosure {D : ReferenceData}
    {M : RadialMatchingData D} (ha : D.a < M.innerLeft)
    (hb : M.innerRight < D.b) (i : Fin 2) :
    matchingCut D M i ∈ closure (matchingOuterRegion D M) := by
  rw [matchingOuterRegion_closure ha hb]
  unfold matchingCut
  split_ifs
  · exact Or.inl ⟨ha.le, le_rfl⟩
  · exact Or.inr ⟨le_rfl, hb.le⟩

theorem matching_outerGraph_of_representative {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {M : RadialMatchingData D}
    (ha : D.a < M.innerLeft) (hb : M.innerRight < D.b)
    {U F : RadialModePair D} {u : ℝ → ℝ}
    (hEq : ModeLocalEquation D M.frequency (matchingOuterRegion D M) U F)
    (hscalar : U.2 = 0)
    (hu : (U.1 : ℝ → ℝ) =ᵐ[(radialHilbertMeasure D).restrict
      (matchingOuterRegion D M)] u)
    (hz : (U.1 : ℝ → ℝ) =ᵐ[(radialHilbertMeasure D).restrict
      (Ioo M.innerLeft M.innerRight)] fun _ => 0)
    (hreg : ContDiffOn ℝ 1 u (Ioc D.a M.innerLeft ∪ Ico M.innerRight D.b))
    (hboundary : ∀ i, M.A i i * Real.sqrt (M.boundaryScale i) * u (matchingCut D M i) +
      M.B i i * matchingOuterFlux D M u i = 0) :
    ModeOuterSeparatedGraph D M U F := by
  classical
  let C := closure (matchingOuterRegion D M)
  let v : ℝ → ℝ := C.indicator u
  have hinner : Ioo M.innerLeft M.innerRight ⊆ Cᶜ := by
    intro r hr hc
    change r ∈ closure (matchingOuterRegion D M) at hc
    rw [matchingOuterRegion_closure ha hb] at hc
    rcases hc with hL | hR
    · exact (not_le.mpr hr.1) hL.2
    · exact (not_le.mpr hr.2) hR.1
  have hclosed : Ioc D.a M.innerLeft ∪ Ico M.innerRight D.b ⊆ C := by
    intro r hr
    change r ∈ closure (matchingOuterRegion D M)
    rw [matchingOuterRegion_closure ha hb]
    rcases hr with hL | hR
    · exact Or.inl ⟨hL.1.le, hL.2⟩
    · exact Or.inr ⟨hR.1, hR.2.le⟩
  have hcover : ∀ᵐ r ∂radialHilbertMeasure D,
      r ∈ matchingOuterRegion D M ∨ r ∈ Ioo M.innerLeft M.innerRight :=
    (matching_ae_inner_or_outer hD M).mono (fun _ h => h.symm)
  refine ⟨hEq, hscalar, v,
    matching_indicator_representative hu hz hcover subset_closure hinner, ?_, ?_, ?_⟩
  · exact hreg.congr (fun r hr => Set.indicator_of_mem (hclosed hr) u)
  · intro r hr
    exact Set.indicator_of_notMem (hinner hr) u
  · intro i
    have hcut : matchingCut D M i ∈ C := matchingCut_mem_outerClosure ha hb i
    have hvalue : v (matchingCut D M i) = u (matchingCut D M i) :=
      Set.indicator_of_mem hcut u
    have hflux : matchingOuterFlux D M v i = matchingOuterFlux D M u i := by
      unfold matchingOuterFlux
      rw [derivWithin_congr (fun r hr => Set.indicator_of_mem hr u)
        (Set.indicator_of_mem hcut u)]
    rw [hvalue, hflux]
    exact hboundary i

end ContinuousFlexibility.Radial
