import ContinuousFlexibility.Radial.SelectedScaledRobinInverse
import ContinuousFlexibility.Radial.SelectedPhysicalTailFactory
import ContinuousFlexibility.Radial.SelectedFirstNaturalTransport
import ContinuousFlexibility.Radial.SelectedLaterRetained

/-!
# Actual regional inverses on the retained pair's two selected cuts

For a fixed band and frequency, choose an auxiliary deep split after both
joins. The old selected profile supplies the complete deep hypotheses and
the retained pair supplies the actual radius/height transport. The natural
functions are the fixed functions passed by the first- or later-band data.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory Real
open scoped Topology ContDiff
open ContinuousFlexibility.Statements ContinuousFlexibility.Analysis

theorem selected_join_outside_first_cut {S : SelectedTailData}
    (hS : IsSelectedTail S) (G : MorseChainGeometryWitness S.chain)
    (hentry : S.entry = r07CellEntry S.chain)
    (hfirst : radialFrequencyBand S.chain S.Cstar S.chain.index 2)
    (hcut : ∀ right n, S.chain.index < n →
      S.cut right n = r07PreviousCellCut S.chain right (n - 1))
    {n j : ℕ} (hj : 2 ≤ j) (heven : Even j)
    (hband : radialFrequencyBand S.chain S.Cstar n j) (right : Bool) :
    if right then S.cut right S.chain.index ≤ S.joinInner right n
      else S.joinInner right n ≤ S.cut right S.chain.index := by
  by_cases hn : n = S.chain.index
  · subst n
    have ho := (hS.2.2.2.2.2 right S.chain.index j hj heven hband).2.2.2.2.1
    cases right
    · exact ho.2.le
    · exact ho.1.le
  · have hlt : S.chain.index < n := by
      have hnle := hband.1
      omega
    have hr := (selected_later_cut_join_entry_retained hS G hentry right hlt hj heven
      hband (hcut right n hlt)).2.1
    have ho := (hS.2.2.2.2.2 right S.chain.index 2 le_rfl (by decide) hfirst).2.2.2.2.1
    cases right
    · exact (hr.2.trans (ho.1.trans ho.2)).le
    · exact ((ho.1.trans ho.2).trans hr.1).le

theorem SeedRetainedPair.exists_selectedOuterRegionalInverse {S : SelectedTailData}
    {K₀ : SeedCentralCutoff} {q length : ℝ} (P : SeedRetainedPair S K₀ q length)
    {E : ReferenceData} (hE : IsAccumulatingProfile E) (hw : E.w = P.pair.profile)
    (hS : IsSelectedTail S) (G : MorseChainGeometryWitness S.chain)
    (hends : ∀ sigma tau, (S.family sigma).a = (S.family tau).a ∧
      (S.family sigma).b = (S.family tau).b)
    (hentry : S.entry = r07CellEntry S.chain)
    (hfirst : radialFrequencyBand S.chain S.Cstar S.chain.index 2)
    (hcut : ∀ right n, S.chain.index < n →
      S.cut right n = r07PreviousCellCut S.chain right (n - 1))
    {n j : ℕ} (hj : 2 ≤ j) (heven : Even j)
    (hband : radialFrequencyBand S.chain S.Cstar n j)
    (V : Bool → ℝ → ℝ) (hV : ∀ right, ContDiff ℝ ∞ (V right))
    (hN : ∀ right, RadialNaturalTail E right j
      (P.sideRadius right * S.joinInner right n) (V right)) :
    ∃ R : ∀ right : Bool,
      Lp ℝ 2 ((radialHilbertMeasure E).restrict
        (radialTailInterval E right (P.sideRadius right * S.joinInner right n))) →L[ℝ]
      Lp ℝ 2 ((radialHilbertMeasure E).restrict
        (radialTailInterval E right (P.sideRadius right * S.joinInner right n))),
      ∀ right,
        let c := P.sideRadius right * S.joinInner right n
        let lam := standInBoundaryScale ((j : ℝ) ^ 2) (E.w c) c
        let v := outerUnitState (selectedBoundaryState E j (r07OutwardSign right) c (V right))
        c ∈ radialCore E ∧ 0 < lam ∧
          RadialTailWeakPairing E hE right c j (R right) ∧
          RadialTailRegularResponse E right c lam v (R right) ∧
          RadialTailCauchyUnique E right c ((j : ℝ) ^ 2) lam v := by
  classical
  let D := S.family S.sigma
  have hreal : MorseChainRealization S.chain S.sigma D S.constants :=
    (hS.2.2.2.1 S.sigma hS.2.2.1).1
  have hBounds : AccumulatingProfileBounds D S.constants := hreal.2.2.2.2.2.2.2.2.2
  have hD : IsAccumulatingProfile D := ⟨S.constants, hBounds⟩
  let η : ℝ := 1 / 32
  let K : ℝ := max 32 (10 * tailSmoothStepConstant + 2)
  have hη : η ≤ 1 / 16 := by norm_num [η]
  have hK : 32 ≤ K := le_max_left _ _
  have hKinv : 10 * tailSmoothStepConstant + 2 ≤ K := le_max_right _ _
  obtain ⟨start, _, _, _, _, _, hsplit⟩ := exists_selected_outer_deep_split hS G hends
    hj heven hband (η := η) (K := K) (by norm_num [η]) (by norm_num [η])
      (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 32) hK) 0
  have hside (right : Bool) :
      ∃ R : Lp ℝ 2 ((radialHilbertMeasure E).restrict
        (radialTailInterval E right (P.sideRadius right * S.joinInner right n))) →L[ℝ]
        Lp ℝ 2 ((radialHilbertMeasure E).restrict
          (radialTailInterval E right (P.sideRadius right * S.joinInner right n))),
        let c := P.sideRadius right * S.joinInner right n
        let lam := standInBoundaryScale ((j : ℝ) ^ 2) (E.w c) c
        let v := outerUnitState (selectedBoundaryState E j (r07OutwardSign right) c (V right))
        c ∈ radialCore E ∧ 0 < lam ∧
          RadialTailWeakPairing E hE right c j R ∧
          RadialTailRegularResponse E right c lam v R ∧
          RadialTailCauchyUnique E right c ((j : ℝ) ^ 2) lam v := by
    let p := S.joinInner right n
    let κ := P.sideRadius right
    let β := P.sideHeight right
    let lam := standInBoundaryScale ((j : ℝ) ^ 2) (D.w p) p
    have hs := hsplit right
    have hp : p ∈ radialCore D := hs.join_core
    have hκ : 0 < κ := P.sideRadius_pos right
    have hβ : 0 < β := P.sideHeight_pos right
    have hout := selected_join_outside_first_cut hS G hentry hfirst hcut hj heven hband right
    have hvalue : E.w (κ * p) = (β * κ) * D.w p :=
      P.reference_side_old_value hw hS right hp hout
    have hpE : κ * p ∈ radialCore E := by
      apply radialCore_mem_of_profile_pos (matchingProfileGeometry hE)
      rw [hvalue]
      exact mul_pos (mul_pos hβ hκ) ((matchingProfileGeometry hD).2.2.2.2.1 _ hp)
    have hprofile (r : ℝ) (hr : r ∈ radialTailInterval D right p) :
        E.w (κ * r) = (β * κ) * D.w r := by
      apply P.reference_side_old_value hw hS right (selectedTailInterval_subset_core hp right hr)
      cases right
      · exact hr.2.le.trans hout
      · exact hout.trans hr.1.le
    have hjn : (j : ℝ) ≠ 0 := by exact_mod_cast (by omega : j ≠ 0)
    have hlam : 0 < lam := standInBoundaryScale_pos (sq_pos_of_ne_zero hjn)
      ((matchingProfileGeometry hD).2.2.2.2.1 _ hp) ((matchingProfileGeometry hD).1.trans hp.1)
    have hscale : standInBoundaryScale ((j : ℝ) ^ 2) (E.w (κ * p)) (κ * p) = β * lam := by
      rw [standInBoundaryScale, hvalue]
      dsimp only [lam, standInBoundaryScale]
      field_simp [hκ.ne', ((matchingProfileGeometry hD).1.trans hp.1).ne'] <;> ring
    have hsign : r07OutwardSign right = outerTailSign right := by cases right <;> rfl
    have hne := selectedBoundaryState_ne_zero_of_natural (matchingProfileGeometry hE) hjn hpE
      (show r07OutwardSign right ≠ 0 by cases right <;> norm_num [r07OutwardSign])
      (hV right) (hN right)
    obtain ⟨F⟩ := SelectedOuterDeepSplitData.exists_physicalBasis hS hs hη hK
    have hac : outerTailSign right * p <
        outerTailSign right * selectedOuterDeepEntrance S right start := by
      simpa only [r07OutwardSign, outerTailSign] using hs.outward_order.1
    obtain ⟨R, hweak, hregular, hunique⟩ := F.exists_scaledNaturalInverse hD hE hp
      hs.entrance_core hac hlam.ne' hs.physicalFactory.1 hs.physicalFactory.2 hη hK hKinv
      hκ hβ hpE (P.reference_side_endpoint (matchingProfileGeometry hE) hw right)
      hprofile hvalue (hV right) (hN right)
      (by simpa only [selectedBoundaryState, outerFluxState, hsign, hscale] using hne)
    refine ⟨R, hpE, ?_, hweak, ?_, ?_⟩
    · rw [hscale]
      exact mul_pos hβ hlam
    · simpa only [selectedBoundaryState, outerFluxState, hsign, hscale] using hregular
    · simpa only [selectedBoundaryState, outerFluxState, hsign, hscale] using hunique
  choose R hR using hside
  exact ⟨R, hR⟩

end ContinuousFlexibility.Radial
