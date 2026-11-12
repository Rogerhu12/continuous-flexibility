import ContinuousFlexibility.Radial.R11aRetainedFamily
import ContinuousFlexibility.Radial.MatchedOuterRetainedParameters
import ContinuousFlexibility.Radial.MatchedOuterTailEnvelope
import ContinuousFlexibility.Radial.MatchedOuterWholeFactory
import ContinuousFlexibility.Radial.MatchedOuterFixedCutoff
import ContinuousFlexibility.Radial.MatchedOuterFixedOperatorBounds

/-!
# Actual outer envelopes at every fixed retained frequency

A genuine auxiliary deep cutoff is moved past the matching cut and the
initial retained entry. The core may contain the nonlinear coordinate
transition; its localizer labels are controlled by actual compactness.
The same original full-source kernel is then dilated to the retained
reference, preserving its natural Robin line.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory Real
open scoped Topology ContDiff
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint

theorem SeedRetainedPair.exists_fixed_selectedOuter_tailEnvelope
    {S : SelectedTailData} {K₀ : SeedCentralCutoff} {q length Cstar : ℝ} {requested : ℕ}
    (P : SeedRetainedPair S K₀ q length) (metadata : R10aSelectedMetadata Cstar requested S)
    (Γ : ConnectedReferenceGeometry)
    (hE : IsAccumulatingProfile Γ.reference) (hPE : RadialPartition Γ.reference)
    (hw : Γ.reference.w = P.pair.profile) (hcoordinates : R11aRetainedCoordinates P Γ)
    {n j : ℕ} (hj : 2 ≤ j) (heven : Even j)
    (hband : radialFrequencyBand S.chain S.Cstar n j) (right : Bool) :
    ∃ B A : ℝ, 0 < B ∧ 0 < A ∧
      MatchedOuterTailEnvelope (S.family S.sigma) Γ.reference hPE right
        (P.sideRadius right * S.joinInner right n) j n B A := by
  classical
  let D := S.family S.sigma
  let E := Γ.reference
  let cut := S.joinInner right n
  let first := S.entry right S.chain.index
  let κ := P.sideRadius right
  let β := P.sideHeight right
  let lam := standInBoundaryScale ((j : ℝ) ^ 2) (D.w cut) cut
  have hS := metadata.selected
  have h := (hS.2.2.2.1 S.sigma hS.2.2.1).1
  have hD : IsAccumulatingProfile D := ⟨S.constants, h.accumulating⟩
  obtain ⟨hcut, hcutE, hlam, hend, hprofile, hprofileCut, hscale⟩ :=
    P.selectedOuter_actual_scaling metadata hE hw hj heven hband right
  have hfirst : first ∈ radialCore D := (metadata.initial right).1
  let anchor := if outerOutwardRadius right cut ≤ outerOutwardRadius right first
    then first else cut
  have ha : anchor ∈ radialCore D := by
    dsimp only [anchor]
    split_ifs <;> assumption
  have hca : outerOutwardRadius right cut ≤ outerOutwardRadius right anchor := by
    dsimp only [anchor]
    split_ifs with hle
    · exact hle
    · exact le_rfl
  have hfa : outerOutwardRadius right first ≤ outerOutwardRadius right anchor := by
    dsimp only [anchor]
    split_ifs with hle
    · exact le_rfl
    · exact (lt_of_not_ge hle).le
  let η : ℝ := 1 / 32
  let K : ℝ := max 32 (10 * tailSmoothStepConstant + 2)
  have hη0 : 0 < η := by norm_num [η]
  have hη : η ≤ 1 / 16 := by norm_num [η]
  have hK : 32 ≤ K := le_max_left _ _
  have hKinv : 10 * tailSmoothStepConstant + 2 ≤ K := le_max_right _ _
  obtain ⟨Ad, hAd, N, _, hN, _, hafter, hlabels, hT, hphysical, hclose, hden, ⟨F⟩⟩ :=
    exists_matchedMorse_fixed_deep_cutoff hS.2.2.2.1 metadata.family_endpoints
      hS.1 hη0 hη hK 0 S.sigma hS.2.2.1 right j hj ha
  have hcutDeep : outerOutwardRadius right cut <
      outerOutwardRadius right (morseOuterDeepEntrance S.chain right N) := hca.trans_lt hafter
  have hfirstDeep : outerOutwardRadius right first <
      outerOutwardRadius right (morseOuterDeepEntrance S.chain right N) := hfa.trans_lt hafter
  have hdeep : morseOuterDeepEntrance S.chain right N ∈ radialCore D :=
    morseOuterDeepEntrance_mem_core h right N (by omega)
  obtain ⟨H, R, hV, hR, _⟩ := F.exists_matchedWholeGreenOperator hD hcut hdeep
    hcutDeep.le hlam.ne' hT hphysical hη hK hKinv
  obtain ⟨e, floor, _, hDlabel, hElabel, _, hlocalizer, hleft, hright, _, _, _⟩ :=
    hcoordinates
  have hindex : ∀ m, D.cellIndex m ≤ E.cellIndex m := by
    intro m
    change (S.family S.sigma).cellIndex m ≤ Γ.reference.cellIndex m
    rw [hElabel, ← hDlabel]
    exact le_max_left _ _
  have hlocal : ∀ m x, x ∈ Ico
      (outerOutwardRadius right (morseOuterDeepEntrance S.chain right N))
      (outerOutwardRadius right (tailPhysicalEndpoint D right)) →
      E.localizer m (outerOutwardRadius right (κ * x)) =
        D.localizer m (outerOutwardRadius right x) := by
    intro m x hx
    have he : e.symm (outerOutwardRadius right x) =
        κ * outerOutwardRadius right x := by
      cases right with
      | false =>
          apply hleft
          change -first < -morseOuterDeepEntrance S.chain false N at hfirstDeep
          change -morseOuterDeepEntrance S.chain false N ≤ x ∧
            x < -tailPhysicalEndpoint D false at hx
          change -x ≤ S.entry false S.chain.index
          dsimp only [first] at hfirstDeep
          linarith [hx.1]
      | true =>
          apply hright
          change first < morseOuterDeepEntrance S.chain true N at hfirstDeep
          change morseOuterDeepEntrance S.chain true N ≤ x ∧
            x < tailPhysicalEndpoint D true at hx
          exact hfirstDeep.le.trans hx.1
    have hout : outerOutwardRadius right (κ * x) =
        κ * outerOutwardRadius right x := by cases right <;> simp [outerOutwardRadius]
    change Γ.reference.localizer m (outerOutwardRadius right (κ * x)) =
      (S.family S.sigma).localizer m (outerOutwardRadius right x)
    rw [hout, hlocalizer, ← he]
    change (S.family S.sigma).localizer m (e (e.symm (outerOutwardRadius right x))) =
      (S.family S.sigma).localizer m (outerOutwardRadius right x)
    rw [e.apply_symm_apply]
  have hκ : 0 < κ := P.sideRadius_pos right
  have hβ : 0 < β := P.sideHeight_pos right
  let hm := outerWholeMeasure_radiusScale hκ hβ hcut hcutE hend hprofile
  obtain ⟨B, A, hB, hA, hbound⟩ := exists_matchedMorse_fixed_whole_radius_bounds h hE
    hN hlabels right j η K F hT hη hK hj hphysical hclose hAd.le hden
    hlam hcutDeep.le H hcut hκ hβ hcutE hend hm hindex hlocal n
  have hb := hbound hPE R hR
  refine ⟨B, A, hB, hA, ?_⟩
  exact matchedOuterTailEnvelope_of_radius_data F hD hE hPE hj hcut hdeep hcutDeep
    hlam hT hphysical hη hK H hV R hR hκ hβ hcutE hend hprofile hprofileCut
    hscale n hb.1 hb.2

end ContinuousFlexibility.Radial
