import ContinuousFlexibility.Radial.MatchedOuterFixedRetainedEnvelope
import ContinuousFlexibility.Radial.MatchedOuterSelectedBounds
import ContinuousFlexibility.Radial.MatchedOuterRadiusCells

/-!
# One outer envelope after the uniform selected threshold

The constants precede all frequencies. Every later matching cut lies in
the exact retained radius chart, so the already proved physical whole
bounds transport isometrically, for every original localizer.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory Real
open scoped Topology ContDiff
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint

theorem SeedRetainedPair.exists_uniform_laterOuter_tailEnvelope
    {S : SelectedTailData} {K₀ : SeedCentralCutoff} {q length Cstar : ℝ} {requested : ℕ}
    (P : SeedRetainedPair S K₀ q length) (metadata : R10aSelectedMetadata Cstar requested S)
    (Γ : ConnectedReferenceGeometry)
    (hE : IsAccumulatingProfile Γ.reference) (hPE : RadialPartition Γ.reference)
    (hw : Γ.reference.w = P.pair.profile) (hcoordinates : R11aRetainedCoordinates P Γ) :
    ∃ C A : ℝ, 0 < C ∧ 0 < A ∧ ∃ N₀ : ℕ, S.chain.index + 3 ≤ N₀ ∧
      ∀ n : ℕ, N₀ ≤ n → ∀ j : ℕ, 2 ≤ j → Even j →
        radialFrequencyBand S.chain S.Cstar n j → ∀ right : Bool,
          MatchedOuterTailEnvelope (S.family S.sigma) Γ.reference hPE right
            (P.sideRadius right * S.joinInner right n) j n C A := by
  classical
  let D := S.family S.sigma
  have hS := metadata.selected
  have h := (hS.2.2.2.1 S.sigma hS.2.2.1).1
  have hD : IsAccumulatingProfile D := ⟨S.constants, h.accumulating⟩
  obtain ⟨entry, he⟩ := morseInitialMiddle_nonempty h
  let η : ℝ := 1 / 32
  let K : ℝ := max 32 (10 * tailSmoothStepConstant + 2)
  have hη0 : 0 < η := by norm_num [η]
  have hη : η ≤ 1 / 16 := by norm_num [η]
  have hK : 32 ≤ K := le_max_left _ _
  have hKinv : 10 * tailSmoothStepConstant + 2 ≤ K := le_max_right _ _
  obtain ⟨C, A, hC, hA, Nb, _, hNb, hbound⟩ :=
    exists_matchedMorse_uniform_selected_whole_bounds hS.2.2.2.1 metadata.family_endpoints
      hS.1 hη0 hη hK 0
  obtain ⟨Ad, hAd, Nd, _, _, _, hdata⟩ :=
    outer_exists_uniform_actual_deepTailProduct S.chain S.constants S.family
      hS.2.2.2.1 metadata.family_endpoints hS.1 hη0 (by norm_num [η])
      (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 32) hK) 0
  refine ⟨C, A, hC, hA, max Nb Nd, hNb.trans (le_max_left _ _), ?_⟩
  intro n hn j hj heven hband right
  have hnb : Nb ≤ n := (le_max_left _ _).trans hn
  have hnd : Nd ≤ n := (le_max_right _ _).trans hn
  have hstrict : S.chain.index < n := by omega
  have hjupper : (j : ℝ) < radialFrequencyThreshold S.chain S.Cstar n := hband.2.2
  let cut := S.joinInner right n
  let κ := P.sideRadius right
  let β := P.sideHeight right
  let lam := standInBoundaryScale ((j : ℝ) ^ 2) (D.w cut) cut
  obtain ⟨hcut, hcutE, hlam, hend, hprofile, hprofileCut, hscale⟩ :=
    P.selectedOuter_actual_scaling metadata hE hw hj heven hband right
  have hdeep : morseOuterDeepEntrance S.chain right n ∈ radialCore D :=
    morseOuterDeepEntrance_mem_core h right n (by omega)
  have hentryEq : morseTransitionPhysicalEntry S.chain entry right n = cut :=
    (matchedMorse_transitionEntry_eq_previousJoin h entry right hstrict).trans
      (metadata.later_join right n hstrict).symm
  have hleftEq : morseTransitionOutwardLeft S.chain entry right n =
      outerOutwardRadius right cut := by
    rw [morseTransitionOutwardLeft_eq, hentryEq]
  have hrightEq : morseTransitionOutwardRight S.chain entry right n =
      outerOutwardRadius right (morseOuterDeepEntrance S.chain right n) :=
    morseTransitionOutwardRight_eq _ _ _ _
  have hcutDeep : outerOutwardRadius right cut <
      outerOutwardRadius right (morseOuterDeepEntrance S.chain right n) := by
    simpa only [hleftEq, hrightEq] using
      (morseTransitionOutward_interval h he right n (by omega)).1
  have hd := hdata n hnd S.sigma hS.2.2.1 j hj hjupper right
  obtain ⟨F⟩ := exists_morsePhysicalTailBasis h.geometry right j (n + 1)
    (h.geometry.1.trans hdeep.1) hd.2.1 hη hK
  obtain ⟨H, R, hV, hR, _⟩ := F.exists_matchedWholeGreenOperator hD hcut hdeep
    hcutDeep.le hlam.ne' hd.2.1 hd.2.2.1 hη hK hKinv
  have hwhole := hbound n hnb S.sigma hS.2.2.1 j hj hjupper entry he right
  dsimp only at hwhole
  rw [← metadata.later_join right n hstrict, hentryEq, hleftEq, hrightEq] at hwhole
  obtain ⟨e, _, _, _, _, _, hlocalizer, hleft, hright, _, _, _⟩ := hcoordinates
  have heRadius : ∀ r ∈ radialTailInterval D right cut, e.symm r = κ * r := by
    intro r hr
    have hjoin := (selected_later_cut_join_entry_retained hS metadata.geometry metadata.entry
      right hstrict hj heven hband (metadata.later_cut right n hstrict)).2.1
    cases right
    · apply hleft
      exact hr.2.le.trans hjoin.2.le
    · apply hright
      exact hjoin.1.le.trans hr.1.le
  have hκ : 0 < κ := P.sideRadius_pos right
  have hβ : 0 < β := P.sideHeight_pos right
  let hm := outerWholeMeasure_radiusScale hκ hβ hcut hcutE hend hprofile
  have hlocal (m : ℕ) := matchedOuter_localizer_radius_ae e hlocalizer right cut heRadius m
  let U₀ : OuterWholeL2 D right cut := (sqrt lam)⁻¹ • hV.toLp H.V
  have hU₀ : (U₀ : ℝ → ℝ) =ᵐ[outerWholeMeasure D right cut]
      fun x => H.V x / sqrt lam := by
    filter_upwards [Lp.coeFn_smul (sqrt lam)⁻¹ (hV.toLp H.V), hV.coeFn_toLp]
      with x hs hx
    rw [hs]
    simp only [Pi.smul_apply, smul_eq_mul, hx, div_eq_mul_inv, mul_comm]
  apply matchedOuterTailEnvelope_of_radius_data F hD hE hPE hj hcut hdeep hcutDeep
    hlam hd.2.1 hd.2.2.1 hη hK H hV R hR hκ hβ hcutE hend hprofile hprofileCut hscale n
  · intro k m
    rw [norm_inverseRadiusOperator_matchedOuterCells h.accumulating.2.1 hPE right
      hκ.ne' hβ hm R k m (hlocal k) (hlocal m)]
    exact (hwhole F H R hR U₀ hU₀ k m).1
  · intro U hU m
    rw [norm_matchedOuterCell_inverseRadiusEquiv h.accumulating.2.1 hPE right
      hκ.ne' hβ hm m (hlocal m) U]
    exact (hwhole F H R hR (inverseRadiusEquiv hκ.ne' hβ hm U)
      (inverseRadiusEquiv_normalized_ae hκ.ne' hβ hm hU) 0 m).2

end ContinuousFlexibility.Radial
