import ContinuousFlexibility.Blueprint.R10a.Geometry
import ContinuousFlexibility.Radial.InnerMorseMonotoneChoices
import ContinuousFlexibility.Radial.SelectedFirstRegionalData
import ContinuousFlexibility.Radial.SelectedLaterTerminalRegional

/-!
# One reference carrying every actual regional inverse

The central models and their costs are chosen first. A common frequency
threshold then fixes the terminal budget, and a larger starting index
absorbs the actual later inverse cost. The selected tail precedes the
finite first-band margin and cone length. Only then is one reference
realized, and that same reference serves every even frequency.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open scoped Topology ContDiff Matrix.Norms.L2Operator
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint

theorem r10aRegionalConstruction (hR09 : R09Statement)
    (hgeometry : R10aGeometrySupply) :
    ∃ D : ReferenceData, IsAccumulatingProfile D ∧ RadialTrueBorder D ∧
      RadialConstructionGeometry D ∧
      ∀ j : ℕ, 2 ≤ j → Even j →
        ∃ W : TerminalRegionalData D, W.matching.frequency = j := by
  classical
  obtain ⟨B⟩ := exists_fixedCentralBorder
  obtain ⟨C₀, K₀, B₀, T, hC₀, hK₀, hB₀, hT, hwindow, hcap, hfar, hcentral⟩ :=
    B.exists_small_error_model_buffers hR09 selectedFirstInnerModelWindow
  choose hbuffers models henergy herror using hcentral
  obtain ⟨CM, KM, hCM, hKM, hMorse⟩ :=
    exists_innerMorsePhysicalChoices_atLeast hR09 (by norm_num : (0 : ℝ) ≤ 0)
  obtain ⟨Cstar, hfloor, hCstar, hCgeometry, hMorseIndex⟩ :=
    hMorse selectedTerminalCstarFloor
  obtain ⟨Nterm, hNterm, hterminal⟩ := exists_selectedTerminalBudgetStart hfloor
  let Nbudget := fixedCentralLaterBudgetStart T B₀ C₀ K₀ CM Cstar
    hC₀.le hCM.le hCstar.le Nterm
  have htermBudget : Nterm ≤ Nbudget :=
    (fixedCentralLaterBudgetStart_spec T B₀ C₀ K₀ CM Cstar
      hC₀.le hCM.le hCstar.le Nterm).1
  obtain ⟨N, hNbudget, hNlarge, hNweight, hmodelFactory⟩ :=
    hMorseIndex (1 / 8) (by norm_num) Nbudget
  have hC : 1000 ≤ Cstar := selectedTerminalCstarFloor_large.trans hfloor
  obtain ⟨S, metadata, hrealize⟩ := hgeometry B Cstar hC N
  have hCS : 1000 ≤ S.Cstar := by rwa [metadata.cstar]
  have hlarge : 4096 ≤ S.chain.index := hNlarge.trans metadata.requested_index
  have hterminalIndex : Nterm ≤ S.chain.index :=
    htermBudget.trans (hNbudget.trans metadata.requested_index)
  have hstart : fixedCentralLaterBudgetStart T B₀ C₀ K₀ CM S.Cstar
      hC₀.le hCM.le metadata.selected.1.le Nterm ≤ S.chain.index := by
    simpa only [metadata.cstar, Nbudget] using hNbudget.trans metadata.requested_index
  obtain ⟨natural, η, hη, hηsmall, hnatural⟩ :=
    exists_selected_first_uniform_margin metadata.selected
      (fun side j hj heven hband => metadata.regular side S.chain.index j hj heven hband)
      metadata.first_cone
  let firstCost : R07FirstFrequency S.chain S.Cstar → ℝ := fun f =>
    sqrt 2 * fixedCentralFirstInverseCost
      (models (f.1 / 2) (even_frequency_half f.2.1 f.2.2.1).1)
      (2 * ((f.1 / 2 : ℕ) : ℝ)) T B₀
  obtain ⟨Kfirst₀, hKfirst₀⟩ := (Set.finite_range firstCost).bddAbove
  let Kfirst : ℝ := max 0 Kfirst₀
  have hKfirst : 0 ≤ Kfirst := le_max_left _ _
  have hcost (f : R07FirstFrequency S.chain S.Cstar) : firstCost f ≤ Kfirst :=
    (hKfirst₀ (mem_range_self f)).trans (le_max_right _ _)
  let J : ℝ := max 2 (radialFrequencyThreshold S.chain S.Cstar S.chain.index)
  have hJ : 0 < J := (by norm_num : (0 : ℝ) < 2).trans_le (le_max_left _ _)
  have hJbound (f : R07FirstFrequency S.chain S.Cstar) : (f.1 : ℝ) ≤ J :=
    f.2.2.2.2.2.le.trans (le_max_right _ _)
  obtain ⟨ε, H, hε, hH, hHpos, hfirstBudget, hfirstBounds⟩ :=
    exists_terminalCone_matching_budget hJ hη hKfirst
  obtain ⟨K, P, Γ, hselected, hhead, hΓ, hw, hheight, hleft, hright,
      hTL, hTR, hcolumn, hprofile, hcentralHeight, hconstruction⟩ :=
    hrealize T 1 (H + 1) hcap (by norm_num) (by linarith only [hHpos])
  refine ⟨Γ.reference, hΓ.2.1, hΓ.2.2.1, hconstruction, ?_⟩
  intro j hj heven
  obtain ⟨n, hband, _⟩ := metadata.selected.2.2.2.2.1 j hj heven
  have hq : 1 ≤ j / 2 := (even_frequency_half hj heven).1
  have hjq : j = 2 * (j / 2) := (even_frequency_half hj heven).2
  by_cases hn : n = S.chain.index
  · subst n
    let f : R07FirstFrequency S.chain S.Cstar := ⟨j, hj, heven, hband⟩
    have hbounds := hfirstBounds (j : ℝ) (by exact_mod_cast hj) (hJbound f)
    have houter := P.firstTerminal_outerSupply hΓ hw metadata.selected metadata.geometry
      metadata.family_endpoints metadata.entry metadata.first_two metadata.later_cut
      (by norm_num) hleft hright f (fun side => natural side f) (fun side => hnatural side f)
    obtain ⟨W, hfrequency, _⟩ := P.exists_first_terminalRegionalData
      metadata.selected metadata.first_two metadata.first_cone (by norm_num) B hΓ hw
      hleft hright hwindow hC₀ hTL hTR hprofile hcolumn f (j / 2) hq hjq
      (hbuffers (j / 2) hq) (models (j / 2) hq)
      (fun i => (henergy (j / 2) hq i).1) (herror (j / 2) hq) (hcost f)
      hη hε.le hH (by linarith) hfirstBudget hbounds.1 hbounds.2
      (fun side => natural side f) (fun side => hnatural side f)
      (fun side => (metadata.regular side S.chain.index j hj heven hband).1) houter
    exact ⟨W, hfrequency⟩
  · have hn' : S.chain.index < n := lt_of_le_of_ne hband.1 (Ne.symm hn)
    have hbandC : radialFrequencyBand S.chain Cstar n j := by
      simpa only [metadata.cstar] using hband
    have hbudget := hterminal S.chain metadata.geometry.d_exact hterminalIndex n j hn' hbandC
    obtain ⟨W, hfrequency, _⟩ := P.exists_later_terminalRegionalData metadata
      (by norm_num) B hΓ hw hleft hright hT hcap hC₀ hK₀.le hCM hTL hTR hprofile
      (selectedFirstInnerModelWindow_spec.2.2 T hwindow) hcolumn Nterm hstart hlarge hCS
      hn' hj heven hband (by simpa only [metadata.cstar] using hbudget)
      (hbuffers (j / 2) hq) (models (j / 2) hq) (henergy (j / 2) hq)
      (herror (j / 2) hq) (by
        intro m hm hmn
        have hreal := (metadata.selected.2.2.2.1 S.sigma metadata.selected.2.2.1).1
        obtain ⟨hbuf, M, hrem, _, herr⟩ := hmodelFactory S.chain S.sigma (S.family S.sigma)
          S.constants hreal metadata.requested_index m n j hm hmn hj hbandC
        refine ⟨hbuf, M, hrem, ?_⟩
        intro side height hheight sign
        exact (herr 0 (by norm_num) side height hheight sign).le)
    exact ⟨W, hfrequency⟩

end ContinuousFlexibility.Radial
