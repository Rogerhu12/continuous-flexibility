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

/-- The existing geometry supply may retain a property of its actual
pair and reference. No analytic conclusion is added to the input. -/
def R10aGeometrySupplyWith (Extra : ∀ {S : SelectedTailData} {K : SeedCentralCutoff} {q length : ℝ},
    SeedRetainedPair S K q length → ConnectedReferenceGeometry → Prop) : Prop :=
  ∀ (B : FixedCentralBorder) (C : ℝ), 1000 ≤ C → ∀ requestedIndex : ℕ,
    ∃ S : SelectedTailData, ∃ _metadata : R10aSelectedMetadata C requestedIndex S,
      ∀ T q length : ℝ, sqrt centralOscillatorA + 2 ≤ T → 0 < q → 0 < length →
        ∃ K : SeedCentralCutoff, ∃ P : SeedRetainedPair S K q length,
          ∃ Γ : ConnectedReferenceGeometry,
            Γ.selected = S ∧ Γ.headLength = q ∧ Γ.Realizes ∧
            Γ.reference.w = P.pair.profile ∧ Γ.reference.phi = P.pair.height ∧
            Γ.centralLeft = exp K.left ∧ Γ.centralRight = exp K.right ∧
            Γ.centralLeft < centralRadius (-T) ∧ centralRadius T < Γ.centralRight ∧
            referenceColumn Γ.reference = fixedCentralColumn B.chi ∧
            EqOn Γ.reference.w (centralRadialProfile 1) (Ioo Γ.centralLeft Γ.centralRight) ∧
            EqOn Γ.reference.phi centralKernelHeight (Ioo Γ.centralLeft Γ.centralRight) ∧
            RadialConstructionGeometry Γ.reference ∧ Extra P Γ

/-- The original construction, retaining its selected family, actual local
model choices, physical cutoff data, and one reference at every frequency.
The proof below is also the proof used by the original public theorem. -/
theorem r10aRegionalConstruction_with_geometry
    (Extra : ∀ {S : SelectedTailData} {K : SeedCentralCutoff} {q length : ℝ},
    SeedRetainedPair S K q length → ConnectedReferenceGeometry → Prop) (hR09 : R09Statement)
    (B : FixedCentralBorder) {C₀ K₀ B₀ T : ℝ}
    (hC₀ : 0 < C₀) (hK₀ : 0 < K₀) (hB₀ : 0 < B₀) (hT : 8 ≤ T)
    (hwindow : selectedFirstInnerModelWindow ≤ T)
    (hcap : sqrt centralOscillatorA + 2 ≤ T)
    (hbuffers : ∀ q : ℕ, 1 ≤ q → BufferHypotheses (B.modelBuffer q T B₀))
    (models : ∀ q : ℕ, 1 ≤ q → InnerBufferLocalizedData (B.modelBuffer q T B₀) C₀ K₀)
    (henergy : ∀ q : ℕ, ∀ hq : 1 ≤ q, ∀ i,
      0 < fixedCentralModelCutEnergy (models q hq) i ∧
        ((models q hq).column i).inwardEnergy ≤
          2 * fixedCentralModelCutEnergy (models q hq) i)
    (herror : ∀ q : ℕ, ∀ hq : 1 ≤ q, ∀ sign : Bool,
      ‖innerTwoCutWeightedError (fixedCentralModelPhysicalKappa (models q hq)) (fun _ => 1)
        ((models q hq).physicalFluxError 1
          (fun i => centralDensityRoot (bufferCut (B.modelBuffer q T B₀) i))) sign‖ ≤
            (1 : ℝ) / 8)
    (hgeometry : R10aGeometrySupplyWith Extra) :
    ∃ CM KM Cstar : ℝ, ∃ N : ℕ,
      ∃ S : SelectedTailData, ∃ metadata : R10aSelectedMetadata Cstar N S,
        0 < CM ∧ 0 < KM ∧ 1000 ≤ Cstar ∧ 4096 ≤ S.chain.index ∧
        (∀ m n j : ℕ, S.chain.index ≤ m → m < n → 2 ≤ j →
          radialFrequencyBand S.chain S.Cstar n j →
          BufferHypotheses
            (innerMorseBufferData (morseChainA S.chain m) (morseChainB S.chain m) j
              (8 * (S.chain.d m : ℝ) ^ 9)) ∧
          ∃ model : InnerBufferLocalizedData
              (innerMorseBufferData (morseChainA S.chain m) (morseChainB S.chain m) j
                (8 * (S.chain.d m : ℝ) ^ 9)) CM KM,
            (∀ i, innerMorseModelNormalizedRemainder model i ≤ 1 / (j : ℝ)) ∧
            InnerMorsePhysicalPoissonBound
              ((metadata.selected.2.2.2.1 S.sigma metadata.selected.2.2.1).1)
              S.chain.index 0 model ∧
            ∀ γ : ℝ, |γ| ≤ 1 → ∀ side : Bool, ∀ height : ℝ, 0 < height → ∀ sign : Bool,
              ‖innerTwoCutWeightedError
                (innerPhysicalCutKappa height (fun _ => 1)
                  (fun i => (model.column i).inwardEnergy))
                (innerMorseCutWeight S.chain.index 0 γ side m)
                (model.physicalFluxError height (fun _ => 1)) sign‖ < (1 : ℝ) / 8) ∧
        ∃ η Kfirst ε H : ℝ, ∃ K : SeedCentralCutoff, ∃ P : SeedRetainedPair S K 1 (H + 1),
          ∃ Γ : ConnectedReferenceGeometry,
            0 < η ∧ η ≤ 1 / 48 ∧ 0 ≤ Kfirst ∧ 0 < ε ∧
            ε + Kfirst * ε ^ 2 ≤ η / 16 ∧ 0 < H ∧ Γ.selected = S ∧ Γ.headLength = 1 ∧ Γ.Realizes ∧
            Γ.reference.w = P.pair.profile ∧ Γ.reference.phi = P.pair.height ∧
            Γ.centralLeft = exp K.left ∧ Γ.centralRight = exp K.right ∧
            Γ.centralLeft < centralRadius (-T) ∧ centralRadius T < Γ.centralRight ∧
            referenceColumn Γ.reference = fixedCentralColumn B.chi ∧
            EqOn Γ.reference.w (centralRadialProfile 1) (Ioo Γ.centralLeft Γ.centralRight) ∧
            EqOn Γ.reference.phi centralKernelHeight (Ioo Γ.centralLeft Γ.centralRight) ∧
            RadialConstructionGeometry Γ.reference ∧ Extra P Γ ∧
            ∀ j : ℕ, 2 ≤ j → Even j →
              ∃ n : ℕ, radialFrequencyBand S.chain S.Cstar n j ∧
                ∃ W : TerminalRegionalData Γ.reference,
                  W.matching.frequency = j ∧ W.matching.transitionIndex = n ∧
                  W.matching.innerLeft = P.sideRadius false * S.joinInner false n ∧
                  W.matching.innerRight = P.sideRadius true * S.joinInner true n ∧
                  W.matching.sourceOuter = modeOuterSource Γ.reference
                    (P.sideRadius false * S.joinInner false n)
                    (P.sideRadius true * S.joinInner true n) ∧
                  ∃ v : Bool → ℝ → ℝ,
                    (∀ side, ContDiff ℝ ∞ (v side) ∧
                      EqOn (v side) (S.outgoing side j)
                        (radialTailInterval (S.family S.sigma) side (S.entry side n)) ∧
                      ContDiff ℝ ∞ (radialRadiusScale (P.sideRadius side) 1 (v side)) ∧
                      RadialNaturalTail Γ.reference side j
                        (P.sideRadius side * S.joinInner side n)
                        (radialRadiusScale (P.sideRadius side) 1 (v side))) ∧
                    (∀ i : Fin 2,
                      W.matching.A i i =
                        (outerUnitState (selectedBoundaryState Γ.reference j
                          (r07OutwardSign (selectedTerminalSide i))
                          (P.sideRadius (selectedTerminalSide i) *
                            S.joinInner (selectedTerminalSide i) n)
                          (radialRadiusScale (P.sideRadius (selectedTerminalSide i)) 1
                            (v (selectedTerminalSide i))))).1 ∧
                      W.matching.B i i =
                        (outerUnitState (selectedBoundaryState Γ.reference j
                          (r07OutwardSign (selectedTerminalSide i))
                          (P.sideRadius (selectedTerminalSide i) *
                            S.joinInner (selectedTerminalSide i) n)
                          (radialRadiusScale (P.sideRadius (selectedTerminalSide i)) 1
                            (v (selectedTerminalSide i))))).2) ∧
                    ((n = S.chain.index ∧ W.matching.margin = η ∧
                      W.inverseCost = Kfirst ∧ W.sourceCost = ε ∧ W.energyCost = ε ∧
                      (∀ i, W.attenuation i = 0) ∧
                      W.cutoff = (fun i => P.firstTerminalCutoff H (selectedTerminalSide i)) ∧
                      ∃ U : ∀ side, SeedPhysicalFirstIncoming P Γ.reference side j,
                        W.standIn = fun i => (U (selectedTerminalSide i)).solution) ∨
                    (S.chain.index < n ∧
                      W.cutoff = (fun i => P.laterTerminalCutoff metadata.geometry n
                        (selectedTerminalSide i)) ∧
                      W.standIn = (fun i => radialRadiusScale
                        (P.sideRadius (selectedTerminalSide i)) 1
                        (S.incoming (selectedTerminalSide i) j)) ∧
                      W.matching.margin =
                        r07UniformTolerance S.Cstar * exp (-(n : ℝ) ^ 2) / 8 ∧
                      W.sourceCost = radialE n ^ terminalMorseRelativeSourceExponent ∧
                      W.energyCost = radialE n ^ terminalMorseEnergyErrorExponent ∧
                      W.inverseCost = radialE n ^ (38 : ℝ) ∧
                      ∀ i, W.attenuation i =
                        terminalMatchingAction S.chain (n - 1) j / 100000000)) := by

  classical
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
      hTL, hTR, hcolumn, hprofile, hcentralHeight, hconstruction, hExtra⟩ :=
    hrealize T 1 (H + 1) hcap (by norm_num) (by linarith only [hHpos])
  have hretainedModels (m n j : ℕ) (hm : S.chain.index ≤ m) (hmn : m < n)
      (hj : 2 ≤ j) (hband : radialFrequencyBand S.chain S.Cstar n j) :=
    hmodelFactory S.chain S.sigma (S.family S.sigma) S.constants
      ((metadata.selected.2.2.2.1 S.sigma metadata.selected.2.2.1).1)
      metadata.requested_index m n j hm hmn hj
      (show radialFrequencyBand S.chain Cstar n j by simpa only [metadata.cstar] using hband)
  refine ⟨CM, KM, Cstar, N, S, metadata, hCM, hKM, hC, hlarge, hretainedModels,
    η, Kfirst, ε, H, K, P, Γ, hη, hηsmall, hKfirst, hε, hfirstBudget, hHpos, hselected, hhead, hΓ, hw, hheight, hleft, hright,
    hTL, hTR, hcolumn, hprofile, hcentralHeight, hconstruction, hExtra, ?_⟩
  intro j hj heven
  obtain ⟨n, hband, _⟩ := metadata.selected.2.2.2.2.1 j hj heven
  have hq : 1 ≤ j / 2 := (even_frequency_half hj heven).1
  have hjq : j = 2 * (j / 2) := (even_frequency_half hj heven).2
  refine ⟨n, hband, ?_⟩
  by_cases hn : n = S.chain.index
  · subst n
    let f : R07FirstFrequency S.chain S.Cstar := ⟨j, hj, heven, hband⟩
    have hbounds := hfirstBounds (j : ℝ) (by exact_mod_cast hj) (hJbound f)
    have houter := P.firstTerminal_outerSupply hΓ hw metadata.selected metadata.geometry
      metadata.family_endpoints metadata.entry metadata.first_two metadata.later_cut
      (by norm_num) hleft hright f (fun side => natural side f) (fun side => hnatural side f)
    obtain ⟨W, hfrequency, hindex, hmarginW, hcostW, hsourceW, henergyW, hcutL, hcutR,
        hattenuation, hcutoff, hstandIn, hsourceOuter, hdiag, hnaturalTarget⟩ :=
      P.exists_first_terminalRegionalData_with_data
      metadata.selected metadata.first_two metadata.first_cone (by norm_num) B hΓ hw
      hleft hright hwindow hC₀ hTL hTR hprofile hcolumn f (j / 2) hq hjq
      (hbuffers (j / 2) hq) (models (j / 2) hq)
      (fun i => (henergy (j / 2) hq i).1) (herror (j / 2) hq) (hcost f)
      hη hε.le hH (by linarith) hfirstBudget hbounds.1 hbounds.2
      (fun side => natural side f) (fun side => hnatural side f)
      (fun side => (metadata.regular side S.chain.index j hj heven hband).1) houter
    refine ⟨W, hfrequency, hindex, hcutL, hcutR, hsourceOuter,
      (fun side => natural side f), ?_, hdiag,
      Or.inl ⟨rfl, hmarginW, hcostW, hsourceW, henergyW, hattenuation, hcutoff, hstandIn⟩⟩
    intro side
    exact ⟨(hnatural side f).1.1, (hnatural side f).1.2.2.1,
      (hnaturalTarget side).1, (hnaturalTarget side).2⟩
  · have hn' : S.chain.index < n := lt_of_le_of_ne hband.1 (Ne.symm hn)
    have hbandC : radialFrequencyBand S.chain Cstar n j := by
      simpa only [metadata.cstar] using hband
    have hbudget := hterminal S.chain metadata.geometry.d_exact hterminalIndex n j hn' hbandC
    obtain ⟨W, hfrequency, hindex, hcutL, hcutR, hcutoff, hstandIn, hmarginW,
        hsourceW, henergyW, hcostW, hattenuation, hsourceOuter, v, hv, hdiag⟩ :=
      P.exists_later_terminalRegionalData_with_data metadata
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
    exact ⟨W, hfrequency, hindex, hcutL, hcutR, hsourceOuter, v, hv, hdiag,
      Or.inr ⟨hn', hcutoff, hstandIn, hmarginW, hsourceW, henergyW, hcostW, hattenuation⟩⟩

/-- The frozen R10a interface forgets the retained implementation data. -/
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
  obtain ⟨CM, KM, Cstar, N, S, metadata, hCM, hKM, hC, hlarge, hmodels,
      η, Kfirst, ε, H, K, P, Γ, hη, hηsmall, hKfirst, hε, hbudget, hH, hselected, hhead, hΓ, hw, hheight, hleft, hright,
      hTL, hTR, hcolumn, hprofile, hcentralHeight, hconstruction, _, hW⟩ :=
    r10aRegionalConstruction_with_geometry
      (fun {_S _K _q _length} _ _ => True) hR09 B hC₀ hK₀ hB₀ hT hwindow hcap
      hbuffers models henergy herror (by
        intro B C hC requested
        obtain ⟨S, metadata, hrealize⟩ := hgeometry B C hC requested
        refine ⟨S, metadata, ?_⟩
        intro T q length hT hq hlength
        obtain ⟨K, P, Γ, hs, hh, hΓ, hw, hphi, hleft, hright,
            hTL, hTR, hcolumn, hmodel, hheight, hconstruction⟩ :=
          hrealize T q length hT hq hlength
        exact ⟨K, P, Γ, hs, hh, hΓ, hw, hphi, hleft, hright,
          hTL, hTR, hcolumn, hmodel, hheight, hconstruction, trivial⟩)
  refine ⟨Γ.reference, hΓ.2.1, hΓ.2.2.1, hconstruction, ?_⟩
  intro j hj heven
  obtain ⟨n, hband, W, hfreq, _⟩ := hW j hj heven
  exact ⟨W, hfreq⟩

end ContinuousFlexibility.Radial
