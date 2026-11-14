module

public import ContinuousFlexibility.Radial.MatchedRetainedInnerEnvelope
public import ContinuousFlexibility.Radial.MatchedInnerFirstBand
public import ContinuousFlexibility.Radial.MatchedMorseInitialWindow
public import ContinuousFlexibility.Radial.MatchedFiniteEnvelope
public import ContinuousFlexibility.Radial.R11aRetainedFamily

/-!
# Uniform actual inner channels of the completed retained family

One fixed seam window and the primitive central and Morse suppliers
give a common cost for every later original finite chain. The original
finite first band is combined with these estimates only afterwards.
All operators and both columns are those of the same completed W/G
family, and the channel labels remain the original canonical labels.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff Matrix.Norms.L2Operator

theorem SeedRetainedPair.exists_uniform_selectedInner_matching_bounds
    {S : SelectedTailData} {Kseed : SeedCentralCutoff}
    {headLength length T Cstar : ℝ} {requested : ℕ}
    (P : SeedRetainedPair S Kseed headLength length)
    (metadata : R10aSelectedMetadata Cstar requested S)
    (Γ : ConnectedReferenceGeometry) (hΓ : Γ.Realizes)
    (hP : RadialPartition Γ.reference)
    (hw : Γ.reference.w = P.pair.profile) (hhead : 0 < headLength) (hT : 8 ≤ T)
    (hleft : Γ.centralLeft = exp Kseed.left) (hright : Γ.centralRight = exp Kseed.right)
    (hTL : Γ.centralLeft < centralRadius (-T)) (hTR : centralRadius T < Γ.centralRight)
    (Bfixed : FixedCentralBorder) (hcap : sqrt centralOscillatorA + 2 ≤ T)
    (hcolumn : referenceColumn Γ.reference = fixedCentralColumn Bfixed.chi)
    (hwindow : selectedFirstInnerModelWindow ≤ T)
    (hmodel : EqOn Γ.reference.w (centralRadialProfile 1) (Ioo Γ.centralLeft Γ.centralRight))
    {B₀ C₀ K₀ CM KM : ℝ} (hC₀ : 0 < C₀) (hCM : 0 < CM)
    (hCstar : 1000 ≤ S.Cstar) (hN : 4096 ≤ S.chain.index)
    (models : ∀ q : ℕ, 1 ≤ q → InnerBufferLocalizedData
      (Bfixed.modelBuffer q T B₀) C₀ K₀)
    (hbuffers : ∀ q : ℕ, 1 ≤ q → BufferHypotheses (Bfixed.modelBuffer q T B₀))
    (henergy : ∀ q : ℕ, ∀ hq : 1 ≤ q, ∀ i,
      0 < fixedCentralModelCutEnergy (models q hq) i ∧
        ((models q hq).column i).inwardEnergy ≤ 2 * fixedCentralModelCutEnergy (models q hq) i)
    (hrem : ∀ q : ℕ, ∀ hq : 1 ≤ q, ∀ i,
      (sqrt 12 * (centralRadiusWeightConstant * (1 + T)) + 1) *
        (innerBufferRemainderEnvelope (Bfixed.modelBuffer q T B₀) C₀ K₀ i /
          sqrt (fixedCentralModelCutEnergy (models q hq) i)) ≤ 1 / (2 * (q : ℝ)))
    (herror : ∀ q : ℕ, ∀ hq : 1 ≤ q, ∀ sign : Bool,
      ‖innerTwoCutWeightedError (fixedCentralModelPhysicalKappa (models q hq)) (fun _ => 1)
        ((models q hq).physicalFluxError 1
          (fun i => centralDensityRoot (bufferCut (Bfixed.modelBuffer q T B₀) i))) sign‖ ≤
        (1 : ℝ) / 8)
    (hsupplier : ∀ m n jf : ℕ, S.chain.index ≤ m → m < n → 2 ≤ jf →
      radialFrequencyBand S.chain S.Cstar n jf →
      BufferHypotheses
        (innerMorseBufferData (morseChainA S.chain m) (morseChainB S.chain m) jf
          (8 * (S.chain.d m : ℝ) ^ 9)) ∧
      ∃ model : InnerBufferLocalizedData
          (innerMorseBufferData (morseChainA S.chain m) (morseChainB S.chain m) jf
            (8 * (S.chain.d m : ℝ) ^ 9)) CM KM,
        (∀ i, innerMorseModelNormalizedRemainder model i ≤ 1 / (jf : ℝ)) ∧
        InnerMorsePhysicalPoissonBound
          ((metadata.selected.2.2.2.1 S.sigma metadata.selected.2.2.1).1)
          S.chain.index 0 model ∧
        ∀ γ : ℝ, |γ| ≤ 1 → ∀ side : Bool, ∀ height : ℝ, 0 < height → ∀ sign : Bool,
          ‖innerTwoCutWeightedError
            (innerPhysicalCutKappa height (fun _ => 1)
              (fun i => (model.column i).inwardEnergy))
            (innerMorseCutWeight S.chain.index 0 γ side m)
            (model.physicalFluxError height (fun _ => 1)) sign‖ < (1 : ℝ) / 8)
    (hcoordinates : R11aRetainedCoordinates P Γ)
    (W : ℕ → TerminalRegionalData Γ.reference)
    (G : ℕ → RadialModePair Γ.reference →L[ℝ] RadialModePair Γ.reference)
    (hactual : ∀ q, ActualMatchedRepresentation Γ.reference (G q) (W q).matching)
    (hfrequency : ∀ q, (W q).matching.frequency = 2 * (q + 1))
    (hband : ∀ q, radialFrequencyBand S.chain S.Cstar
      (W q).matching.transitionIndex (W q).matching.frequency)
    (hML : ∀ q, (W q).matching.innerLeft =
      P.sideRadius false * S.joinInner false (W q).matching.transitionIndex)
    (hMR : ∀ q, (W q).matching.innerRight =
      P.sideRadius true * S.joinInner true (W q).matching.transitionIndex)
    (hlater : ∀ q, S.chain.index < (W q).matching.transitionIndex →
      (W q).cutoff = (fun i => P.laterTerminalCutoff metadata.geometry
        (W q).matching.transitionIndex (selectedTerminalSide i)) ∧
      (W q).standIn = (fun i => radialRadiusScale (P.sideRadius (selectedTerminalSide i)) 1
        (S.incoming (selectedTerminalSide i) (W q).matching.frequency)) ∧
      (W q).sourceCost =
        radialE (W q).matching.transitionIndex ^ terminalMorseRelativeSourceExponent ∧
      ∀ i, (W q).attenuation i = terminalMatchingAction S.chain
        ((W q).matching.transitionIndex - 1) (W q).matching.frequency / 100000000) :
    ∃ CI aI CPI bI : ℝ, 0 < CI ∧ 0 ≤ aI ∧ 0 < CPI ∧ 0 ≤ bI ∧
      (∀ q u v,
        ‖matchedModeChannel Γ.reference hP u ∘L (W q).matching.innerInverse ∘L
          matchingSourceInnerCLM Γ.reference (W q).matching
            (actualMatchedRepresentation_localRealizations (hactual q)) ∘L
          (matchedModeScalarGate Γ.reference (decide (q = 0)) ∘L
            matchedModeChannel Γ.reference hP v)‖ ≤
          CI * exp (aI *
            (radialQ (referenceRawChannelLevel (S.family S.sigma) u) +
              radialQ (referenceRawChannelLevel (S.family S.sigma) v)) -
            |radialS (referenceRawChannelLevel (S.family S.sigma) u) -
              radialS (referenceRawChannelLevel (S.family S.sigma) v)|)) ∧
      (∀ q u i, ‖matchedModeChannel Γ.reference hP u ((W q).matching.innerPoisson i)‖ ≤
        CPI * exp (bI *
          (radialQ (referenceRawChannelLevel (S.family S.sigma) u) +
            radialQ (W q).matching.transitionIndex) -
          |radialS (referenceRawChannelLevel (S.family S.sigma) u) -
            radialS (W q).matching.transitionIndex|)) := by
  classical
  let D₀ := S.family S.sigma
  let level := referenceRawChannelLevel D₀
  have hreal := (metadata.selected.2.2.2.1 S.sigma metadata.selected.2.2.1).1
  obtain ⟨J, hJ, _, hwin⟩ := exists_matchedMorse_initial_localizer_window hreal S.chain.index
  obtain ⟨e, floor, _, _, _, _, hχ, heL, heR, _, _, _⟩ := hcoordinates
  have he : ∀ side x, (if side then morseChainSeam S.chain true S.chain.index ≤ x
      else x ≤ morseChainSeam S.chain false S.chain.index) →
        e.symm x = P.sideRadius side * x := by
    intro side x hx
    cases side
    · have hentry : S.entry false S.chain.index = morseChainSeam S.chain false S.chain.index := by
        rw [metadata.entry]
        rfl
      exact heL x (by simpa only [hentry, Bool.false_eq_true, ite_false] using hx)
    · have hentry : S.entry true S.chain.index = morseChainSeam S.chain true S.chain.index := by
        rw [metadata.entry]
        rfl
      exact heR x (by simpa only [hentry, ite_true] using hx)
  have hχ' : ∀ m x, Γ.reference.localizer m x = D₀.localizer m (e x) := by
    intro m x
    exact congrFun (congrFun hχ m) x
  have hTpos : 0 < T := by linarith only [hT]
  let cost := matchedRetainedInnerWeightCost S.chain.index T B₀ C₀ CM
  have hcost : 0 < cost :=
    matchedRetainedInnerWeightCost_pos S.chain.index T B₀ hC₀.le hCM.le
  let RC := matchedMorseLocalizerWeightConstant S.chain.index J
  have hRC : 1 ≤ RC := matchedMorseLocalizerWeightConstant_ge_one _ _
  let CI₀ := (sqrt 2 * cost) * RC ^ 2
  let CPI₀ := ((1 + sqrt 2 * cost) * exp (radialS S.chain.index)) * RC
  let aP := matchedMorseTerminalColumnExponent 41414
  have hCI₀ : 0 ≤ CI₀ := by dsimp only [CI₀]; positivity
  have hCPI₀ : 0 ≤ CPI₀ := by dsimp only [CPI₀]; positivity
  have haP : 0 ≤ aP := matchedMorseTerminalColumnExponent_nonneg _
  have hlarge (q : ℕ) (hq : S.chain.index < (W q).matching.transitionIndex) :
      (∀ u v,
        ‖matchedModeChannel Γ.reference hP u ∘L (W q).matching.innerInverse ∘L
          matchingSourceInnerCLM Γ.reference (W q).matching
            (actualMatchedRepresentation_localRealizations (hactual q)) ∘L
          (matchedModeScalarGate Γ.reference (decide (q = 0)) ∘L
            matchedModeChannel Γ.reference hP v)‖ ≤
          CI₀ * exp (41414 * (radialQ (level u) + radialQ (level v)) -
            |radialS (level u) - radialS (level v)|)) ∧
      (∀ u i, ‖matchedModeChannel Γ.reference hP u ((W q).matching.innerPoisson i)‖ ≤
        CPI₀ * exp (aP * (radialQ (level u) + radialQ (W q).matching.transitionIndex) -
          |radialS (level u) - radialS (W q).matching.transitionIndex|)) := by
    let k := (W q).matching.transitionIndex - S.chain.index
    have hk : 0 < k := by dsimp only [k]; omega
    have hnk : S.chain.index + k = (W q).matching.transitionIndex :=
      Nat.add_sub_of_le (hband q).1
    have hqf : 1 ≤ q + 1 := by omega
    have hj : 2 ≤ (W q).matching.frequency := by rw [hfrequency q]; omega
    have heven : Even (W q).matching.frequency := by
      rw [hfrequency q]
      exact ⟨q + 1, by omega⟩
    have hb : radialFrequencyBand S.chain S.Cstar (S.chain.index + k)
        (W q).matching.frequency := by simpa only [hnk] using hband q
    have hbq : radialFrequencyBand S.chain S.Cstar (S.chain.index + k) (2 * (q + 1)) := by
      simpa only [hfrequency q] using hb
    obtain ⟨hB, tailModels, CW, hCW, hS, hbound⟩ :=
      P.exists_retainedFamily_innerWeightData metadata hΓ hw hhead hT
        hleft hright hTL hTR k hk hwindow hmodel Bfixed hcap hcolumn
        (q + 1) hqf (hbuffers (q + 1) hqf) (models (q + 1) hqf)
        hC₀ hCM hN hbq (henergy (q + 1) hqf) (hrem (q + 1) hqf)
        (herror (q + 1) hqf) hsupplier
    let H := P.retainedMorseInnerGeometry (matchingProfileGeometry hΓ.2.1) hw
      metadata.selected metadata.geometry metadata.first_two hhead hTpos
      hleft hright hTL hTR k hk
    let center := innerModelChainPiece (innerMorseInnerCenter k)
    let column := matchingBorderVector Γ.reference hΓ.2.1 hΓ.2.2.1
    have hcore := P.retainedFamily_inner_central_core metadata hΓ hw hhead hT
      hleft hright hTL hTR k hk
    have hcenter := P.retainedMorseInnerGeometry_center (matchingProfileGeometry hΓ.2.1) hw
      metadata.selected metadata.geometry metadata.first_two hhead hTpos
      hleft hright hTL hTR k hk
    let centralModel := fixedCentralPhysicalModelChart Bfixed Γ.reference hΓ.2.1 hΓ.2.2.1
      H center (q + 1) hT hcap hcolumn hcore
      (retainedMorse_central_weight_identity hTL hTR hmodel) hcenter.1 hcenter.2
      (hbuffers (q + 1) hqf) (models (q + 1) hqf)
    have hjpos : 0 < 2 * ((q + 1 : ℕ) : ℝ) := by positivity
    let Chain := P.retainedMorseActualChain (matchingProfileGeometry hΓ.2.1) hw
      metadata.selected metadata.geometry metadata.first_two hhead hTpos
      hleft hright hTL hTR k hk metadata.initial_bridge_positive hmodel
      (selectedFirstInnerModelWindow_spec.2.2 T hwindow)
      (centralModelBordered (q + 1)) (2 * ((q + 1 : ℕ) : ℝ)) hjpos
      column hB tailModels centralModel
    have hbool : centralModelBordered (q + 1) = decide ((W q).matching.frequency = 2) := by
      by_cases hz : q = 0
      · rw [hfrequency q]
        simp [centralModelBordered, hz]
      · have hq1 : q + 1 ≠ 1 := by omega
        have hf : (W q).matching.frequency ≠ 2 := by rw [hfrequency q]; omega
        simp only [centralModelBordered, if_neg hq1, decide_eq_false hf]
    have hfreq : 2 * ((q + 1 : ℕ) : ℝ) = ((W q).matching.frequency : ℝ) := by
      simp only [hfrequency q, Nat.cast_mul, Nat.cast_ofNat]
    obtain ⟨hcut, hstand, hsource, hatt⟩ := hlater q hq
    have hcut' : (W q).cutoff = (fun i => P.laterTerminalCutoff metadata.geometry
        (S.chain.index + k) (selectedTerminalSide i)) := by simpa only [hnk] using hcut
    have hsource' : (W q).sourceCost =
        radialE (S.chain.index + k) ^ terminalMorseRelativeSourceExponent := by
      simpa only [hnk] using hsource
    have hatt' : ∀ i, (W q).attenuation i = terminalMatchingAction S.chain
        (S.chain.index + k - 1) (W q).matching.frequency / 100000000 := by
      simpa only [hnk] using hatt
    have hL : (W q).matching.innerLeft =
        P.sideRadius false * S.joinInner false (S.chain.index + k) := by
      simpa only [hnk] using hML q
    have hR : (W q).matching.innerRight =
        P.sideRadius true * S.joinInner true (S.chain.index + k) := by
      simpa only [hnk] using hMR q
    have hh := P.retainedMorse_actual_inner_envelopes metadata hΓ hw hhead hTpos
      hleft hright hTL hTR Bfixed hcap hcolumn hCstar k hk hN e he hχ' hJ hwin
      (W q) (actualMatchedRepresentation_localRealizations (hactual q)) hL hR hj heven
      hb hcut' hstand hsource' hatt' Chain hbool hfreq hS CW hCW hP hcost.le hbound
    have hgate : decide ((W q).matching.frequency = 2) = decide (q = 0) := by
      by_cases hz : q = 0
      · rw [hfrequency q]
        simp [hz]
      · have hf : (W q).matching.frequency ≠ 2 := by rw [hfrequency q]; omega
        simp only [hf, hz, decide_false]
    rw [hgate] at hh
    simpa only [CI₀, CPI₀, RC, cost, aP, level, D₀, hnk, ContinuousLinearMap.comp_assoc]
      using hh
  obtain ⟨CF, hCF, hfirst, hfirstP⟩ :=
    matchedInner_actual_firstBand_spatial_envelope hΓ.2.1 hP G (fun q => (W q).matching)
      hactual hfrequency S.chain S.Cstar level (fun q => decide (q = 0))
  refine ⟨max CF CI₀, 41414, max CF CPI₀, aP, hCF.trans_le (le_max_left _ _),
    by norm_num, hCF.trans_le (le_max_left _ _), haP, ?_, ?_⟩
  · intro q u v
    by_cases hq : (W q).matching.transitionIndex = S.chain.index
    · have hb : radialFrequencyBand S.chain S.Cstar S.chain.index
          (W q).matching.frequency := by simpa only [hq] using hband q
      have hh := (hfirst q hb u v).trans (by
        simpa only [zero_mul, zero_sub] using
          matchedEnvelope_mono hCF.le (le_max_left CF CI₀)
            (by norm_num : (0 : ℝ) ≤ 41414) (level u) (level v))
      simpa only [ContinuousLinearMap.comp_assoc] using hh
    · have hn : S.chain.index < (W q).matching.transitionIndex :=
        lt_of_le_of_ne (hband q).1 (Ne.symm hq)
      exact ((hlarge q hn).1 u v).trans
        (matchedEnvelope_mono hCI₀ (le_max_right CF CI₀) le_rfl (level u) (level v))
  · intro q u i
    by_cases hq : (W q).matching.transitionIndex = S.chain.index
    · have hb : radialFrequencyBand S.chain S.Cstar S.chain.index
          (W q).matching.frequency := by simpa only [hq] using hband q
      have hh := (hfirstP q hb u i).trans (by
        simpa only [zero_mul, zero_sub] using
          matchedEnvelope_mono hCF.le (le_max_left CF CPI₀) haP (level u) S.chain.index)
      simpa only [hq] using hh
    · have hn : S.chain.index < (W q).matching.transitionIndex :=
        lt_of_le_of_ne (hband q).1 (Ne.symm hq)
      exact ((hlarge q hn).2 u i).trans
        (matchedEnvelope_mono hCPI₀ (le_max_right CF CPI₀) le_rfl
          (level u) (W q).matching.transitionIndex)

end ContinuousFlexibility.Radial
