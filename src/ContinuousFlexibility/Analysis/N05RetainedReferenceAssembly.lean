import ContinuousFlexibility.Radial.R11aActualAssembly
import ContinuousFlexibility.Radial.N05FixedReferenceRetention
import Lean.Util.CollectAxioms

/-!
# Retaining the actual R11a geometry through radial-reference completion

Draft integration target: the complete R11a dependency closure from
`bfa87806ee8e2ca5794e919764f37c8424b47b30`.
This file deliberately remains outside `src/` until those upstream modules
are integrated. It contains complete proof terms and no new assumptions.

The two fixed-reference helpers use the actual spatial envelope and call
`referenceSchur_common_inverse_of_modal_envelope` directly. The local
R11b/R12 retention helper then completes that same reference. The final
existence theorem retains every certificate of
`r11a_exists_quantitative_geometry_family`, including its actual
`SeedRetainedPair`, connected geometry, coordinate transport and full
terminal matching family. Its only added field is
`IsRadialReference Γ.reference`.

The closed inputs are supplied by `r11a_closed_regional_inputs`, whose
proof uses the proved R06a/R06b/R06c nodes and `r09Statement`. No open
Blueprint theorem is applied.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Real
open ContinuousFlexibility.Radial

/-- The actual modal envelope completes the original reference data. -/
theorem n05_isRadialReference_of_modal_envelope {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    (hconstruction : RadialConstructionGeometry D)
    (G : ℕ → RadialModePair D →L[ℝ] RadialModePair D)
    (hG : ∀ n : ℕ, ModeInverseProperties D (2 * (n + 1)) (G n))
    (hmatched : ∀ n : ℕ, ∃ M : RadialMatchingData D,
      M.frequency = 2 * (n + 1) ∧ ActualMatchedRepresentation D (G n) M)
    (N : ℕ) (hfibers : ∀ n, Set.Finite {m | D.cellIndex m = n})
    (hcard : ∀ n, Set.ncard {m | D.cellIndex m = n} ≤ N)
    {C₀ a : ℝ} (hC₀ : 0 < C₀)
    (hmodal : ∀ n k m,
      ‖matchedModeChannel D hD.choose_spec.2.1 k ∘L
          (G n ∘L matchedModeScalarGate D (decide (n = 0))) ∘L
            matchedModeChannel D hD.choose_spec.2.1 m‖ ≤
        C₀ * Real.exp
          (a * (radialQ (referenceRawChannelLevel D k) +
            radialQ (referenceRawChannelLevel D m)) -
            |radialS (referenceRawChannelLevel D k) -
              radialS (referenceRawChannelLevel D m)|)) :
    IsRadialReference D := by
  obtain ⟨M₀, M₁, _, H, hH⟩ :=
    referenceSchur_common_inverse_of_modal_envelope hD hborder G hG N hfibers hcard
      hC₀ hmodal
  have hmodes : ∀ j : ℕ, 2 ≤ j → Even j →
      ∃ Gmode : RadialModePair D →L[ℝ] RadialModePair D,
        ModeInverseProperties D j Gmode := by
    intro j hj heven
    obtain ⟨k, hk⟩ := heven
    have hkpos : 0 < k := by omega
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hkpos)
    have hjn : j = 2 * (n + 1) := by omega
    rw [hjn]
    exact ⟨G n, hG n⟩
  obtain ⟨Mdata, _, hactual⟩ := hmatched 0
  exact n05_isRadialReference_of_fixed_mode_inverse hD hborder hconstruction hmodes
    ⟨G 0, Mdata, hactual⟩
    (ε := 1 / 8) (M₀ := M₀) (M₁ := M₁) (G := H)
    (by norm_num) (by norm_num) hH


/-- Combining the four actual regional estimates retains the input reference. -/
theorem n05_isRadialReference_of_regional_envelopes {D₀ D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    (hconstruction : RadialConstructionGeometry D)
    (G : ℕ → RadialModePair D →L[ℝ] RadialModePair D)
    (M : ℕ → RadialMatchingData D)
    (hactual : ∀ q, ActualMatchedRepresentation D (G q) (M q))
    (hfrequency : ∀ q, (M q).frequency = 2 * (q + 1))
    (floor fiberBound : ℕ)
    (hfloor : D.cellIndex = fun m => max (D₀.cellIndex m) floor)
    (hfibers : ∀ n, Set.Finite {m | D.cellIndex m = n})
    (hcard : ∀ n, Set.ncard {m | D.cellIndex m = n} ≤ fiberBound)
    {CI CO CPI CPO Cκ aI aO bI bO : ℝ}
    (hCI : 0 < CI) (hCO : 0 < CO) (hCPI : 0 < CPI) (hCPO : 0 < CPO)
    (hCκ : 0 < Cκ)
    (haI : 0 ≤ aI) (haO : 0 ≤ aO) (hbI : 0 ≤ bI) (hbO : 0 ≤ bO)
    (hinner : ∀ q k m,
      ‖matchedModeChannel D hD.choose_spec.2.1 k ∘L (M q).innerInverse ∘L
        matchingSourceInnerCLM D (M q) (actualMatchedRepresentation_localRealizations (hactual q)) ∘L
          (matchedModeScalarGate D (decide (q = 0)) ∘L
            matchedModeChannel D hD.choose_spec.2.1 m)‖ ≤
        CI * exp (aI * (radialQ (referenceRawChannelLevel D₀ k) +
          radialQ (referenceRawChannelLevel D₀ m)) -
          |radialS (referenceRawChannelLevel D₀ k) -
            radialS (referenceRawChannelLevel D₀ m)|))
    (houter : ∀ q k m,
      ‖matchedModeChannel D hD.choose_spec.2.1 k ∘L (M q).outerInverse ∘L
        matchingSourceOuterCLM D (M q) (actualMatchedRepresentation_localRealizations (hactual q)) ∘L
          (matchedModeScalarGate D (decide (q = 0)) ∘L
            matchedModeChannel D hD.choose_spec.2.1 m)‖ ≤
        CO * exp (aO * (radialQ (referenceRawChannelLevel D₀ k) +
          radialQ (referenceRawChannelLevel D₀ m)) -
          |radialS (referenceRawChannelLevel D₀ k) -
            radialS (referenceRawChannelLevel D₀ m)|))
    (hPi : ∀ q k i,
      ‖matchedModeChannel D hD.choose_spec.2.1 k ((M q).innerPoisson i)‖ ≤
        CPI * exp (bI * (radialQ (referenceRawChannelLevel D₀ k) +
          radialQ (M q).transitionIndex) -
          |radialS (referenceRawChannelLevel D₀ k) - radialS (M q).transitionIndex|))
    (hPo : ∀ q k i,
      ‖matchedModeChannel D hD.choose_spec.2.1 k ((M q).outerPoisson i)‖ ≤
        CPO * exp (bO * (radialQ (referenceRawChannelLevel D₀ k) +
          radialQ (M q).transitionIndex) -
          |radialS (referenceRawChannelLevel D₀ k) - radialS (M q).transitionIndex|))
    (hmargin : ∀ q, 4 / (M q).margin + 1 ≤ Cκ * exp (radialQ (M q).transitionIndex)) :
    IsRadialReference D := by
  let a : ℝ := aI + aO + bI + bO
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  have haI' : aI ≤ a := by dsimp only [a]; linarith only [haO, hbI, hbO]
  have haO' : aO ≤ a := by dsimp only [a]; linarith only [haI, hbI, hbO]
  have hbI' : bI ≤ a := by dsimp only [a]; linarith only [haI, haO, hbO]
  have hbO' : bO ≤ a := by dsimp only [a]; linarith only [haI, haO, hbI]
  have hCI' : CI ≤ CI + CO := by linarith only [hCO]
  have hCO' : CO ≤ CI + CO := by linarith only [hCI]
  have hCPI' : CPI ≤ CPI + CPO := by linarith only [hCPO]
  have hCPO' : CPO ≤ CPI + CPO := by linarith only [hCPI]
  obtain ⟨C, hC, hbound⟩ :=
    matchedMode_actual_channels_spatial_envelope hD hD.choose_spec.2.1 G M hactual
      (fun q => (M q).transitionIndex) (referenceRawChannelLevel D₀)
      (a := a) (d := 1) (C₀ := CI + CO) (Cₚ := CPI + CPO)
      ha (by norm_num) (add_pos hCI hCO) (add_pos hCPI hCPO) hCκ
      (fun q k m => (hinner q k m).trans
        (matchedEnvelope_mono hCI.le hCI' haI'
          (referenceRawChannelLevel D₀ k) (referenceRawChannelLevel D₀ m)))
      (fun q k m => (houter q k m).trans
        (matchedEnvelope_mono hCO.le hCO' haO'
          (referenceRawChannelLevel D₀ k) (referenceRawChannelLevel D₀ m)))
      (fun q k i => (hPi q k i).trans
        (matchedEnvelope_mono hCPI.le hCPI' hbI'
          (referenceRawChannelLevel D₀ k) (M q).transitionIndex))
      (fun q k i => (hPo q k i).trans
        (matchedEnvelope_mono hCPO.le hCPO' hbO'
          (referenceRawChannelLevel D₀ k) (M q).transitionIndex))
      (fun q => by simpa only [one_mul] using hmargin q)
  have hG (q : ℕ) : ModeInverseProperties D (2 * (q + 1)) (G q) := by
    simpa only [hfrequency q] using
      actualMatchedRepresentation_modeInverseProperties hD hborder (hactual q)
  refine n05_isRadialReference_of_modal_envelope hD hborder hconstruction G hG
    (fun q => ⟨M q, hfrequency q, hactual q⟩) fiberBound hfibers hcard
    (C₀ := C * exp (radialS floor)) (a := 3 * a + 1)
    (mul_pos hC (exp_pos _)) ?_
  intro q k m
  exact (hbound q k m).trans
    (referenceRawChannel_envelope_floor hfloor hC.le (by linarith only [ha]) k m)

end ContinuousFlexibility.Statements

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open scoped Topology ContDiff Matrix.Norms.L2Operator
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint

/-- The full retained R11a construction, with radial-reference completion on
its original `Γ.reference`. All original witnesses and certificates survive. -/
theorem n05_exists_retained_radial_reference :
    ∃ B : FixedCentralBorder, ∃ C₀ K₀ B₀ T : ℝ,
      ∃ models : ∀ q : ℕ, 1 ≤ q → InnerBufferLocalizedData (B.modelBuffer q T B₀) C₀ K₀,
        0 < C₀ ∧ 0 < K₀ ∧ 0 < B₀ ∧ 8 ≤ T ∧ selectedFirstInnerModelWindow ≤ T ∧
        sqrt centralOscillatorA + 2 ≤ T ∧
        (∀ j : ℝ, 2 ≤ j → 2 * C₀ * centralRadiusA ≤ centralBufferMass j T) ∧
        (∀ q : ℕ, 1 ≤ q → BufferHypotheses (B.modelBuffer q T B₀)) ∧
        (∀ q : ℕ, ∀ hq : 1 ≤ q, ∀ i,
          0 < fixedCentralModelCutEnergy (models q hq) i ∧
          ((models q hq).column i).inwardEnergy ≤
            2 * fixedCentralModelCutEnergy (models q hq) i) ∧
        (∀ q : ℕ, ∀ hq : 1 ≤ q, ∀ i,
          (sqrt 12 * (centralRadiusWeightConstant * (1 + T)) + 1) *
            (innerBufferRemainderEnvelope (B.modelBuffer q T B₀) C₀ K₀ i /
              sqrt (fixedCentralModelCutEnergy (models q hq) i)) ≤
                1 / (2 * (q : ℝ))) ∧
        (∀ q : ℕ, ∀ hq : 1 ≤ q, ∀ height : ℝ, 0 < height → ∀ sign : Bool,
          ‖innerTwoCutWeightedError
            (innerPhysicalCutKappa height
              (fun i => centralDensityRoot (bufferCut (B.modelBuffer q T B₀) i))
              (fixedCentralModelCutEnergy (models q hq)))
            (fun _ => 1)
            ((models q hq).physicalFluxError height
              (fun i => centralDensityRoot (bufferCut (B.modelBuffer q T B₀) i))) sign‖ ≤
                (1 : ℝ) / 8) ∧
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
            RadialConstructionGeometry Γ.reference ∧ R11aRetainedCoordinates P Γ ∧
            IsRadialReference Γ.reference ∧
            ∃ Cκ : ℝ, 0 < Cκ ∧
            ∀ j : ℕ, 2 ≤ j → Even j →
              ∃ n : ℕ, radialFrequencyBand S.chain S.Cstar n j ∧
                ∃ W : TerminalRegionalData Γ.reference,
                ∃ G : RadialModePair Γ.reference →L[ℝ] RadialModePair Γ.reference,
                  ActualMatchedRepresentation Γ.reference G W.matching ∧
                  ModeInverseProperties Γ.reference j G ∧
                  W.matching.frequency = j ∧ W.matching.transitionIndex = n ∧
                  W.matching.innerLeft = P.sideRadius false * S.joinInner false n ∧
                  W.matching.innerRight = P.sideRadius true * S.joinInner true n ∧
                  W.matching.sourceOuter = modeOuterSource Γ.reference
                    (P.sideRadius false * S.joinInner false n)
                    (P.sideRadius true * S.joinInner true n) ∧
                  4 / W.matching.margin + 1 ≤
                    Cκ * exp (radialQ W.matching.transitionIndex) ∧
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
  obtain ⟨hR06, hR09⟩ := r11a_closed_regional_inputs
  obtain ⟨B, C₀, K₀, B₀, T, models, hC₀, hK₀, hB₀, hT, hwindow, hcap,
      hfar, hbuffers, henergy, hrem, herror,
      CM, KM, Cstar, requested, S, metadata, hCM, hKM, hCstar, hindex, hmodels,
      η, Kfirst, ε, H, K, P, Γ, hη, hη48, hKfirst, hε, hsmall, hH,
      hselected, hhead, hreal, hw, hphi, hcentralLeft, hcentralRight,
      hTL, hTR, hcolumn, hcentral, hcentralHeight, hconstruction,
      hcoordinates, Cκ, hCκ, hfamily⟩ :=
    r11a_exists_quantitative_geometry_family hR06 hR09
  have hreference : IsRadialReference Γ.reference := by
    have hj (q : ℕ) : 2 ≤ 2 * (q + 1) := by omega
    have heven (q : ℕ) : Even (2 * (q + 1)) := ⟨q + 1, by omega⟩
    choose n hband W G hactual hmode hfrequency htransition hleft hright hsource
      hmargin v hv hAB hcases using fun q => hfamily (2 * (q + 1)) (hj q) (heven q)
    let D₀ := S.family S.sigma
    let D := Γ.reference
    have hD : IsAccumulatingProfile D := hreal.2.1
    have hborder : RadialTrueBorder D := hreal.2.2.1
    let hP : RadialPartition D := hD.choose_spec.2.1
    let M : ℕ → RadialMatchingData D := fun q => (W q).matching
    have hj' (q : ℕ) : 2 ≤ (M q).frequency := by
      simpa only [M, hfrequency q] using hj q
    have heven' (q : ℕ) : Even (M q).frequency := by
      simpa only [M, hfrequency q] using heven q
    have hband' (q : ℕ) :
        radialFrequencyBand S.chain S.Cstar (M q).transitionIndex (M q).frequency := by
      simpa only [M, htransition q, hfrequency q] using hband q
    have hleft' (q : ℕ) : (M q).innerLeft =
        P.sideRadius false * S.joinInner false (M q).transitionIndex := by
      simpa only [M, htransition q] using hleft q
    have hright' (q : ℕ) : (M q).innerRight =
        P.sideRadius true * S.joinInner true (M q).transitionIndex := by
      simpa only [M, htransition q] using hright q
    have hsource' (q : ℕ) : (M q).sourceOuter =
        modeOuterSource D (M q).innerLeft (M q).innerRight := by
      simpa only [M, hleft q, hright q] using hsource q
    let vscaled : ℕ → Bool → ℝ → ℝ := fun q side =>
      radialRadiusScale (P.sideRadius side) 1 (v q side)
    have hvsmooth (q : ℕ) (side : Bool) : ContDiff ℝ ∞ (vscaled q side) :=
      (hv q side).2.2.1
    have hvnatural (q : ℕ) (side : Bool) :
        RadialNaturalTail D side (M q).frequency
          (if side then (M q).innerRight else (M q).innerLeft) (vscaled q side) := by
      cases side
      · simpa only [M, hfrequency q, hleft q, Bool.false_eq_true, ite_false]
          using (hv q false).2.2.2
      · simpa only [M, hfrequency q, hright q, eq_self_iff_true, ite_true]
          using (hv q true).2.2.2
    have hAB' (q : ℕ) (side : Bool) :
        (M q).A (if side then 1 else 0) (if side then 1 else 0) =
          (outerUnitState (selectedBoundaryState D (M q).frequency (r07OutwardSign side)
            (if side then (M q).innerRight else (M q).innerLeft) (vscaled q side))).1 ∧
        (M q).B (if side then 1 else 0) (if side then 1 else 0) =
          (outerUnitState (selectedBoundaryState D (M q).frequency (r07OutwardSign side)
            (if side then (M q).innerRight else (M q).innerLeft) (vscaled q side))).2 := by
      cases side
      · simpa only [M, hfrequency q, hleft q, selectedTerminalSide, Bool.false_eq_true,
          ite_false, ↓reduceIte] using hAB q 0
      · simpa only [M, hfrequency q, hright q, selectedTerminalSide,
          show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte] using hAB q 1
    obtain ⟨CO, aO, CPO, bO, hCO, haO, hCPO, hbO, houter, hPo⟩ :=
      P.exists_uniform_selectedOuter_matching_bounds metadata Γ hD hborder hP hw
        hcoordinates W G hactual hj' heven' hband' hleft' hright' hsource'
        vscaled hvsmooth hvnatural hAB'

    have hlater (q : ℕ) (hq : S.chain.index < (W q).matching.transitionIndex) :
        (W q).cutoff = (fun i => P.laterTerminalCutoff metadata.geometry
          (W q).matching.transitionIndex (selectedTerminalSide i)) ∧
        (W q).standIn = (fun i => radialRadiusScale (P.sideRadius (selectedTerminalSide i)) 1
          (S.incoming (selectedTerminalSide i) (W q).matching.frequency)) ∧
        (W q).sourceCost =
          radialE (W q).matching.transitionIndex ^ terminalMorseRelativeSourceExponent ∧
        ∀ i, (W q).attenuation i = terminalMatchingAction S.chain
          ((W q).matching.transitionIndex - 1) (W q).matching.frequency / 100000000 := by
      rcases hcases q with hfirst | hlater
      · have hq' : S.chain.index < n q := by simpa only [htransition q] using hq
        exact False.elim ((ne_of_gt hq') hfirst.1)
      · rcases hlater with ⟨_, hcut, hstand, _, hsource, _, _, hatt⟩
        refine ⟨?_, ?_, ?_, ?_⟩
        · simpa only [htransition q] using hcut
        · simpa only [hfrequency q] using hstand
        · simpa only [htransition q] using hsource
        · simpa only [htransition q, hfrequency q] using hatt
    obtain ⟨CI, aI, CPI, bI, hCI, haI, hCPI, hbI, hinner, hPi⟩ :=
      P.exists_uniform_selectedInner_matching_bounds
        metadata Γ hreal hP hw zero_lt_one hT
        hcentralLeft hcentralRight hTL hTR B hcap hcolumn hwindow hcentral
        hC₀ hCM (by simpa only [metadata.cstar] using hCstar) hindex
        models hbuffers henergy hrem
        (fun q hq sign => herror q hq 1 zero_lt_one sign)
        hmodels hcoordinates W G hactual hfrequency hband' hleft' hright' hlater

    obtain ⟨e, floor, hfloorPos, hlabels, hfloor, hcells, hlocalizer,
      hleftDilation, hrightDilation, hfibers, ha, hb⟩ := hcoordinates
    have hfloor' : D.cellIndex = fun m => max (D₀.cellIndex m) floor := by
      simpa only [D₀, hlabels] using hfloor
    exact n05_isRadialReference_of_regional_envelopes hD hborder hconstruction G M hactual
      hfrequency floor (2 * floor + 3) hfloor'
      (fun n => (hfibers n).1) (fun n => (hfibers n).2)
      hCI hCO hCPI hCPO hCκ haI haO hbI hbO hinner houter hPi hPo hmargin
  exact ⟨B, C₀, K₀, B₀, T, models, hC₀, hK₀, hB₀, hT, hwindow, hcap,
    hfar, hbuffers, henergy, hrem, herror,
    CM, KM, Cstar, requested, S, metadata, hCM, hKM, hCstar, hindex, hmodels,
    η, Kfirst, ε, H, K, P, Γ, hη, hη48, hKfirst, hε, hsmall, hH,
    hselected, hhead, hreal, hw, hphi, hcentralLeft, hcentralRight,
    hTL, hTR, hcolumn, hcentral, hcentralHeight, hconstruction,
    hcoordinates, hreference, Cκ, hCκ, hfamily⟩

end ContinuousFlexibility.Radial

open Lean in
run_cmd do
  let axioms ← collectAxioms
    ``ContinuousFlexibility.Radial.n05_exists_retained_radial_reference
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in n05_exists_retained_radial_reference"

#print axioms ContinuousFlexibility.Radial.n05_exists_retained_radial_reference
