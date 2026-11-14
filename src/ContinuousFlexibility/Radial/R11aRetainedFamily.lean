module

public import ContinuousFlexibility.Radial.R11aGeometryCellIndex
public import ContinuousFlexibility.Radial.R10aRegionalConstruction
public import ContinuousFlexibility.Radial.MatchedFixedCentralChoices
public import ContinuousFlexibility.Radial.MatchedSelectedMargin
public import ContinuousFlexibility.Radial.MatchedTerminalCompletion

/-!
# One quantitative family from the actual closed regional construction

The true central localized models and their frequency-normalized
remainders are chosen first. The original regional factory then chooses
the selected family, finite first-band cost and retained length in its
proved order. Its same reference carries the canonical index floor,
localizer pullback, natural boundary lines and actual terminal cutoffs
at every even frequency. The original Poisson and matrix completion
supplies the same actual matching representation and modal inverse.
No weighted inverse estimate is assumed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open scoped Topology ContDiff Matrix.Norms.L2Operator
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint

/-- Exact identities of the constructed reference. The cell saturation is
recorded as inclusion; every localizer keeps its original pullback. -/
def R11aRetainedCoordinates {S : SelectedTailData} {K : SeedCentralCutoff}
    {q length : ℝ} (P : SeedRetainedPair S K q length)
    (Γ : ConnectedReferenceGeometry) : Prop :=
  ∃ e : ℝ ≃o ℝ, ∃ N : ℕ, 1 ≤ N ∧
    (S.family S.sigma).cellIndex =
      morseTwoTailAt S.chain.index (fun _ k => S.chain.index + k) ∧
    Γ.reference.cellIndex = (fun m =>
      max (morseTwoTailAt S.chain.index (fun _ k => S.chain.index + k) m) N) ∧
    (∀ m, e ⁻¹' (S.family S.sigma).cells m ⊆ Γ.reference.cells m) ∧
    Γ.reference.localizer = (fun m r => (S.family S.sigma).localizer m (e r)) ∧
    (∀ r ≤ S.entry false S.chain.index, e.symm r = P.pair.radiusL * r) ∧
    (∀ r, S.entry true S.chain.index ≤ r → e.symm r = P.pair.radiusR * r) ∧
    (∀ n : ℕ, Set.Finite {m | Γ.reference.cellIndex m = n} ∧
      Set.ncard {m | Γ.reference.cellIndex m = n} ≤ 2 * N + 3) ∧
    Γ.reference.a = P.pair.radiusL * (S.family S.sigma).a ∧
    Γ.reference.b = P.pair.radiusR * (S.family S.sigma).b

theorem r11a_geometrySupply_with_coordinates (hR06 : R06Statement) :
    R10aGeometrySupplyWith
      (fun {_S _K _q _length} P Γ => R11aRetainedCoordinates P Γ) := by
  intro B C hC requested
  obtain ⟨S, metadata, hrealize⟩ :=
    r11a_exists_parameterized_geometry_with_construction_geometry hR06 B C hC requested
  refine ⟨S, metadata, ?_⟩
  intro T q length hT hq hlength
  obtain ⟨K, P, Γ, e, N, hN, hselected, hhead, hreal, hconstruction, hlabels, hindex,
      hcells, hlocalizer, hleftDilation, hrightDilation, hfibers, hw, hphi,
      hleft, hright, hTL, hTR, hcolumn, hcentral, hcentralHeight, ha, hb⟩ :=
    hrealize T q length hT hq hlength
  exact ⟨K, P, Γ, hselected, hhead, hreal, hw, hphi, hleft, hright, hTL, hTR,
    hcolumn, hcentral, hcentralHeight, hconstruction,
    e, N, hN, hlabels, hindex, hcells, hlocalizer, hleftDilation, hrightDilation, hfibers, ha, hb⟩

/-- Complete retained data for the same actual geometry and central model
family. The displayed local estimates precede the reference and every mode. -/
theorem r11a_exists_quantitative_geometry_family (hR06 : R06Statement) (hR09 : R09Statement) :
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
  obtain ⟨B⟩ := exists_fixedCentralBorder
  obtain ⟨C₀, K₀, B₀, T, hC₀, hK₀, hB₀, hT, hwindow, hcap, hfar,
      models, hbuffers, henergy, hrem, herror⟩ :=
    B.exists_frequency_normalized_model_buffers hR09 selectedFirstInnerModelWindow
  refine ⟨B, C₀, K₀, B₀, T, models, hC₀, hK₀, hB₀, hT, hwindow, hcap,
    hfar, hbuffers, henergy, hrem, herror, ?_⟩
  obtain ⟨CM, KM, Cstar, N, S, metadata, hCM, hKM, hCstar, hindex, hmodels,
      η, Kfirst, ε, H, K, P, Γ, hη, hη48, hKfirst, hε, hsmall, hH,
      hselected, hhead, hreal, hw, hphi, hleft, hright, hTL, hTR, hcolumn,
      hcentral, hcentralHeight, hconstruction, hcoordinates, hfamily⟩ :=
    r10aRegionalConstruction_with_geometry
      (fun {_S _K _q _length} P Γ => R11aRetainedCoordinates P Γ) hR09 B
      hC₀ hK₀ hB₀ hT hwindow hcap hbuffers models henergy
      (fun q hq sign => herror q hq 1 zero_lt_one sign)
      (r11a_geometrySupply_with_coordinates hR06)
  refine ⟨CM, KM, Cstar, N, S, metadata, hCM, hKM, hCstar, hindex, hmodels,
    η, Kfirst, ε, H, K, P, Γ, hη, hη48, hKfirst, hε, hsmall, hH,
    hselected, hhead, hreal, hw, hphi, hleft, hright, hTL, hTR, hcolumn,
    hcentral, hcentralHeight, hconstruction, hcoordinates,
    matchedSelectedMarginConstant η S.Cstar,
    matchedSelectedMarginConstant_pos hη metadata.selected.1.le, ?_⟩
  intro j hj heven
  obtain ⟨n, hband, W, hfrequency, htransition, hinnerLeft, hinnerRight,
      hsource, v, hv, hAB, hcases⟩ := hfamily j hj heven
  obtain ⟨Pcol, pcol, Db, Kinv, G, hactual, hmode⟩ :=
    W.exists_completed_actual hreal.2.1 hreal.2.2.1
  let R : TerminalRegionalData Γ.reference :=
    { W with matching :=
        { W.matching with innerPoisson := Pcol, innerFunction := pcol, Db := Db, Kinv := Kinv } }
  have hmode' : ModeInverseProperties Γ.reference j G := by
    simpa only [hfrequency] using hmode
  refine ⟨n, hband, R, G, hactual, hmode', hfrequency, htransition, hinnerLeft, hinnerRight,
    hsource, ?_, v, hv, hAB, hcases⟩
  change 4 / W.matching.margin + 1 ≤
    matchedSelectedMarginConstant η S.Cstar * exp (radialQ W.matching.transitionIndex)
  rw [htransition]
  apply matchedSelectedMargin_bound hη metadata.selected.1.le n
  rcases hcases with hfirst | hlater
  · exact Or.inl hfirst.2.1
  · exact Or.inr hlater.2.2.2.1

end ContinuousFlexibility.Radial
