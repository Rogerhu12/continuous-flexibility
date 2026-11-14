module

public import ContinuousFlexibility.Radial.SelectedLaterTerminalData
public import ContinuousFlexibility.Radial.RetainedLaterFrozenInverse

/-!
# Later regional data from the actual localized-model factory

The model supplier has the same order of quantifiers as the monotone
Morse compression choice: every earlier cell supplies one localized
model with its own remainder and both oriented error estimates. The
finite model family and the even-frequency reindexing are performed
here, before constructing the actual inner and outer regional data.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set MeasureTheory
open scoped ContDiff Matrix.Norms.L2Operator
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint

theorem SeedRetainedPair.exists_later_terminalRegionalData_with_data
    {C : ℝ} {requested : ℕ} {S : SelectedTailData}
    {K : SeedCentralCutoff} {q length : ℝ} (P : SeedRetainedPair S K q length)
    (metadata : R10aSelectedMetadata C requested S) (hq : 0 < q)
    (B : FixedCentralBorder) {Γ : ConnectedReferenceGeometry} (hΓ : Γ.Realizes)
    (hw : Γ.reference.w = P.pair.profile)
    (hleft : Γ.centralLeft = exp K.left) (hright : Γ.centralRight = exp K.right)
    {T B₀ C₀ K₀ CM KM : ℝ} (hT : 8 ≤ T)
    (hcap : sqrt centralOscillatorA + 2 ≤ T)
    (hC₀ : 0 < C₀) (hK₀ : 0 ≤ K₀) (hCM : 0 < CM)
    (hTL : Γ.centralLeft < centralRadius (-T)) (hTR : centralRadius T < Γ.centralRight)
    (hmodel : EqOn Γ.reference.w (centralRadialProfile 1) (Ioo Γ.centralLeft Γ.centralRight))
    (hwindow : ∀ r, 0 < r → (r ≤ centralRadius (-T) ∨ centralRadius T ≤ r) →
      (3 / 4 : ℝ) ≤ r * deriv (centralRadialProfile 1) r / centralRadialProfile 1 r)
    (hcolumn : referenceColumn Γ.reference = fixedCentralColumn B.chi)
    (initial : ℕ)
    (hstart : fixedCentralLaterBudgetStart T B₀ C₀ K₀ CM S.Cstar
      hC₀.le hCM.le metadata.selected.1.le initial ≤ S.chain.index)
    (hN : 4096 ≤ S.chain.index) (hC : 1000 ≤ S.Cstar)
    {n j : ℕ} (hn : S.chain.index < n) (hj : 2 ≤ j) (heven : Even j)
    (hband : radialFrequencyBand S.chain S.Cstar n j)
    (hbudget : 1000000000 ≤ terminalMatchingAction S.chain (n - 1) j ∧
      (radialE n ^ terminalMorseEnergyErrorExponent + radialE n ^ (38 : ℝ) *
        (radialE n ^ terminalMorseRelativeSourceExponent) ^ (2 : ℕ)) *
        exp (-(terminalMatchingAction S.chain (n - 1) j / 100000000) -
          terminalMatchingAction S.chain (n - 1) j / 100000000) ≤
        ((r07UniformTolerance S.Cstar * exp (-(n : ℝ) ^ 2)) / 8) / 16)
    (hB₀ : BufferHypotheses (B.modelBuffer (j / 2) T B₀))
    (M₀ : InnerBufferLocalizedData (B.modelBuffer (j / 2) T B₀) C₀ K₀)
    (henergy : ∀ i, 0 < fixedCentralModelCutEnergy M₀ i ∧
      (M₀.column i).inwardEnergy ≤ 2 * fixedCentralModelCutEnergy M₀ i)
    (herror₀ : ∀ sign : Bool,
      ‖innerTwoCutWeightedError (fixedCentralModelPhysicalKappa M₀) (fun _ => 1)
        (M₀.physicalFluxError 1
          (fun i => centralDensityRoot (bufferCut (B.modelBuffer (j / 2) T B₀) i))) sign‖ ≤
        (1 : ℝ) / 8)
    (hMorse : ∀ m : ℕ, S.chain.index ≤ m → m < n →
      BufferHypotheses
        (innerMorseBufferData (morseChainA S.chain m) (morseChainB S.chain m) (j : ℝ)
          (8 * (S.chain.d m : ℝ) ^ 9)) ∧
      ∃ M : InnerBufferLocalizedData
        (innerMorseBufferData (morseChainA S.chain m) (morseChainB S.chain m) (j : ℝ)
          (8 * (S.chain.d m : ℝ) ^ 9)) CM KM,
        (∀ i, innerMorseModelNormalizedRemainder M i ≤ 1 / (j : ℝ)) ∧
        ∀ side : Bool, ∀ height : ℝ, 0 < height → ∀ sign : Bool,
          ‖innerTwoCutWeightedError
            (innerPhysicalCutKappa height (fun _ => 1) (fun i => (M.column i).inwardEnergy))
            (innerMorseCutWeight S.chain.index 0 0 side m)
            (M.physicalFluxError height (fun _ => 1)) sign‖ ≤ (1 : ℝ) / 8) :
    ∃ W : TerminalRegionalData Γ.reference,
      W.matching.frequency = j ∧ W.matching.transitionIndex = n ∧
      W.matching.innerLeft = P.sideRadius false * S.joinInner false n ∧
      W.matching.innerRight = P.sideRadius true * S.joinInner true n ∧
      W.cutoff = (fun i => P.laterTerminalCutoff metadata.geometry n (selectedTerminalSide i)) ∧
      W.standIn = (fun i => radialRadiusScale (P.sideRadius (selectedTerminalSide i)) 1
        (S.incoming (selectedTerminalSide i) j)) ∧
      W.matching.margin = r07UniformTolerance S.Cstar * exp (-(n : ℝ) ^ 2) / 8 ∧
      W.sourceCost = radialE n ^ terminalMorseRelativeSourceExponent ∧
      W.energyCost = radialE n ^ terminalMorseEnergyErrorExponent ∧
      W.inverseCost = radialE n ^ (38 : ℝ) ∧
      (∀ i, W.attenuation i = terminalMatchingAction S.chain (n - 1) j / 100000000) ∧
      W.matching.sourceOuter = modeOuterSource Γ.reference
        (P.sideRadius false * S.joinInner false n) (P.sideRadius true * S.joinInner true n) ∧
      ∃ v : Bool → ℝ → ℝ,
        (∀ side, ContDiff ℝ ∞ (v side) ∧
          EqOn (v side) (S.outgoing side j)
            (radialTailInterval (S.family S.sigma) side (S.entry side n)) ∧
          ContDiff ℝ ∞ (radialRadiusScale (P.sideRadius side) 1 (v side)) ∧
          RadialNaturalTail Γ.reference side j (P.sideRadius side * S.joinInner side n)
            (radialRadiusScale (P.sideRadius side) 1 (v side))) ∧
        ∀ i : Fin 2,
          W.matching.A i i =
            (outerUnitState (selectedBoundaryState Γ.reference j
              (r07OutwardSign (selectedTerminalSide i))
              (P.sideRadius (selectedTerminalSide i) * S.joinInner (selectedTerminalSide i) n)
              (radialRadiusScale (P.sideRadius (selectedTerminalSide i)) 1
                (v (selectedTerminalSide i))))).1 ∧
          W.matching.B i i =
            (outerUnitState (selectedBoundaryState Γ.reference j
              (r07OutwardSign (selectedTerminalSide i))
              (P.sideRadius (selectedTerminalSide i) * S.joinInner (selectedTerminalSide i) n)
              (radialRadiusScale (P.sideRadius (selectedTerminalSide i)) 1
                (v (selectedTerminalSide i))))).2 := by
  classical
  let k := n - S.chain.index
  let qf := j / 2
  have hk : 0 < k := Nat.sub_pos_of_lt hn
  have hnk : S.chain.index + k = n := Nat.add_sub_of_le hn.le
  have hqf : 1 ≤ qf := (even_frequency_half hj heven).1
  have hjf : j = 2 * qf := (even_frequency_half hj heven).2
  have hjreal : (j : ℝ) = 2 * (qf : ℝ) := by exact_mod_cast hjf
  have hband' : radialFrequencyBand S.chain S.Cstar (S.chain.index + k) (2 * qf) := by
    rw [hnk, ← hjf]
    exact hband
  have hraw (side : Bool) (p : Fin k) :
      let m := innerMorseInnerTailIndex S.chain.index k side p
      BufferHypotheses
        (innerMorseBufferData (morseChainA S.chain m) (morseChainB S.chain m)
          (2 * (qf : ℝ)) (8 * (S.chain.d m : ℝ) ^ 9)) ∧
      ∃ M : InnerBufferLocalizedData
        (innerMorseBufferData (morseChainA S.chain m) (morseChainB S.chain m)
          (2 * (qf : ℝ)) (8 * (S.chain.d m : ℝ) ^ 9)) CM KM,
        (∀ i, innerMorseModelNormalizedRemainder M i ≤ 1 / (2 * (qf : ℝ))) ∧
        ∀ height : ℝ, 0 < height → ∀ sign : Bool,
          ‖innerTwoCutWeightedError
            (innerPhysicalCutKappa height (fun _ => 1) (fun i => (M.column i).inwardEnergy))
            (innerMorseCutWeight S.chain.index 0 0 side m)
            (M.physicalFluxError height (fun _ => 1)) sign‖ ≤ (1 : ℝ) / 8 := by
    have hm := innerMorseInnerTailIndex_bounds S.chain.index k side p
    have hmn : innerMorseInnerTailIndex S.chain.index k side p < n := hm.2.trans_eq hnk
    have hh := hMorse (innerMorseInnerTailIndex S.chain.index k side p) hm.1 hmn
    rw [hjreal] at hh
    obtain ⟨hbuf, M, hrem, herr⟩ := hh
    exact ⟨hbuf, M, hrem, herr side⟩
  have hB (side : Bool) (p : Fin k) := (hraw side p).1
  choose models hrem herror using fun (side : Bool) (p : Fin k) => (hraw side p).2
  apply P.exists_later_terminalData_of_supplies_with_data metadata hq hΓ hw hleft hright
    hC hn hj heven hband hbudget
  intro margin slope boundary
  let M := selectedTerminalMatching Γ.reference j n margin
    (fun side => P.sideRadius side * S.joinInner side n) slope boundary
  obtain ⟨A, u, hnorm, _, hsolve, hunique, hrep⟩ :=
    P.exists_later_inner_inverse metadata.selected metadata.geometry metadata.first_two hq
      metadata.initial_bridge_positive metadata.later_join B hΓ hw hleft hright hT hcap
      hC₀ hK₀ hCM metadata.selected.1.le hTL hTR hmodel hwindow hcolumn initial hstart hN
      k hk qf hqf hband' hB₀ M₀ henergy herror₀ hB models hrem herror
      M hjf (by rw [hnk]; rfl) (by rw [hnk]; rfl) rfl
  refine ⟨A, u, ?_, hsolve, hunique, hrep⟩
  simpa only [hnk] using hnorm

/-- The original interface projects the retained construction to its cuts. -/
theorem SeedRetainedPair.exists_later_terminalRegionalData
    {C : ℝ} {requested : ℕ} {S : SelectedTailData}
    {K : SeedCentralCutoff} {q length : ℝ} (P : SeedRetainedPair S K q length)
    (metadata : R10aSelectedMetadata C requested S) (hq : 0 < q)
    (B : FixedCentralBorder) {Γ : ConnectedReferenceGeometry} (hΓ : Γ.Realizes)
    (hw : Γ.reference.w = P.pair.profile)
    (hleft : Γ.centralLeft = exp K.left) (hright : Γ.centralRight = exp K.right)
    {T B₀ C₀ K₀ CM KM : ℝ} (hT : 8 ≤ T)
    (hcap : sqrt centralOscillatorA + 2 ≤ T)
    (hC₀ : 0 < C₀) (hK₀ : 0 ≤ K₀) (hCM : 0 < CM)
    (hTL : Γ.centralLeft < centralRadius (-T)) (hTR : centralRadius T < Γ.centralRight)
    (hmodel : EqOn Γ.reference.w (centralRadialProfile 1) (Ioo Γ.centralLeft Γ.centralRight))
    (hwindow : ∀ r, 0 < r → (r ≤ centralRadius (-T) ∨ centralRadius T ≤ r) →
      (3 / 4 : ℝ) ≤ r * deriv (centralRadialProfile 1) r / centralRadialProfile 1 r)
    (hcolumn : referenceColumn Γ.reference = fixedCentralColumn B.chi)
    (initial : ℕ)
    (hstart : fixedCentralLaterBudgetStart T B₀ C₀ K₀ CM S.Cstar
      hC₀.le hCM.le metadata.selected.1.le initial ≤ S.chain.index)
    (hN : 4096 ≤ S.chain.index) (hC : 1000 ≤ S.Cstar)
    {n j : ℕ} (hn : S.chain.index < n) (hj : 2 ≤ j) (heven : Even j)
    (hband : radialFrequencyBand S.chain S.Cstar n j)
    (hbudget : 1000000000 ≤ terminalMatchingAction S.chain (n - 1) j ∧
      (radialE n ^ terminalMorseEnergyErrorExponent + radialE n ^ (38 : ℝ) *
        (radialE n ^ terminalMorseRelativeSourceExponent) ^ (2 : ℕ)) *
        exp (-(terminalMatchingAction S.chain (n - 1) j / 100000000) -
          terminalMatchingAction S.chain (n - 1) j / 100000000) ≤
        ((r07UniformTolerance S.Cstar * exp (-(n : ℝ) ^ 2)) / 8) / 16)
    (hB₀ : BufferHypotheses (B.modelBuffer (j / 2) T B₀))
    (M₀ : InnerBufferLocalizedData (B.modelBuffer (j / 2) T B₀) C₀ K₀)
    (henergy : ∀ i, 0 < fixedCentralModelCutEnergy M₀ i ∧
      (M₀.column i).inwardEnergy ≤ 2 * fixedCentralModelCutEnergy M₀ i)
    (herror₀ : ∀ sign : Bool,
      ‖innerTwoCutWeightedError (fixedCentralModelPhysicalKappa M₀) (fun _ => 1)
        (M₀.physicalFluxError 1
          (fun i => centralDensityRoot (bufferCut (B.modelBuffer (j / 2) T B₀) i))) sign‖ ≤
        (1 : ℝ) / 8)
    (hMorse : ∀ m : ℕ, S.chain.index ≤ m → m < n →
      BufferHypotheses
        (innerMorseBufferData (morseChainA S.chain m) (morseChainB S.chain m) (j : ℝ)
          (8 * (S.chain.d m : ℝ) ^ 9)) ∧
      ∃ M : InnerBufferLocalizedData
        (innerMorseBufferData (morseChainA S.chain m) (morseChainB S.chain m) (j : ℝ)
          (8 * (S.chain.d m : ℝ) ^ 9)) CM KM,
        (∀ i, innerMorseModelNormalizedRemainder M i ≤ 1 / (j : ℝ)) ∧
        ∀ side : Bool, ∀ height : ℝ, 0 < height → ∀ sign : Bool,
          ‖innerTwoCutWeightedError
            (innerPhysicalCutKappa height (fun _ => 1) (fun i => (M.column i).inwardEnergy))
            (innerMorseCutWeight S.chain.index 0 0 side m)
            (M.physicalFluxError height (fun _ => 1)) sign‖ ≤ (1 : ℝ) / 8) :
    ∃ W : TerminalRegionalData Γ.reference,
      W.matching.frequency = j ∧ W.matching.transitionIndex = n ∧
      W.matching.innerLeft = P.sideRadius false * S.joinInner false n ∧
      W.matching.innerRight = P.sideRadius true * S.joinInner true n := by
  obtain ⟨W, hfreq, hindex, hcutL, hcutR, _⟩ :=
    P.exists_later_terminalRegionalData_with_data metadata hq B hΓ hw hleft hright hT
      hcap hC₀ hK₀ hCM hTL hTR hmodel hwindow hcolumn initial hstart hN hC hn hj heven
      hband hbudget hB₀ M₀ henergy herror₀ hMorse
  exact ⟨W, hfreq, hindex, hcutL, hcutR⟩

end ContinuousFlexibility.Radial
