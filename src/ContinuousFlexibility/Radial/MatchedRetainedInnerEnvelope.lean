module

public import ContinuousFlexibility.Radial.MatchedRetainedFamilyInnerWeightData
public import ContinuousFlexibility.Radial.MatchedRetainedTerminalCapWeights
public import ContinuousFlexibility.Radial.MatchedRetainedLocalizerWeights
public import ContinuousFlexibility.Radial.MatchedSelectedTerminalTwoWeights
public import ContinuousFlexibility.Radial.MatchedMorseInnerWeightTransfer
public import ContinuousFlexibility.Radial.MatchedInnerSupportedCells
public import ContinuousFlexibility.Radial.MatchedSupportedColumnCells
public import ContinuousFlexibility.Radial.ReferenceRawKernelSchur

/-!
# Both actual later inner envelopes from the same finite chain

The local signed inverse estimate is transported to the original
matching inverse. Its two external columns use the original terminal
leading functions and residuals between those same two weights.
Actual localizers then give the canonical channel estimates.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff

namespace SeedRetainedPair

variable {S : SelectedTailData} {K₀ : SeedCentralCutoff}
  {headLength length T Cstar : ℝ} {requested : ℕ}
  (P : SeedRetainedPair S K₀ headLength length)
  (metadata : R10aSelectedMetadata Cstar requested S)
  {Γ : ConnectedReferenceGeometry} (hΓ : Γ.Realizes)
  (hw : Γ.reference.w = P.pair.profile) (hhead : 0 < headLength) (hT : 0 < T)
  (hleft : Γ.centralLeft = exp K₀.left) (hright : Γ.centralRight = exp K₀.right)
  (hTL : Γ.centralLeft < centralRadius (-T)) (hTR : centralRadius T < Γ.centralRight)
  (Bfixed : FixedCentralBorder) (hcapT : sqrt centralOscillatorA + 2 ≤ T)
  (hcolumn : referenceColumn Γ.reference = fixedCentralColumn Bfixed.chi)
  (hCstar : 1000 ≤ S.Cstar)
  (k : ℕ) (hk : 0 < k)
  (hN : 4096 ≤ S.chain.index)
  (e : ℝ ≃o ℝ)
  (he : ∀ side x, (if side then morseChainSeam S.chain true S.chain.index ≤ x
    else x ≤ morseChainSeam S.chain false S.chain.index) →
      e.symm x = P.sideRadius side * x)
  (hχ : ∀ m x, Γ.reference.localizer m x = (S.family S.sigma).localizer m (e x))
  {J : ℕ} (hJ : S.chain.index ≤ J)
  (hwindow : ∀ m, (S.family S.sigma).cellIndex m ≤ S.chain.index →
    ∀ x, (S.family S.sigma).localizer m x ≠ 0 →
      x ∈ Icc (morseChainSeam S.chain false J) (morseChainSeam S.chain true J))
  (R : TerminalRegionalData Γ.reference)
  (hM : MatchingLocalRealizations Γ.reference R.matching)
  (hML : R.matching.innerLeft = P.sideRadius false * S.joinInner false (S.chain.index + k))
  (hMR : R.matching.innerRight = P.sideRadius true * S.joinInner true (S.chain.index + k))
  (hj : 2 ≤ R.matching.frequency) (heven : Even R.matching.frequency)
  (hband : radialFrequencyBand S.chain S.Cstar (S.chain.index + k) R.matching.frequency)
  (hcutoff : R.cutoff = fun i =>
    P.laterTerminalCutoff metadata.geometry (S.chain.index + k) (selectedTerminalSide i))
  (hstandIn : R.standIn = fun i =>
    radialRadiusScale (P.sideRadius (selectedTerminalSide i)) 1
      (S.incoming (selectedTerminalSide i) R.matching.frequency))
  (hsource : R.sourceCost = radialE (S.chain.index + k) ^ terminalMorseRelativeSourceExponent)
  (hattenuation : ∀ i, R.attenuation i =
    terminalMatchingAction S.chain (S.chain.index + k - 1) R.matching.frequency / 100000000)

local notation "hD" => matchingProfileGeometry (And.left (And.right hΓ))
local notation "H" => P.retainedMorseInnerGeometry hD hw metadata.selected metadata.geometry
  metadata.first_two hhead hT hleft hright hTL hTR k hk
local notation "column" => matchingBorderVector Γ.reference
  (And.left (And.right hΓ)) (And.left (And.right (And.right hΓ)))

variable {bordered : Bool} {frequency : ℝ}
  (C : InnerRadialActualChain Γ.reference
    (P.retainedMorseInnerGeometry (matchingProfileGeometry hΓ.2.1) hw metadata.selected
      metadata.geometry metadata.first_two hhead hT hleft hright hTL hTR k hk)
    bordered frequency (innerModelChainPiece (innerMorseInnerCenter k))
    (matchingBorderVector Γ.reference hΓ.2.1 hΓ.2.2.1))
  (hbool : bordered = decide (R.matching.frequency = 2))
  (hfreq : frequency = (R.matching.frequency : ℝ))
  (hS : IsUnit C.fluxMatrix)
  (CW : ℝ)
  (hCW : ∀ sign x, |matchedMorseSignedWeight S.chain.index k
    (P.retainedMorseInnerGeometry (matchingProfileGeometry hΓ.2.1) hw metadata.selected
      metadata.geometry metadata.first_two hhead hT hleft hright hTL hTR k hk)
    C.matchedWeightLeft C.matchedWeightRight sign x| ≤ CW)

local notation "l" => C.matchedWeightLeft
local notation "r" => C.matchedWeightRight
local notation "Wi" => matchedMorseSignedWeight S.chain.index k H l r
local notation "Wo" => matchedMorseLocalizedWeight S.chain.index k H l r
local notation "hWi" => matchedMorseSignedWeight_measurable S.chain.index k H l r
local notation "hWo" => matchedMorseLocalizedWeight_measurable S.chain.index k H l r
local notation "hi" => matchedMorseSignedWeight_pos S.chain.index k H l r
local notation "ho" => matchedMorseLocalizedWeight_pos S.chain.index k H l r
local notation "hOut" => matchedMorseLocalizedWeight_bound S.chain.index k H l r hCW
local notation "hOutInv" => matchedMorseLocalizedWeight_inv_bound S.chain.index k H l r hCW
local notation "Co" => matchedMorseLossInverseBound S.chain.index k * CW
local notation "hInInv" => fun sign x =>
  Eq.trans_le (congrArg abs (matchedMorseSignedWeight_inv S.chain.index k H l r sign x))
    (hCW (!sign) x)
local notation "Out" => fun sign => matchedModeActualWeight Γ.reference
  (Wo sign) (hWo sign) (ho sign) CW Co (hOut sign) (hOutInv sign)
local notation "In" => fun sign => matchedModeActualWeight Γ.reference
  (Wi sign) (hWi sign) (hi sign) CW CW (hCW sign) (hInInv sign)
local notation "level" => referenceRawChannelLevel (S.family S.sigma)
local notation "RC" => matchedMorseLocalizerWeightConstant S.chain.index J
local notation "aP" => matchedMorseTerminalColumnExponent 41414

include hN he hχ hJ hwindow Bfixed hcapT hcolumn hCstar hML hMR hj heven hband
  hcutoff hstandIn hsource hattenuation hbool hfreq

theorem retainedMorse_actual_inner_envelopes
    (hP : RadialPartition Γ.reference) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ sign : Bool,
      ‖innerSupportedWeightMultiplier (radialHilbertMeasure Γ.reference)
          (innerRadialChainRegion Γ.reference H) (innerRadialChainRegion_measurable Γ.reference H)
          bordered (Wo sign) (hWo sign) CW (hOut sign) ∘L C.inverse (hD).2.2.1.1 hS ∘L
        innerSupportedWeightMultiplier (radialHilbertMeasure Γ.reference)
          (innerRadialChainRegion Γ.reference H) (innerRadialChainRegion_measurable Γ.reference H)
          bordered (Wi (!sign)) (hWi (!sign)) CW (hCW (!sign))‖ ≤ B) :
    (∀ u v,
      ‖matchedModeChannel Γ.reference hP u ∘L R.matching.innerInverse ∘L
        matchingSourceInnerCLM Γ.reference R.matching hM ∘L
        matchedModeScalarGate Γ.reference (decide (R.matching.frequency = 2)) ∘L
          matchedModeChannel Γ.reference hP v‖ ≤
        (sqrt 2 * B) * RC ^ 2 * exp
          (41414 * (radialQ (level u) + radialQ (level v)) -
            |radialS (level u) - radialS (level v)|)) ∧
    (∀ u i, ‖matchedModeChannel Γ.reference hP u (R.matching.innerPoisson i)‖ ≤
      ((1 + sqrt 2 * B) * exp (radialS S.chain.index)) * RC * exp
        (aP * (radialQ (level u) + radialQ (S.chain.index + k)) -
          |radialS (level u) - radialS (S.chain.index + k)|)) := by
  have hends := P.retainedMorseInnerGeometry_outer hD hw metadata.selected metadata.geometry
    metadata.first_two hhead hT hleft hright hTL hTR k hk metadata.later_join
  have hL : R.matching.innerLeft = (H).left 0 := hML.trans hends.1.symm
  have hR : R.matching.innerRight = (H).right (Fin.last (2 * (2 * k + 1))) :=
    hMR.trans hends.2.symm
  have hsub : Icc R.matching.innerLeft R.matching.innerRight ⊆ radialCore Γ.reference := by
    intro x hx
    exact ⟨R.cut_order.1.trans_le hx.1, hx.2.trans_lt R.cut_order.2.2⟩
  have hcenter := P.retainedMorseInnerGeometry_center hD hw metadata.selected metadata.geometry
    metadata.first_two hhead hT hleft hright hTL hTR k hk
  have hcolfix : innerL2PieceProjection (radialHilbertMeasure Γ.reference)
      (Ioo ((H).left (innerModelChainPiece (innerMorseInnerCenter k)))
        ((H).right (innerModelChainPiece (innerMorseInnerCenter k)))) column = column := by
    apply innerL2PieceProjection_eq_self _ _ isOpen_Ioo.measurableSet
    have hs : Function.support (referenceColumn Γ.reference) ⊆
        Ioo ((H).left (innerModelChainPiece (innerMorseInnerCenter k)))
          ((H).right (innerModelChainPiece (innerMorseInnerCenter k))) := by
      rw [hcenter.1, hcenter.2, hcolumn]
      exact Bfixed.column_support_in_model hcapT
    filter_upwards [matchingBorderVector_coe hΓ.2.1 hΓ.2.2.1] with x hx
    intro hout
    have hz : referenceColumn Γ.reference x = 0 := by
      by_contra hne
      exact hout (hs hne)
    simp only [hx, matchingBorderTest, hz, zero_div]
  have hBop : 0 ≤ sqrt 2 * B := mul_nonneg (sqrt_nonneg 2) hB
  have hop (sign : Bool) :
      ‖(Out sign : RadialModePair Γ.reference →L[ℝ] RadialModePair Γ.reference) ∘L
          R.matching.innerInverse ∘L matchingSourceInnerCLM Γ.reference R.matching hM ∘L
          matchedModeScalarGate Γ.reference (decide (R.matching.frequency = 2)) ∘L
          ((In sign).symm : RadialModePair Γ.reference →L[ℝ] RadialModePair Γ.reference)‖ ≤
        sqrt 2 * B :=
    matchedInnerActualInverse_morse_loss_weighted hΓ.2.1 hΓ.2.2.1 (hD).2.2.1.1
      S.chain.index k H R.matching hM hL hR hsub
      (innerModelChainPiece (innerMorseInnerCenter k)) column rfl hcolfix C hbool hfreq hS
      l r CW hCW hB hbound sign
  have hlocal (sign : Bool) (m : ℕ) :
      ∀ᵐ x ∂radialHilbertMeasure Γ.reference, Γ.reference.localizer m x ≠ 0 →
        x ∈ Ioo R.matching.innerLeft R.matching.innerRight →
        |(Wo sign x)⁻¹| ≤ RC * exp
          (41414 * radialQ (level (m + 1)) -
            (if sign then radialS (level (m + 1)) else -radialS (level (m + 1)))) ∧
        |Wi sign x| ≤ RC * exp
          (41414 * radialQ (level (m + 1)) +
            (if sign then radialS (level (m + 1)) else -radialS (level (m + 1)))) := by
    have hs : |(if sign then (1 : ℝ) else -1)| ≤ 1 := by cases sign <;> norm_num
    have hh := P.retainedMorse_localizer_weight_ae hD hw metadata.selected metadata.geometry
      metadata.first_two hhead hT hleft hright hTL hTR k hk hN e he hχ hJ hwindow
      hΓ.2.1 l r hs m
    filter_upwards [hh] with x hx hχx hinner
    have hb := hx hχx (by simpa only [hL, hR] using hinner)
    cases sign <;> simpa only [matchedMorseLocalizedWeight, matchedMorseSignedWeight,
      referenceRawChannelLevel, Bool.false_eq_true, ite_false, ite_true,
      one_mul, neg_one_mul] using hb
  constructor
  · intro u v
    exact matchedInner_twoSign_supported_cell_envelope hΓ.2.1 hP R.matching hM level rfl
      Wo Wi hWo hWi ho hi (fun _ => CW) (fun _ => Co) (fun _ => CW) (fun _ => CW)
      hOut hOutInv hCW hInInv hBop (matchedMorseLocalizerWeightConstant_ge_one _ _)
      hop hlocal u v
  · have hweighted (sign : Bool) (i : Fin 2) :
        ‖Out sign (R.matching.innerPoisson i)‖ ≤
          ((1 + sqrt 2 * B) * exp (radialS S.chain.index)) *
            exp (aP * radialQ (S.chain.index + k) +
              (if sign then radialS (S.chain.index + k) else -radialS (S.chain.index + k))) := by
      let Eo := innerWeightEquiv (radialHilbertMeasure Γ.reference)
        (Wo sign) (hWo sign) (ho sign) CW Co (hOut sign) (hOutInv sign)
      let Ei := innerWeightEquiv (radialHilbertMeasure Γ.reference)
        (Wi sign) (hWi sign) (hi sign) CW CW (hCW sign) (hInInv sign)
      have hEo := innerWeightEquiv_ae (radialHilbertMeasure Γ.reference)
        (Wo sign) (hWo sign) (ho sign) CW Co (hOut sign) (hOutInv sign)
      have hEi := innerWeightEquiv_ae (radialHilbertMeasure Γ.reference)
        (Wi sign) (hWi sign) (hi sign) CW CW (hCW sign) (hInInv sign)
      have hs : |(if sign then (1 : ℝ) else -1)| ≤ 1 := by cases sign <;> norm_num
      have hcap := P.retainedMorse_terminal_cap_weight_bound hD hw metadata.selected
        metadata.geometry metadata.first_two hhead hT hleft hright hTL hTR k hk
        hΓ.2.1 hN l r (selectedTerminalSide i) hs
      have hm : S.chain.index + (k - 1) = S.chain.index + k - 1 := by omega
      have hk' : S.chain.index + k - 1 - S.chain.index = k - 1 := by omega
      simp only [hm] at hcap
      simp only [← hk'] at hcap
      let capSet := Icc
        (terminalMorseLayerRadius (selectedTerminalSide i)
          (morseChainA S.chain (S.chain.index + k - 1))
          (morseChainB S.chain (S.chain.index + k - 1))
          (P.sideRadius (selectedTerminalSide i) *
            metadata.geometry.factor (selectedTerminalSide i) (S.chain.index + k - 1 - S.chain.index))
          (metadata.geometry.normal (S.chain.index + k - 1 - S.chain.index)) 0)
        (terminalMorseLayerRadius (selectedTerminalSide i)
          (morseChainA S.chain (S.chain.index + k - 1))
          (morseChainB S.chain (S.chain.index + k - 1))
          (P.sideRadius (selectedTerminalSide i) *
            metadata.geometry.factor (selectedTerminalSide i) (S.chain.index + k - 1 - S.chain.index))
          (metadata.geometry.normal (S.chain.index + k - 1 - S.chain.index))
          (terminalMorseLayerLength (selectedTerminalSide i)
            (morseChainA S.chain (S.chain.index + k - 1))))
      let capWeight := exp (radialS S.chain.index) * exp
        (41414 * radialQ (S.chain.index + k) +
          (if sign then (1 : ℝ) else -1) * radialS (S.chain.index + k))
      have hcapIn : ∀ᵐ x ∂radialHilbertMeasure Γ.reference, x ∈ capSet →
          |Wi sign x| ≤ capWeight := by
        simpa only [capSet, capWeight, matchedMorseSignedWeight] using hcap
      have hcapOut : ∀ᵐ x ∂radialHilbertMeasure Γ.reference, x ∈ capSet →
          |Wo sign x| ≤ capWeight := by
        filter_upwards [hcapIn] with x hx hxc
        change |innerMorseInnerLoss S.chain.index k H 37 x * Wi sign x| ≤ capWeight
        rw [abs_mul]
        exact (mul_le_mul_of_nonneg_right
          (innerMorseInnerLoss_le_one S.chain.index k H (Nat.cast_nonneg 37) x)
          (abs_nonneg _)).trans (by simpa only [one_mul] using hx hxc)
      have hp := P.later_innerPoisson_twoWeight_bound metadata Γ hΓ hw hhead
        hleft hright hCstar R hM (by omega) hj heven hband hML hMR hcutoff hstandIn
        hsource hattenuation i Eo Ei (Wo sign) (Wi sign) hEo hEi
        S.chain.index 41414 (if sign then (1 : ℝ) else -1) hcapOut hcapIn
      have hh : ‖Out sign (R.matching.innerPoisson i)‖ ≤
          ((1 + sqrt 2 * B) * exp (radialS S.chain.index)) *
            exp (aP * radialQ (S.chain.index + k) +
              (if sign then (1 : ℝ) else -1) * radialS (S.chain.index + k)) :=
        hp.trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (add_le_add le_rfl (hop sign)) (exp_pos _).le)
          (exp_pos _).le)
      cases sign <;> simpa only [Bool.false_eq_true, ite_false, ite_true,
        one_mul, neg_one_mul] using hh
    intro u i
    apply matchedMode_twoSign_supported_column_envelope Γ.reference hP
      (R.matching.innerPoisson i) (S.chain.index + k) level rfl
      (Ioo R.matching.innerLeft R.matching.innerRight)
      (matchedInnerPoisson_supported hΓ.2.1 hM i)
      Wo hWo ho (fun _ => CW) (fun _ => Co) hOut hOutInv
      (mul_nonneg (by linarith only [hBop]) (exp_pos _).le)
      (matchedMorseLocalizerWeightConstant_ge_one _ _)
      (fun sign => hweighted sign i) ?_ u
    intro sign m
    filter_upwards [hlocal sign m] with x hx hχx hinner
    exact (hx hχx hinner).1.trans (mul_le_mul_of_nonneg_left
      (exp_le_exp.mpr (sub_le_sub_right
        (mul_le_mul_of_nonneg_right (matchedMorseTerminalColumnExponent_ge_cell 41414)
          (radialQ_nonneg _)) _))
      (zero_le_one.trans (matchedMorseLocalizerWeightConstant_ge_one _ _)))

end SeedRetainedPair

end ContinuousFlexibility.Radial
