import ContinuousFlexibility.Radial.MatchedTerminalTwoWeightColumns
import ContinuousFlexibility.Radial.MatchedMorseTerminalBudget
import ContinuousFlexibility.Radial.SelectedLaterCutoffGeometry
import ContinuousFlexibility.Radial.SelectedTerminalMatching
import ContinuousFlexibility.Blueprint.R10a.Geometry

/-!
# The original later terminal columns between two actual weights

The selected incoming solution, cutoff, matching endpoint and boundary
normalization are all the fields of the same completed regional data.
Only local bounds for the two physical weight functions are arguments.
The true inverse norm remains explicit until the finite-chain estimate
is inserted.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff

namespace SeedRetainedPair

variable {S : SelectedTailData} {K : SeedCentralCutoff}
  {headLength length Cstar : ℝ} {requested : ℕ}
  (P : SeedRetainedPair S K headLength length)
  (metadata : R10aSelectedMetadata Cstar requested S)
  (Γ : ConnectedReferenceGeometry) (hΓ : Γ.Realizes)
  (hw : Γ.reference.w = P.pair.profile) (hhead : 0 < headLength)
  (hleft : Γ.centralLeft = exp K.left) (hright : Γ.centralRight = exp K.right)
  (hC : 1000 ≤ S.Cstar)
  (R : TerminalRegionalData Γ.reference)
  (hM : MatchingLocalRealizations Γ.reference R.matching)
  {n : ℕ} (hn : S.chain.index < n)
  (hj : 2 ≤ R.matching.frequency) (heven : Even R.matching.frequency)
  (hband : radialFrequencyBand S.chain S.Cstar n R.matching.frequency)
  (hML : R.matching.innerLeft = P.sideRadius false * S.joinInner false n)
  (hMR : R.matching.innerRight = P.sideRadius true * S.joinInner true n)
  (hcutoff : R.cutoff = fun i =>
    P.laterTerminalCutoff metadata.geometry n (selectedTerminalSide i))
  (hstandIn : R.standIn = fun i =>
    radialRadiusScale (P.sideRadius (selectedTerminalSide i)) 1
      (S.incoming (selectedTerminalSide i) R.matching.frequency))
  (hsource : R.sourceCost = radialE n ^ terminalMorseRelativeSourceExponent)
  (hattenuation : ∀ i, R.attenuation i =
    terminalMatchingAction S.chain (n - 1) R.matching.frequency / 100000000)
  (i : Fin 2)
  (Eo Ei : RadialModeL2 Γ.reference ≃L[ℝ] RadialModeL2 Γ.reference)
  (weightOut weightIn : ℝ → ℝ)
  (hEo : ∀ f, Eo f =ᵐ[radialHilbertMeasure Γ.reference] fun x => weightOut x * f x)
  (hEi : ∀ f, Ei f =ᵐ[radialHilbertMeasure Γ.reference] fun x => weightIn x * f x)

local notation "side" => selectedTerminalSide i
local notation "A" => morseChainA S.chain (n - 1)
local notation "B" => morseChainB S.chain (n - 1)
local notation "radius" => metadata.geometry.normal (n - 1 - S.chain.index)
local notation "scale" => P.sideRadius side * metadata.geometry.factor side (n - 1 - S.chain.index)
local notation "cap" => Icc (terminalMorseLayerRadius side A B scale radius 0)
  (terminalMorseLayerRadius side A B scale radius (terminalMorseLayerLength side A))
local notation "Om" => Eo.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ)
local notation "Im" => Ei.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ)
local notation "Op" =>
  (Om : RadialModePair Γ.reference →L[ℝ] RadialModePair Γ.reference) ∘L
    R.matching.innerInverse ∘L matchingSourceInnerCLM Γ.reference R.matching hM ∘L
      matchedModeScalarGate Γ.reference (decide (R.matching.frequency = 2)) ∘L
        (ContinuousLinearEquiv.symm Im : RadialModePair Γ.reference →L[ℝ] RadialModePair Γ.reference)

include hΓ hw hhead hleft hright hC hn hj heven hband hML hMR hcutoff hstandIn
  hsource hattenuation hEo hEi

theorem later_innerPoisson_twoWeight_bound (N : ℕ) (bcap σ : ℝ)
    (hlocalOut : ∀ᵐ x ∂radialHilbertMeasure Γ.reference, x ∈ cap →
      |weightOut x| ≤ exp (radialS N) * exp (bcap * radialQ n + σ * radialS n))
    (hlocalIn : ∀ᵐ x ∂radialHilbertMeasure Γ.reference, x ∈ cap →
      |weightIn x| ≤ exp (radialS N) * exp (bcap * radialQ n + σ * radialS n)) :
    ‖Om (R.matching.innerPoisson i)‖ ≤
      (1 + ‖Op‖) * exp (radialS N) *
        exp (matchedMorseTerminalColumnExponent bcap * radialQ n + σ * radialS n) := by
  have hm : S.chain.index ≤ n - 1 := by omega
  obtain ⟨hs, hscale, hr, _, hprofile, hode, hzero, hjoin, _⟩ :=
    P.reference_later_cap_data hw metadata.selected metadata.geometry metadata.entry
      metadata.first_two hC side hn hj heven hband (metadata.later_cut side n hn)
      (metadata.later_join side n hn) ((metadata.regular side n _ hj heven hband).1)
  obtain ⟨hB, hAB, hAsmall, _, hBA⟩ := metadata.geometry.cell_terminal_parameters hm
  have hgeometry := P.later_cutoff_geometry metadata.selected metadata.geometry metadata.entry
    metadata.first_two hC hhead hΓ hw hleft hright hn hj heven hband
    (fun s => metadata.later_cut s n hn) (fun s => metadata.later_join s n hn)
    (fun s => (metadata.regular s n _ hj heven hband).1)
  obtain ⟨_, _, _, _, _, _, _, _, hcaps⟩ := hgeometry
  have hcap : cap ⊆ Icc R.matching.innerLeft R.matching.innerRight := by
    rw [hML, hMR]
    exact hcaps side
  have hends := P.later_cap_endpoints metadata.geometry side hn
    (metadata.later_cut side n hn) (metadata.later_join side n hn)
  have hterminal : if side then
      R.matching.innerRight = terminalMorseLayerRadius side A B scale radius
        (terminalMorseLayerLength side A)
      else R.matching.innerLeft = terminalMorseLayerRadius side A B scale radius 0 := by
    cases hs : selectedTerminalSide i with
    | false =>
        simp only [hs, Bool.false_eq_true, ite_false] at hends ⊢
        exact hML.trans hends.1.symm
    | true =>
        simp only [hs, ite_true] at hends ⊢
        exact hMR.trans hends.2.symm
  have hcut : matchingCut Γ.reference R.matching i =
      P.sideRadius side * S.joinInner side n := by
    by_cases hi : i = 0
    · simp only [matchingCut, selectedTerminalSide, hi, ite_true, hML]
    · simp only [matchingCut, selectedTerminalSide, hi, ite_false, hMR]
  have hp := metadata.geometry.scaled_previousCap_endpoints (P.sideRadius side) side hm
  rw [← metadata.later_join side n hn] at hp
  have hjoinRadius : scale * radius
      (if side then morseRightCapEnd A B (1 / 100) else morseCellLeftCut) =
        P.sideRadius side * S.joinInner side n := hp.2
  have hnorm : R.matching.boundaryScale i = standInBoundaryScale
      ((R.matching.frequency : ℝ) ^ 2)
      (Γ.reference.w (scale * radius
        (if side then morseRightCapEnd A B (1 / 100) else morseCellLeftCut)))
      (scale * radius (if side then morseRightCapEnd A B (1 / 100) else morseCellLeftCut)) := by
    rw [R.boundary_scale i, hcut, hjoinRadius]
  have hχ : R.cutoff i = terminalMorsePhysicalCutoff side A B scale radius := by
    rw [hcutoff]
    rfl
  have hU : R.standIn i =
      radialRadiusScale (P.sideRadius side) 1 (S.incoming side R.matching.frequency) := by
    rw [hstandIn]
  rw [← hU] at hode hzero hjoin
  have hraw := terminalRegional_innerPoisson_morse_twoWeight_bound hΓ.2.1 hΓ.2.2.1
    R hM i Eo Ei side weightOut weightIn hEo hEi hB hAB hs hscale hAsmall hBA hr
    (matchingProfileGeometry hΓ.2.1).2.2.1.1 hprofile hχ hode hzero hjoin hnorm hcap
    hterminal (by positivity) hlocalOut hlocalIn
  have hjreal : (1 : ℝ) ≤ R.matching.frequency := by
    exact_mod_cast (show 1 ≤ R.matching.frequency by omega)
  have hatt : 0 ≤ R.attenuation i := by
    rw [hattenuation i]
    exact div_nonneg (terminalMatchingAction_nonneg _ _ _) (by norm_num)
  rw [hsource] at hraw
  exact hraw.trans (matchedMorse_terminal_cost_bound S.chain N (n - 1) n bcap
    ((metadata.selected.2.2.2.1 S.sigma metadata.selected.2.2.1).1.d_eq _ hm)
    (Nat.sub_le _ _) (by omega) hjreal (R.diagonal i).2.2.1 hatt (norm_nonneg Op))

end SeedRetainedPair

end ContinuousFlexibility.Radial
