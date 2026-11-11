import ContinuousFlexibility.Radial.R11aClosedInputs
import ContinuousFlexibility.Radial.R11aRetainedFamily
import ContinuousFlexibility.Radial.MatchedInnerCompletedFamily
import ContinuousFlexibility.Radial.MatchedOuterCompletedFamily
import ContinuousFlexibility.Radial.R11aRegionalEnvelopeAssembly

/-!
# The weighted inverse on the actual retained reference

The regional constructions and both spatial estimates use the same
completed matching family. The constants precede the modal index.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set
open scoped ContDiff
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint

theorem r11a_actual_assembly : R11aStatement := by
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
    · simpa only [M, hfrequency q, hleft q] using (hv q false).2.2.2
    · simpa only [M, hfrequency q, hright q] using (hv q true).2.2.2
  have hAB' (q : ℕ) (side : Bool) :
      (M q).A (if side then 1 else 0) (if side then 1 else 0) =
        (outerUnitState (selectedBoundaryState D (M q).frequency (r07OutwardSign side)
          (if side then (M q).innerRight else (M q).innerLeft) (vscaled q side))).1 ∧
      (M q).B (if side then 1 else 0) (if side then 1 else 0) =
        (outerUnitState (selectedBoundaryState D (M q).frequency (r07OutwardSign side)
          (if side then (M q).innerRight else (M q).innerLeft) (vscaled q side))).2 := by
    cases side
    · simpa only [M, hfrequency q, hleft q, selectedTerminalSide, ↓reduceIte]
        using hAB q 0
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
  exact r11aStatement_of_regional_envelopes hD hborder hconstruction G M hactual
    hfrequency floor (2 * floor + 3) hfloor'
    (fun n => (hfibers n).1) (fun n => (hfibers n).2)
    hCI hCO hCPI hCPO hCκ haI haO hbI hbO hinner houter hPi hPo hmargin

end ContinuousFlexibility.Radial
