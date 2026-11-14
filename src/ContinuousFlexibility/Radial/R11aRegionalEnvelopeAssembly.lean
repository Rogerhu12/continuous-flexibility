module

public import ContinuousFlexibility.Radial.ReferenceMatchedFamily
public import ContinuousFlexibility.Radial.MatchedChannelEnvelope
public import ContinuousFlexibility.Radial.MatchedFiniteEnvelope
public import ContinuousFlexibility.Radial.MatchedFlooredRawEnvelope
public import ContinuousFlexibility.Radial.MatchingInverseTheorem

/-!
# The exact R11a conclusion from the four actual regional estimates

All four estimates concern one fixed reference and one actual matching
family. Their constants and coefficient exponents may differ. The
matching formula first combines them on the original canonical labels.
The actual index floor then costs only exp(S N), including the one scalar
channel. The already proved physical Schur construction supplies the
same inverse at the three frozen exponents.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Real
open ContinuousFlexibility.Radial

/-- This is only the final combination of the actual regional estimates.
The hypotheses do not include a global inverse norm or a weighted
conclusion. The original geometry is used here only for its exact
canonical cell labels. -/
theorem r11aStatement_of_regional_envelopes {D₀ D : ReferenceData}
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
    Blueprint.R11aStatement := by
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
  refine r11aStatement_of_modal_envelope hD hborder hconstruction G hG
    (fun q => ⟨M q, hfrequency q, hactual q⟩) fiberBound hfibers hcard
    (C₀ := C * exp (radialS floor)) (a := 3 * a + 1)
    (mul_pos hC (exp_pos _)) ?_
  intro q k m
  exact (hbound q k m).trans
    (referenceRawChannel_envelope_floor hfloor hC.le (by linarith only [ha]) k m)

end ContinuousFlexibility.Statements
