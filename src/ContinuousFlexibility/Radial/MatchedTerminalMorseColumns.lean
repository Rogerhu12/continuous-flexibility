import ContinuousFlexibility.Radial.MatchedTerminalWeightedCorrection
import ContinuousFlexibility.Radial.MatchedTerminalMorseLeading

/-!
# Actual terminal Morse columns after a physical weight

Both endpoint choices use the original normalized Morse stand-in and
the original terminal cutoff. Their true leading term has cost
400 / (j A²). The residual retains its original attenuation and is
corrected by the same scalar-gated inner inverse in the matching data.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter Real MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff

theorem terminalMorsePhysicalCutoff_tsupport_deriv_cap
    (long : Bool) {A B s : ℝ} {r : ℝ → ℝ}
    (hB : 0 < B) (hAB : 4 * B < A) (hs : 0 < s)
    (hr : IsNormalizedMorseCell A B r) :
    tsupport (deriv (terminalMorsePhysicalCutoff long A B s r)) ⊆
      Icc (terminalMorseLayerRadius long A B s r 0)
        (terminalMorseLayerRadius long A B s r (terminalMorseLayerLength long A)) := by
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  have hL := terminalMorseLayerLength_pos long hA
  have hmono := (terminalMorseLayerRadius_strictMono long hB hAB hs hr).monotoneOn
  have hl : terminalMorseLayerRadius long A B s r 0 ≤
      terminalMorseLayerLeft long A B s r :=
    hmono (show (0 : ℝ) ∈ Icc 0 (terminalMorseLayerLength long A) by
      exact ⟨le_rfl, hL.le⟩)
      (show terminalMorseLayerLength long A / 4 ∈
        Icc 0 (terminalMorseLayerLength long A) by constructor <;> linarith)
      (by linarith)
  have hh : terminalMorseLayerRight long A B s r ≤
      terminalMorseLayerRadius long A B s r (terminalMorseLayerLength long A) :=
    hmono (show terminalMorseLayerLength long A / 2 ∈
        Icc 0 (terminalMorseLayerLength long A) by constructor <;> linarith)
      (show terminalMorseLayerLength long A ∈
        Icc 0 (terminalMorseLayerLength long A) by exact ⟨hL.le, le_rfl⟩)
      (by linarith)
  exact (terminalMorsePhysicalCutoff_tsupport_deriv long hB hAB hs hr).trans
    (fun _ hx => ⟨hl.trans hx.1, hx.2.trans hh⟩)

section OriginalColumn

variable {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hBorder : RadialTrueBorder D)
    (R : TerminalRegionalData D) (hM : MatchingLocalRealizations D R.matching)
    (i : Fin 2) (long : Bool)
    (E : RadialModeL2 D ≃L[ℝ] RadialModeL2 D) (weight : ℝ → ℝ)
    (hE : ∀ f, E f =ᵐ[radialHilbertMeasure D] fun x => weight x * f x)

local notation "Em" => E.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ)
local notation "T" =>
  (Em : RadialModePair D →L[ℝ] RadialModePair D) ∘L R.matching.innerInverse ∘L
    matchingSourceInnerCLM D R.matching hM ∘L
    matchedModeScalarGate D (decide (R.matching.frequency = 2)) ∘L
    (ContinuousLinearEquiv.symm Em : RadialModePair D →L[ℝ] RadialModePair D)

include hD hBorder hE

/-- The full original external column has the physical cap bound.
The operator norm on the right is the actual restricted inner inverse,
which is identified with the same finite-chain C by frozen uniqueness. -/
theorem terminalRegional_innerPoisson_morse_weighted_bound
    {A B s weightScale W : ℝ} {r : ℝ → ℝ}
    (hB : 0 < B) (hAB : 4 * B < A) (hs : 0 < s)
    (hscale : 0 < weightScale) (hA₀ : A ≤ 1 / 1000) (hBA : B ≤ A ^ 9)
    (hr : IsNormalizedMorseCell A B r) (hw : ContDiff ℝ ∞ D.w)
    (hweight : ∀ x ∈ Icc morseCellLeftCut (morseRightCapEnd A B (1 / 100)),
      D.w (s * r x) = weightScale * (s * deriv r x))
    (hcutoff : R.cutoff i = terminalMorsePhysicalCutoff long A B s r)
    (hode : ∀ x ∈ Icc (if long then morseRightTurn A B else morseCellLeftCut)
        (if long then morseRightCapEnd A B (1 / 100) else morseShortLeftCapCut),
      radialJacobi ((R.matching.frequency : ℝ) ^ 2) D.w (R.standIn i) (s * r x) = 0)
    (hzero : R.standIn i
      (s * r (if long then morseRightTurn A B else morseShortLeftCapCut)) = 0)
    (hjoin : R.standIn i
      (s * r (if long then morseRightCapEnd A B (1 / 100) else morseCellLeftCut)) = 1)
    (hnorm : R.matching.boundaryScale i = standInBoundaryScale
      ((R.matching.frequency : ℝ) ^ 2)
      (D.w (s * r (if long then morseRightCapEnd A B (1 / 100) else morseCellLeftCut)))
      (s * r (if long then morseRightCapEnd A B (1 / 100) else morseCellLeftCut)))
    (hcap : Icc (terminalMorseLayerRadius long A B s r 0)
      (terminalMorseLayerRadius long A B s r (terminalMorseLayerLength long A)) ⊆
        Icc R.matching.innerLeft R.matching.innerRight)
    (hterminal : if long then
      R.matching.innerRight =
        terminalMorseLayerRadius long A B s r (terminalMorseLayerLength long A)
      else R.matching.innerLeft = terminalMorseLayerRadius long A B s r 0)
    (hW : 0 ≤ W)
    (hlocal : ∀ᵐ x ∂radialHilbertMeasure D,
      x ∈ Icc (terminalMorseLayerRadius long A B s r 0)
        (terminalMorseLayerRadius long A B s r (terminalMorseLayerLength long A)) →
      |weight x| ≤ W) :
    ‖Em (R.matching.innerPoisson i)‖ ≤
      W * (400 / ((R.matching.frequency : ℝ) * A ^ 2) +
        ‖T‖ * ((R.sourceCost * sqrt (R.matching.D0 i)) * exp (-R.attenuation i))) := by
  have hsupp : tsupport (deriv (R.cutoff i)) ⊆
      Icc (terminalMorseLayerRadius long A B s r 0)
        (terminalMorseLayerRadius long A B s r (terminalMorseLayerLength long A)) := by
    rw [hcutoff]
    exact terminalMorsePhysicalCutoff_tsupport_deriv_cap long hB hAB hs hr
  have hsource := terminalRegional_source_weighted_bound_ae R i E weight hE hW
    (hlocal.mono (fun x hx hxs => hx (hsupp hxs)))
  have hlead : ‖Em (terminalCapInnerLift hD R.matching.innerLeft R.matching.innerRight
      (R.matching.boundaryScale i) (R.cutoff_smooth i) (R.standIn_smooth i))‖ ≤
      W * (400 / ((R.matching.frequency : ℝ) * A ^ 2)) := by
    simpa only [hcutoff] using
      terminalMorseCapInnerLift_weighted_bound hD long hB hAB R.frequency_pos hs
        hscale hA₀ hBA hr hw (R.standIn_smooth i) hweight hode hzero hjoin
        hnorm hcap hterminal E weight hE hW hlocal
  exact (terminalRegional_innerPoisson_weighted_norm_split
    hD hBorder R hM i E weight hE).trans
      ((add_le_add hlead (mul_le_mul_of_nonneg_left hsource (norm_nonneg T))).trans_eq
        (by ring))

end OriginalColumn

end ContinuousFlexibility.Radial
