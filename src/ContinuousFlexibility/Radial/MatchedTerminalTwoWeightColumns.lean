import ContinuousFlexibility.Radial.MatchedTerminalMorseColumns

/-!
# Actual terminal columns between the two finite-chain weights

The physical leading term carries the output weight. The original
residual carries the input weight. Their correction is the same
restricted matching inverse between those two weights. In particular,
the original coefficient loss may stay on the output side throughout.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter Real MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff

section TwoWeights

variable {D : ReferenceData}
  (hD : IsAccumulatingProfile D) (hBorder : RadialTrueBorder D)
  (R : TerminalRegionalData D) (hM : MatchingLocalRealizations D R.matching)
  (i : Fin 2)
  (Eo Ei : RadialModeL2 D ≃L[ℝ] RadialModeL2 D)

local notation "Om" => Eo.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ)
local notation "Im" => Ei.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ)
local notation "T" =>
  (Om : RadialModePair D →L[ℝ] RadialModePair D) ∘L R.matching.innerInverse ∘L
    matchingSourceInnerCLM D R.matching hM ∘L
    matchedModeScalarGate D (decide (R.matching.frequency = 2)) ∘L
    (ContinuousLinearEquiv.symm Im : RadialModePair D →L[ℝ] RadialModePair D)

include hD hBorder hM

/-- The actual zero-scalar residual is unchanged by the original
source restriction and frequency gate. -/
theorem terminalRegional_innerPoisson_twoWeight_norm_split :
    ‖Om (R.matching.innerPoisson i)‖ ≤
      ‖Om (terminalCapInnerLift hD R.matching.innerLeft R.matching.innerRight
        (R.matching.boundaryScale i) (R.cutoff_smooth i) (R.standIn_smooth i))‖ +
      ‖T‖ * ‖Im (terminalCapInnerSource R.matching.innerLeft R.matching.innerRight
        (R.matching.boundaryScale i) (R.cutoff i) (R.standIn i) (R.source_memLp i))‖ := by
  let F := terminalCapInnerSource R.matching.innerLeft R.matching.innerRight
    (R.matching.boundaryScale i) (R.cutoff i) (R.standIn i) (R.source_memLp i)
  have hFs : F.2 = 0 := rfl
  have hfix : R.matching.sourceInner F = F := by
    rw [R.inner_source F]
    exact modeInnerSource_idempotent D R.matching.innerLeft R.matching.innerRight _
  have hgate : matchedModeScalarGate D (decide (R.matching.frequency = 2)) F = F :=
    matchedModeScalarGate_eq_self D _ F (fun _ => hFs)
  have happ : T (Im F) = Om (R.matching.innerInverse F) := by
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.symm_apply_apply, hgate, matchingSourceInnerCLM_apply, hfix]
  have hrem : ‖Om (R.matching.innerInverse F)‖ ≤ ‖T‖ * ‖Im F‖ := by
    rw [← happ]
    exact (T).le_opNorm _
  rw [terminalRegional_innerPoisson_eq hD hBorder R hM i, map_sub]
  exact (norm_sub_le _ _).trans (add_le_add le_rfl hrem)

variable (long : Bool) (weightOut weightIn : ℝ → ℝ)
  (hEo : ∀ f, Eo f =ᵐ[radialHilbertMeasure D] fun x => weightOut x * f x)
  (hEi : ∀ f, Ei f =ᵐ[radialHilbertMeasure D] fun x => weightIn x * f x)

include hEo hEi

/-- The same physical cap supplies both localized weights. The original
source attenuation and the actual inverse remain explicit. -/
theorem terminalRegional_innerPoisson_morse_twoWeight_bound
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
    (hlocalOut : ∀ᵐ x ∂radialHilbertMeasure D,
      x ∈ Icc (terminalMorseLayerRadius long A B s r 0)
        (terminalMorseLayerRadius long A B s r (terminalMorseLayerLength long A)) →
      |weightOut x| ≤ W)
    (hlocalIn : ∀ᵐ x ∂radialHilbertMeasure D,
      x ∈ Icc (terminalMorseLayerRadius long A B s r 0)
        (terminalMorseLayerRadius long A B s r (terminalMorseLayerLength long A)) →
      |weightIn x| ≤ W) :
    ‖Om (R.matching.innerPoisson i)‖ ≤
      W * (400 / ((R.matching.frequency : ℝ) * A ^ 2) +
        ‖T‖ * ((R.sourceCost * sqrt (R.matching.D0 i)) * exp (-R.attenuation i))) := by
  have hsupp : tsupport (deriv (R.cutoff i)) ⊆
      Icc (terminalMorseLayerRadius long A B s r 0)
        (terminalMorseLayerRadius long A B s r (terminalMorseLayerLength long A)) := by
    rw [hcutoff]
    exact terminalMorsePhysicalCutoff_tsupport_deriv_cap long hB hAB hs hr
  have hsource := terminalRegional_source_weighted_bound_ae R i Ei weightIn hEi hW
    (hlocalIn.mono (fun x hx hxs => hx (hsupp hxs)))
  have hlead : ‖Om (terminalCapInnerLift hD R.matching.innerLeft R.matching.innerRight
      (R.matching.boundaryScale i) (R.cutoff_smooth i) (R.standIn_smooth i))‖ ≤
      W * (400 / ((R.matching.frequency : ℝ) * A ^ 2)) := by
    simpa only [hcutoff] using
      terminalMorseCapInnerLift_weighted_bound hD long hB hAB R.frequency_pos hs
        hscale hA₀ hBA hr hw (R.standIn_smooth i) hweight hode hzero hjoin
        hnorm hcap hterminal Eo weightOut hEo hW hlocalOut
  exact (terminalRegional_innerPoisson_twoWeight_norm_split
    hD hBorder R hM i Eo Ei).trans
      ((add_le_add hlead (mul_le_mul_of_nonneg_left hsource (norm_nonneg T))).trans_eq
        (by ring))


end TwoWeights

end ContinuousFlexibility.Radial
