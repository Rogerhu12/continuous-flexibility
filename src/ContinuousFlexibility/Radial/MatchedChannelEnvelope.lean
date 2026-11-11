import ContinuousFlexibility.Radial.MatchedUniformEnvelope
import ContinuousFlexibility.Radial.MatchedPhysicalChannelComparison
import ContinuousFlexibility.Radial.MatchedPhysicalScalarGate

/-!
# The actual channel and scalar gate in the matching estimate

The scalar gate contracts the product norm and preserves pairing symmetry
after every actual channel. Consequently the two column estimates already
control both rows in the matching formula. This is the channel form used by
the common inverse construction.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open ContinuousFlexibility.Statements

theorem matchedModeChannel_pairing (D : ReferenceData) (hP : RadialPartition D)
    (m : ℕ) (U F : RadialModePair D) :
    modePairing D U (matchedModeChannel D hP m F) =
      modePairing D (matchedModeChannel D hP m U) F := by
  cases m with
  | zero => exact matchedModeBorder_pairing D U F
  | succ m => exact matchedModeCell_pairing D hP m U F

theorem matchedModeScalarGate_norm_apply_le (D : ReferenceData) (active : Bool)
    (U : RadialModePair D) : ‖matchedModeScalarGate D active U‖ ≤ ‖U‖ := by
  rw [matchedModeScalarGate_apply]
  cases active with
  | false =>
      change ‖(U.1, (0 : ℝ))‖ ≤ ‖U‖
      rw [Prod.norm_def, Prod.norm_def, norm_zero, max_eq_left (norm_nonneg _)]
      exact le_max_left _ _
  | true => exact le_rfl

theorem matchedModeScalarGate_channel_pairing (D : ReferenceData)
    (hP : RadialPartition D) (active : Bool) (m : ℕ) (U F : RadialModePair D) :
    modePairing D U ((matchedModeScalarGate D active ∘L matchedModeChannel D hP m) F) =
      modePairing D ((matchedModeScalarGate D active ∘L matchedModeChannel D hP m) U) F := by
  cases m with
  | zero =>
      cases active with
      | false =>
          simp only [ContinuousLinearMap.comp_apply, matchedModeChannel,
            matchedModeScalarGate_apply, matchedModeBorder_apply, Bool.false_eq_true,
            ↓reduceIte, modePairing, inner_zero_right, inner_zero_left,
            mul_zero, zero_mul, add_zero, zero_add]
      | true =>
          simpa only [ContinuousLinearMap.comp_apply, matchedModeChannel,
            matchedModeScalarGate_apply, Bool.true_eq_true, ↓reduceIte] using
              matchedModeBorder_pairing D U F
  | succ m =>
      have h (V : RadialModePair D) :
          matchedModeScalarGate D active (matchedModeCell D hP m V) =
            matchedModeCell D hP m V :=
        matchedModeScalarGate_eq_self D active _ (fun _ => rfl)
      simpa only [ContinuousLinearMap.comp_apply, matchedModeChannel, h] using
        matchedModeCell_pairing D hP m U F

theorem matchedMode_actual_channels_spatial_envelope {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hP : RadialPartition D)
    (G : ℕ → RadialModePair D →L[ℝ] RadialModePair D)
    (M : ℕ → RadialMatchingData D)
    (hM : ∀ i, ActualMatchedRepresentation D (G i) (M i))
    (transition level : ℕ → ℕ)
    {a d C₀ Cₚ Cκ : ℝ}
    (ha : 0 ≤ a) (hd : 0 ≤ d) (hC₀ : 0 < C₀) (hCₚ : 0 < Cₚ) (hCκ : 0 < Cκ)
    (hinner : ∀ i k m,
      ‖matchedModeChannel D hP k ∘L (M i).innerInverse ∘L
        matchingSourceInnerCLM D (M i) (actualMatchedRepresentation_localRealizations (hM i)) ∘L
          (matchedModeScalarGate D (decide (i = 0)) ∘L matchedModeChannel D hP m)‖ ≤
        C₀ * Real.exp
          (a * (radialQ (level k) +
            radialQ (level m)) -
            |radialS (level k) -
              radialS (level m)|))
    (houter : ∀ i k m,
      ‖matchedModeChannel D hP k ∘L (M i).outerInverse ∘L
        matchingSourceOuterCLM D (M i) (actualMatchedRepresentation_localRealizations (hM i)) ∘L
          (matchedModeScalarGate D (decide (i = 0)) ∘L matchedModeChannel D hP m)‖ ≤
        C₀ * Real.exp
          (a * (radialQ (level k) +
            radialQ (level m)) -
            |radialS (level k) -
              radialS (level m)|))
    (hPi : ∀ i k t, ‖matchedModeChannel D hP k ((M i).innerPoisson t)‖ ≤
      Cₚ * Real.exp
        (a * (radialQ (level k) + radialQ (transition i)) -
          |radialS (level k) - radialS (transition i)|))
    (hPo : ∀ i k t, ‖matchedModeChannel D hP k ((M i).outerPoisson t)‖ ≤
      Cₚ * Real.exp
        (a * (radialQ (level k) + radialQ (transition i)) -
          |radialS (level k) - radialS (transition i)|))
    (hmargin : ∀ i, 4 / (M i).margin + 1 ≤
      Cκ * Real.exp (d * radialQ (transition i))) :
    ∃ C : ℝ, 0 < C ∧ ∀ i k m,
      ‖matchedModeChannel D hP k ∘L
          (G i ∘L matchedModeScalarGate D (decide (i = 0))) ∘L
            matchedModeChannel D hP m‖ ≤
        C * Real.exp
          ((3 * a + d) * (radialQ (level k) +
            radialQ (level m)) -
            |radialS (level k) -
              radialS (level m)|) := by
  obtain ⟨C, hC, hbound⟩ := matchedMode_actual_spatial_envelope hD G M hM
    transition (level) (matchedModeChannel D hP)
    (fun i m => matchedModeScalarGate D (decide (i = 0)) ∘L matchedModeChannel D hP m)
    (fun i m U F => matchedModeScalarGate_channel_pairing D hP _ m U F)
    ha hd hC₀ hCₚ hCκ hinner houter hPi hPo
    (fun i m t => (matchedModeScalarGate_norm_apply_le D _ _).trans (hPi i m t))
    (fun i m t => (matchedModeScalarGate_norm_apply_le D _ _).trans (hPo i m t))
    hmargin
  refine ⟨C, hC, ?_⟩
  intro i k m
  simpa only [ContinuousLinearMap.comp_assoc] using hbound i k m

end ContinuousFlexibility.Radial
