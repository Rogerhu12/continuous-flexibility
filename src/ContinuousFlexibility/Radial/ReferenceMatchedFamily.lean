module

public import ContinuousFlexibility.Blueprint.Statements
public import ContinuousFlexibility.Radial.ReferenceModalKernelEnvelope

/-!
# The frozen R11a conclusion from one actual matched family

All modes, their matching representations, the physical cell labels and
the raw spatial estimate refer to the same reference data. The preceding
construction supplies one inverse at the three exponents. This assembly
does not choose a second geometry or replace an actual matching operator.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open ContinuousFlexibility.Radial

theorem r11aStatement_of_modal_envelope {D : ReferenceData}
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
    Blueprint.R11aStatement := by
  obtain ⟨M₀, M₁, _, H, hH⟩ :=
    referenceSchur_common_inverse_of_modal_envelope hD hborder G hG N hfibers hcard
      hC₀ hmodal
  refine ⟨D, hD, hborder, hconstruction, 1 / 8, M₀, M₁, by norm_num, by norm_num, H, ?_, hH⟩
  intro j hj heven
  obtain ⟨k, hk⟩ := heven
  have hkpos : 0 < k := by omega
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hkpos)
  have hjn : j = 2 * (n + 1) := by omega
  rw [hjn]
  exact ⟨G n, hG n, hmatched n⟩

end ContinuousFlexibility.Statements
