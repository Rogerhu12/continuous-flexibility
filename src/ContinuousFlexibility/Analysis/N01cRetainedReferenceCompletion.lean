module

public import ContinuousFlexibility.Blueprint.R11b
public import ContinuousFlexibility.Blueprint.R12
public import ContinuousFlexibility.Radial.ReferenceMatchedFamily

/-! # Completing the inverse on a specified reference -/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open ContinuousFlexibility.Radial

/-- The existing R11a conclusions with the reference kept as a parameter. -/
def N01cReferenceInverseAt (D : ReferenceData) : Prop :=
  IsAccumulatingProfile D ∧ RadialTrueBorder D ∧ RadialConstructionGeometry D ∧
    ∃ ε M₀ M₁ : ℝ, 0 < ε ∧ ε < 1 / 4 ∧
      ∃ G : RadialSource → RadialUnknown,
        (∀ j : ℕ, 2 ≤ j → Even j →
          ∃ Gmode : RadialModePair D →L[ℝ] RadialModePair D,
            ModeInverseProperties D j Gmode ∧
            ∃ M : RadialMatchingData D,
              M.frequency = j ∧ ActualMatchedRepresentation D Gmode M) ∧
        ∀ γ : ℝ, γ = referenceBeta - ε ∨ γ = referenceBeta ∨ γ = referenceBeta + ε →
          ReferenceInverseProperties D γ M₀ M₁ G

theorem n01cReferenceInverseAt_of_modal_envelope {D : ReferenceData}
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
    N01cReferenceInverseAt D := by
  obtain ⟨M₀, M₁, _, H, hH⟩ :=
    referenceSchur_common_inverse_of_modal_envelope hD hborder G hG N hfibers hcard
      hC₀ hmodal
  refine ⟨hD, hborder, hconstruction, 1 / 8, M₀, M₁, by norm_num, by norm_num, H, ?_, hH⟩
  intro j hj heven
  obtain ⟨k, hk⟩ := heven
  have hkpos : 0 < k := by omega
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hkpos)
  have hjn : j = 2 * (n + 1) := by omega
  rw [hjn]
  exact ⟨G n, hG n, hmatched n⟩

/-- The existing first-normal and graph-completion proofs preserve `D`. -/
theorem n01cReferenceInverseAt_radialReference {D : ReferenceData}
    (h : N01cReferenceInverseAt D) : IsRadialReference D := by
  obtain ⟨hD, hborder, hgeo, ε, M₀, M₁, hε, hεquarter, G, hmatchedModes, hG⟩ := h
  have hmodes : ∀ j : ℕ, 2 ≤ j → Even j →
      ∃ H : RadialModePair D →L[ℝ] RadialModePair D, ModeInverseProperties D j H := by
    intro j hj he
    obtain ⟨H, hH, _⟩ := hmatchedModes j hj he
    exact ⟨H, hH⟩
  obtain ⟨H₂, _, M₂, _, hMatch₂⟩ := hmatchedModes 2 le_rfl (by decide)
  obtain ⟨L, hL, hnormal⟩ :=
    r11b_firstNormalInverseEstimate hD hborder M₀ M₁ hmodes ⟨H₂, M₂, hMatch₂⟩
  have hnatural : RadialNaturalKernels D :=
    radialNaturalKernels_of_modeInverses hD hborder hgeo.1 hmodes
  refine ⟨hD, hnatural, hgeo.2, hborder, ε, M₀, M₁ + L, hε, hεquarter, G, ?_⟩
  intro γ hγ
  have hγpos : 0 < γ := by
    rcases hγ with rfl | rfl | rfl <;> dsimp only [referenceBeta] <;>
      linarith only [hε, hεquarter]
  have hγabs : |γ| ≤ 1 := by
    rw [abs_of_pos hγpos]
    rcases hγ with rfl | rfl | rfl <;> dsimp only [referenceBeta] <;>
      linarith only [hε, hεquarter]
  have hinverse : ReferenceInverseProperties D γ M₀ (M₁ + L) G :=
    r11b_referenceInverse_enlarge hD hborder hmodes hγpos le_rfl
      (le_add_of_nonneg_right hL) (hG γ hγ)
  have hnormal' : FirstNormalInverseEstimate D γ M₀ (M₁ + L) G :=
    hnormal γ hγpos hγabs G (hG γ hγ)
  have hcore : ReferenceSmoothCoreClosure D γ M₀ (M₁ + L) := by
    apply referenceSmoothCoreClosure_of_dense_inverse_core hD hinverse
      (ReferenceSmoothFiniteSource D)
    · intro F hF
      obtain ⟨Fₙ, hsmooth, _, hmember, hconv⟩ := hF.exists_smoothFinite_approximation hD
      exact ⟨Fₙ, fun n => ⟨hmember n, hsmooth n⟩, hconv⟩
    · intro F hF hfinite
      exact reference_smooth_inverse_image hD hborder hgeo.1
        (hmodes 2 le_rfl (by decide)) hinverse hnormal' hγpos hF hfinite
  exact ⟨hinverse, referenceGraphClosed_of_positive hD hborder hγpos, hcore,
    referenceGreenReciprocity_of_smooth_core hD hborder hγpos hcore, hnormal'⟩

end ContinuousFlexibility.Statements
