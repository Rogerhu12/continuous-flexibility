module

public import ContinuousFlexibility.Radial.R11bModeUniqueness
public import ContinuousFlexibility.Radial.R11bMeanUniqueness
public import ContinuousFlexibility.Radial.R11bPhysicalCompleteness
public import ContinuousFlexibility.Radial.R11bWeightMonotonicity

/-!
# Uniqueness on every positively attenuated maximum graph

The positive even channels are determined by the given modal inverses. The
zero channel is determined by endpoint resistance. Actual angular
completeness then identifies the original measurable physical fields. The
argument is independent of the coefficient exponents in the cell weights.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory
open ContinuousFlexibility.Statements

theorem r11b_maximum_graph_unique {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    (hmodes : ∀ j : ℕ, 2 ≤ j → Even j →
      ∃ G : RadialModePair D →L[ℝ] RadialModePair D, ModeInverseProperties D j G)
    {γ γ' M₀ M₀' M₁ M₁' : ℝ} (hγ : 0 < γ) (hγ' : 0 < γ')
    {U V : RadialUnknown} {F : RadialSource}
    (hUF : ReferenceGraph D γ M₀ M₁ U F)
    (hVF : ReferenceGraph D γ' M₀' M₁' V F) :
    RadialRepresentativeEq D U V := by
  have hcoeff : ∀ j : ℕ, 0 < j → Even j →
      referenceMode U.1 j =ᵐ[volume.restrict (radialCore D)] referenceMode V.1 j := by
    intro j hj he
    have hj₂ : 2 ≤ j := by
      obtain ⟨k, hk⟩ := he
      omega
    obtain ⟨G, hG⟩ := hmodes j hj₂ he
    exact (r11b_graph_mode_unique hD hborder hγ hγ' hUF hVF hj hG).1
  obtain ⟨G₂, hG₂⟩ := hmodes 2 le_rfl (by decide)
  have hscalar : U.2 = V.2 :=
    (r11b_graph_mode_unique hD hborder hγ hγ' hUF hVF (by decide : 0 < 2) hG₂).2 rfl
  have hU := r11b_output_memLp hD hborder hγ hUF.1
  have hV := r11b_output_memLp hD hborder hγ' hVF.1
  obtain ⟨aU, haU⟩ := hUF.1
  obtain ⟨aV, haV⟩ := hVF.1
  have hpU (r : ℝ) : Function.Periodic (fun θ => U.1 (r, θ)) Real.pi := by
    intro θ
    have h := haU.2.2.1 (r, θ)
    change U.1 (r + 0, θ + Real.pi) = U.1 (r, θ) at h
    simpa only [add_zero] using h
  have hpV (r : ℝ) : Function.Periodic (fun θ => V.1 (r, θ)) Real.pi := by
    intro θ
    have h := haV.2.2.1 (r, θ)
    change V.1 (r + 0, θ + Real.pi) = V.1 (r, θ) at h
    simpa only [add_zero] using h
  exact ⟨hscalar, r11b_physical_ae_eq_of_referenceModes hU hV
    haU.2.2.2 haV.2.2.2 hpU hpV
    (r11b_graph_mean_unique hD hborder hγ hγ' hUF hVF) hcoeff⟩

/-- Increasing the coefficient exponents preserves the same full inverse,
with uniqueness now proved on the enlarged maximum graph. -/
theorem r11b_referenceInverse_enlarge {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    (hmodes : ∀ j : ℕ, 2 ≤ j → Even j →
      ∃ H : RadialModePair D →L[ℝ] RadialModePair D, ModeInverseProperties D j H)
    {γ M₀ M₀' M₁ M₁' : ℝ} (hγ : 0 < γ)
    (h₀ : M₀ ≤ M₀') (h₁ : M₁ ≤ M₁')
    {G : RadialSource → RadialUnknown}
    (hG : ReferenceInverseProperties D γ M₀ M₁ G) :
    ReferenceInverseProperties D γ M₀' M₁' G := by
  have hab := hD.choose_spec.1.2.1.le
  apply r11b_referenceInverseProperties_mono hab h₀ h₁ hG
  intro U F hUF
  exact r11b_maximum_graph_unique hD hborder hmodes hγ hγ
    (hG.1 F (r11b_sourceMember_of_le hab h₀ hUF.2.1)) hUF

end ContinuousFlexibility.Radial
