module

public import ContinuousFlexibility.Radial.MorseSecondModeEndpointFlat
public import ContinuousFlexibility.Radial.RadialTailSmoothExtension

/-! # Smooth outward zero extension of a specified Morse natural tail -/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter
open scoped Topology ContDiff
open ContinuousFlexibility.Statements ContinuousFlexibility.Analysis

/-- Full smooth extension of the specified natural tail, preserving the
entry value and the entire original open tail, and vanishing outward. -/
theorem morseSecondMode_naturalTail_smoothZeroExtension
    {T : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ}
    {right : Bool} {entry : ℝ} {u : ℝ → ℝ}
    (hreal : MorseChainRealization T σ D C)
    (hmass : MorseMassResistanceBounds T σ D C)
    (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2)
    (hentry : entry ∈ radialCore D) (hu : RadialNaturalTail D right 2 entry u) :
    ∃ v : ℝ → ℝ, ContDiff ℝ ∞ v ∧ v entry = u entry ∧
      (∀ r ∈ radialTailInterval D right entry, v r = u r) ∧
      (∀ r, (if right then D.b ≤ r else r ≤ D.a) → v r = 0) ∧
      ∀ k r, (if right then D.b ≤ r else r ≤ D.a) → radialJet k v r = 0 := by
  obtain ⟨c, hc, _, v, hv, heq, hjet⟩ :=
    morseSecondMode_naturalTail_flatGerm hreal hmass hσ hentry hu
  have hj : ∀ k, iteratedDeriv k v (if right then D.b else D.a) = 0 := by
    intro k
    rw [← radialJet_eq_iteratedDeriv]
    exact hjet k
  cases right
  · change D.a < c ∧ c < entry at hc
    obtain ⟨V, hV, hVe, hVz⟩ := smooth_zero_left_of_flat_germ
      hc.1 hc.2 hu.1 hu.2.1.1 hv heq hj
    refine ⟨V, hV, hVe ⟨hentry.1, le_rfl⟩, ?_, ?_, ?_⟩
    · intro r hr
      exact hVe ⟨hr.1, hr.2.le⟩
    · intro r hr
      simpa only [iteratedDeriv_zero] using hVz 0 r hr
    · intro k r hr
      rw [radialJet_eq_iteratedDeriv]
      exact hVz k r hr
  · change entry < c ∧ c < D.b at hc
    obtain ⟨V, hV, hVe, hVz⟩ := smooth_zero_right_of_flat_germ
      hc.1 hc.2 hu.1 hu.2.1.1 hv heq hj
    refine ⟨V, hV, hVe ⟨le_rfl, hentry.2⟩, ?_, ?_, ?_⟩
    · intro r hr
      exact hVe ⟨hr.1.le, hr.2⟩
    · intro r hr
      simpa only [iteratedDeriv_zero] using hVz 0 r hr
    · intro k r hr
      rw [radialJet_eq_iteratedDeriv]
      exact hVz k r hr

end ContinuousFlexibility.Radial
