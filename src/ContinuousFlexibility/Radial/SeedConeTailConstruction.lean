module

public import ContinuousFlexibility.Radial.SeedConeTailGluing
public import ContinuousFlexibility.Radial.SeedNaturalState
public import ContinuousFlexibility.Radial.MorseSecondModeSmoothExtension

/-! # Inward cone continuation of the actual Morse natural second mode -/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

/-- The actual Morse natural tail supplies every input of the cone continuation. -/
theorem exists_morseSecondMode_coneTail
    {T : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ}
    {right : Bool} {entry : ℝ} {u : ℝ → ℝ}
    (hreal : MorseChainRealization T σ D C) (hmass : MorseMassResistanceBounds T σ D C)
    (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2) (hentry : entry ∈ radialCore D)
    (hu : RadialNaturalTail D right 2 entry u) (hder : 0 < deriv D.w entry) :
    Nonempty (SeedConeTail D right entry u) := by
  have hGeometry : RadialProfileGeometry D := hreal.2.2.2.2.2.2.2.2.2.1
  have hne := radialNaturalTail_entry_state_ne_zero hGeometry hentry hu
  obtain ⟨V, hVs, hV₀, hVtail, hVzero, hVjets⟩ :=
    morseSecondMode_naturalTail_smoothZeroExtension hreal hmass hσ hentry hu
  have hd : deriv V entry = deriv u entry := by
    simpa only [radialJet_eq_iteratedDeriv, iteratedDeriv_one] using
      radialTail_extension_entry_jets hentry hu.1 hVs.contDiffAt hV₀ hVtail 1
  have hVne : (V entry, deriv V entry) ≠ (0, 0) := by
    simpa only [hV₀, hd] using hne
  exact exists_seedConeTail_of_smoothNatural hGeometry hentry hder hVs hVtail hVzero
    (radialTail_extension_radialJacobi hGeometry hentry hu hVs hVtail) hVne

end ContinuousFlexibility.Radial
