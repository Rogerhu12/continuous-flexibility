module

public import ContinuousFlexibility.Radial.MorseAssociatedOperator
public import ContinuousFlexibility.Radial.MorseSmoothCore

/-!
# The weak Morse equation on the actual physical energy domain

The compact-test differential equation extends to all energy tests by the
proved smooth compact energy core. Thus it characterizes the associated
form graph for a vector that already has an actual physical energy lift.
This does not identify the maximal distributional domain in L², or assert
that the compact smooth functions are an operator graph core.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace InnerProductSpace

set_option backward.isDefEq.respectTransparency false

local instance : SeminormedAddCommGroup (MorseWeakEnergy →L[ℝ] ℝ) :=
  ContinuousLinearMap.toSeminormedAddCommGroup

local instance : NormedSpace ℝ (MorseWeakEnergy →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

/-- Genuine compact differential tests determine the variational pairing
on the entire physical energy space, with the same Morse parameters. -/
theorem morsePhysicalForm_pairing_of_compactWeak (α w V : ℝ)
    (U : MorseWeakEnergy) (f : MorseL2)
    (hweak : MorseCompactWeakEquation α w V (morseEnergyBase U) f) :
    ∀ W : MorseWeakEnergy,
      morsePhysicalForm α w V U W = ⟪f, morseEnergyBase W⟫_ℝ := by
  let L : MorseWeakEnergy →L[ℝ] ℝ := morsePhysicalForm α w V U -
    (innerSL ℝ f).comp morseEnergyBase
  let S : Set MorseWeakEnergy := {u | ∃ (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hcφ : HasCompactSupport φ),
    u = morseEnergyLift (compactSmooth_morseEnergyDomain hφ hcφ)}
  have hzero : S ⊆ {W : MorseWeakEnergy | L W = 0} := by
    intro W hW
    rcases hW with ⟨φ, hφ, hcφ, rfl⟩
    change morsePhysicalForm α w V U
      (morseEnergyLift (compactSmooth_morseEnergyDomain hφ hcφ)) -
        ⟪f, morseEnergyBase
          (morseEnergyLift (compactSmooth_morseEnergyDomain hφ hcφ))⟫_ℝ = 0
    rw [morsePhysicalForm_weak_test U hφ hcφ α w V,
      morseEnergyLift_base, morseL2_inner_right_toLp]
    exact sub_eq_zero.mpr (hweak φ hφ hcφ).symm
  have hclosed : IsClosed {W : MorseWeakEnergy | L W = 0} :=
    isClosed_eq L.continuous continuous_const
  have hall : closure S ⊆ {W : MorseWeakEnergy | L W = 0} :=
    closure_minimal hzero hclosed
  intro W
  have hW := hall (morseCompactSmoothEnergy_dense W)
  change morsePhysicalForm α w V U W - ⟪f, morseEnergyBase W⟫_ℝ = 0 at hW
  exact sub_eq_zero.mp hW

theorem morsePhysicalForm_pairing_iff_compactWeak (α w V : ℝ)
    (U : MorseWeakEnergy) (f : MorseL2) :
    (∀ W : MorseWeakEnergy,
      morsePhysicalForm α w V U W = ⟪f, morseEnergyBase W⟫_ℝ) ↔
      MorseCompactWeakEquation α w V (morseEnergyBase U) f := by
  constructor
  · intro h
    exact morseAssociatedGraph_compact_weak α w V (morseEnergyBase U) f ⟨U, rfl, h⟩
  · exact morsePhysicalForm_pairing_of_compactWeak α w V U f

/-- The actual graph and the actual compact-test differential equation
are equivalent for this fixed energy vector. -/
theorem morseAssociatedGraph_iff_compactWeak_of_energy (α w V : ℝ)
    (U : MorseWeakEnergy) (f : MorseL2) :
    (morseEnergyBase U, f) ∈ morseAssociatedGraph α w V ↔
      MorseCompactWeakEquation α w V (morseEnergyBase U) f := by
  constructor
  · exact morseAssociatedGraph_compact_weak α w V (morseEnergyBase U) f
  · intro h
    exact ⟨U, rfl, morsePhysicalForm_pairing_of_compactWeak α w V U f h⟩

/-- A version on L² in which the necessary energy-lift condition remains
explicit; no regularity assertion for arbitrary L² weak solutions is hidden. -/
theorem morseAssociatedGraph_iff_energy_compactWeak (α w V : ℝ) (u f : MorseL2) :
    (u, f) ∈ morseAssociatedGraph α w V ↔
      ∃ U : MorseWeakEnergy, morseEnergyBase U = u ∧
        MorseCompactWeakEquation α w V u f := by
  constructor
  · intro h
    have hw := morseAssociatedGraph_compact_weak α w V u f h
    rcases h with ⟨U, hU, _⟩
    exact ⟨U, hU, hw⟩
  · rintro ⟨U, hU, hweak⟩
    rw [← hU] at hweak ⊢
    exact (morseAssociatedGraph_iff_compactWeak_of_energy α w V U f).mpr hweak

end ContinuousFlexibility.Radial
