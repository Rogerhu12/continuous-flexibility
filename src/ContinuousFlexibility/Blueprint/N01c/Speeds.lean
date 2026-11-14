module

public import ContinuousFlexibility.Blueprint.N01c.Statements
public import ContinuousFlexibility.Analysis.N01cCharacteristicSpeedTameBounds

/-!
# N01c: quantitative characteristic speeds

The actual normalized drift, optical multiplier and optical square root
give all endpoint-weighted speed jets on one common neighbourhood.
The previously established coefficient clause and all primitive geometry
remain attached to the same witness.
Source: readable §7, Lemma `uniform-characteristic-flow-constants`, Step 1.
Task: `docs/tasks/N01c-Speeds.md`.
-/

@[expose] public section

namespace ContinuousFlexibility.Blueprint

open ContinuousFlexibility.Statements

theorem N01cSpeeds (hCoefficients : N01CoefficientStatement) : N01SpeedStatement := by
  obtain ⟨A, T, S, C, base, loss, ε, hT, hS, hA, hε, hB, hCoeff, hG, hE⟩ := hCoefficients
  obtain ⟨base', loss', ε', hε', _, _, _, hB', hCoeff', hSpeed⟩ :=
    n01_exists_common_characteristicSpeedTameBounds
      hS hT hA hε hB hCoeff hE hG.1 hG.2.1 hG.2.2
  exact ⟨A, T, S, C, base', loss', ε', hT, hS, hA, hε', hB', hCoeff', hSpeed, hG, hE⟩

end ContinuousFlexibility.Blueprint
