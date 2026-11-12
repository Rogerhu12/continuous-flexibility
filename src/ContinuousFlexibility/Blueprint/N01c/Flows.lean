import ContinuousFlexibility.Analysis.N01cOrdinaryFlowBounds

/-!
# N01c: variations of the ordinary flows

The actual angular and radial variations satisfy their estimates on one
common neighborhood. The coefficient estimate and the geometric clauses
restrict to that same neighborhood, yielding the complete N01 package.
-/

namespace ContinuousFlexibility.Blueprint

open ContinuousFlexibility.Statements

theorem N01cFlows (hSpeeds : N01SpeedStatement) : N01Statement := by
  obtain ⟨A, T, S, C, base, loss, ε, hT, hS, hA, hε, hB,
    hCoefficients, hSpeed, hG, hE⟩ := hSpeeds
  obtain ⟨base', ε', hb, hε', hε'ε, hFlows⟩ :=
    n01_exists_ordinaryFlowFamilyTameBounds hS hT hA hε hB hG hE hSpeed
  exact ⟨A, T, S, C, base', loss, ε', hT, hS,
    n01Properties_of_parts hA hε' (n01PartB_mono hB hb hε'ε)
      (coefficientFamilyTameBounds_mono_of_accumulatingProfile hT hA.1.1
        hCoefficients hb le_rfl hε'ε) hFlows⟩

end ContinuousFlexibility.Blueprint
