import ContinuousFlexibility.Radial.BorderedCoreInverse
import ContinuousFlexibility.Radial.ModeCoreGraph

/-!
# From exact smooth-core inversion to the frozen modal inverse

The core is the concrete family of smooth modal inputs and their
differential sources. The inactive scalar is temporarily extended by the
identity, so that the same bounded-adjoint argument applies at every mode.
The conclusion is exactly ModeInverseProperties on the original space.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set
open scoped ContDiff InnerProductSpace
open ContinuousFlexibility.Statements

def matchingCoreRelation (D : ReferenceData) (hD : IsAccumulatingProfile D)
    (hB : RadialTrueBorder D) (j : ℕ) (U F : RadialModePair D) : Prop :=
  ∃ (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ),
    HasCompactSupport ψ ∧ Function.support ψ ⊆ radialCore D ∧
      ∃ s : ℝ, U = matchingTestInput D hD ψ hψ s ∧
        F = matchingTestSource D hD hB j ψ hψ s

theorem borderedPairing_eq_modePairing (D : ReferenceData) (U F : RadialModePair D) :
    borderedPairing U F = modePairing D U F := by
  simp only [borderedPairing, modePairing, RCLike.inner_apply, conj_trivial]
  ring

theorem matchingCoreAdjoint_iff_extended {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D)
    (j : ℕ) (U F : RadialModePair D) :
    BorderedCoreAdjoint (matchingCoreRelation D hD hB j) U F ↔
      ModeExtendedGraph D j U F := by
  rw [modeExtendedGraph_iff_core_pairings hD hB]
  constructor
  · intro h ψ hψ hc hs s
    have ht := h (matchingTestInput D hD ψ hψ s)
      (matchingTestSource D hD hB j ψ hψ s) ⟨ψ, hψ, hc, hs, s, rfl, rfl⟩
    simpa only [borderedPairing_eq_modePairing] using ht
  · intro h V H hVH
    rcases hVH with ⟨ψ, hψ, hc, hs, s, rfl, rfl⟩
    simpa only [borderedPairing_eq_modePairing] using h ψ hψ hc hs s

def matchingExtendedOperator {D : ReferenceData} (j : ℕ)
    (G : RadialModePair D →L[ℝ] RadialModePair D) :
    RadialModePair D →L[ℝ] RadialModePair D :=
  G + if j = 2 then 0 else
    (ContinuousLinearMap.inr ℝ (RadialModeL2 D) ℝ).comp
      (ContinuousLinearMap.snd ℝ (RadialModeL2 D) ℝ)

theorem matchingExtendedOperator_apply {D : ReferenceData} (j : ℕ)
    (G : RadialModePair D →L[ℝ] RadialModePair D) (F : RadialModePair D) :
    matchingExtendedOperator j G F = G F + (0, if j = 2 then 0 else F.2) := by
  by_cases hj : j = 2 <;>
    simp [matchingExtendedOperator, hj, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inr_apply]

theorem matchingExtendedOperator_eq_of_admissible {D : ReferenceData} (j : ℕ)
    (G : RadialModePair D →L[ℝ] RadialModePair D) (F : RadialModePair D)
    (hF : j ≠ 2 → F.2 = 0) : matchingExtendedOperator j G F = G F := by
  rw [matchingExtendedOperator_apply]
  by_cases hj : j = 2
  · simp only [if_pos hj, Prod.mk_zero_zero, add_zero]
  · simp only [if_neg hj, hF hj, Prod.mk_zero_zero, add_zero]

/-- The analytic obligations are exact homogeneous uniqueness and exact
left inversion on concrete differential test pairs. No surrogate graph
or weaker inverse property appears in the conclusion. -/
theorem modeInverseProperties_of_core_leftInverse {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D) (j : ℕ)
    (G : RadialModePair D →L[ℝ] RadialModePair D)
    (hkernel : ∀ U, ModeFullGraph D j U 0 → U = 0)
    (hleft : ∀ (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ),
      HasCompactSupport ψ → Function.support ψ ⊆ radialCore D → ∀ s : ℝ,
      matchingExtendedOperator j G (matchingTestSource D hD hB j ψ hψ s) =
        matchingTestInput D hD ψ hψ s) :
    ModeInverseProperties D j G := by
  have hsym (U F : RadialModePair D) (hUF : matchingCoreRelation D hD hB j U F) :
      BorderedCoreAdjoint (matchingCoreRelation D hD hB j) U F := by
    rcases hUF with ⟨ψ, hψ, hc, hs, s, rfl, rfl⟩
    apply (matchingCoreAdjoint_iff_extended hD hB j _ _).mpr
    exact matchingTestPair_mem_extendedGraph hD hB j ψ hψ s
  have hker (U : RadialModePair D)
      (hU : BorderedCoreAdjoint (matchingCoreRelation D hD hB j) U 0) : U = 0 := by
    apply hkernel U
    apply (modeFullGraph_iff_extended j U 0).mpr
    exact ⟨(matchingCoreAdjoint_iff_extended hD hB j U 0).mp hU, fun _ => rfl⟩
  have hleft' (U F : RadialModePair D) (hUF : matchingCoreRelation D hD hB j U F) :
      matchingExtendedOperator j G F = U := by
    rcases hUF with ⟨ψ, hψ, hc, hs, s, rfl, rfl⟩
    exact hleft ψ hψ hc hs s
  obtain ⟨hright, hunique, _⟩ :=
    bordered_inverse_of_core (matchingCoreRelation D hD hB j)
      (matchingExtendedOperator j G) hsym hker hleft'
  constructor
  · intro F hF
    apply (modeFullGraph_iff_extended j (G F) F).mpr
    refine ⟨?_, hF⟩
    have h := (matchingCoreAdjoint_iff_extended hD hB j _ F).mp (hright F)
    rw [matchingExtendedOperator_eq_of_admissible j G F hF] at h
    exact h
  · intro U F hUF
    obtain ⟨hU, hF⟩ := (modeFullGraph_iff_extended j U F).mp hUF
    have h := hunique U F ((matchingCoreAdjoint_iff_extended hD hB j U F).mpr hU)
    rw [matchingExtendedOperator_eq_of_admissible j G F hF] at h
    exact h

end ContinuousFlexibility.Radial
