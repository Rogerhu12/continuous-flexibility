import ContinuousFlexibility.Radial.ReferenceGraphAlgebra

/-!
# Completion of the inverse from actual bounded solvability

A solution is chosen only after the genuine weak graph and its norm
bound have been proved for each source. Maximal-graph uniqueness forces
this choice to be linear modulo physical almost-everywhere equality.
This supplies exactly the inverse properties in the frozen statement.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

theorem boundedReferenceInverse_of_bounded_solvability {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D)
    {γ M₀ M₁ : ℝ} (hγ : 0 < γ)
    (hunique : ∀ U V : RadialUnknown, ∀ F : RadialSource,
      ReferenceGraph D γ M₀ M₁ U F → ReferenceGraph D γ M₀ M₁ V F →
        RadialRepresentativeEq D U V)
    (hsolve : ∃ C : ℝ, 0 < C ∧
      ∀ F : RadialSource, SourceMember D γ M₀ F →
        ∃ U : RadialUnknown, ∃ aL : ℝ,
          ReferenceGraph D γ M₀ M₁ U F ∧ OutputRealization D γ M₁ aL U ∧
            outputNormSquare D γ M₁ aL U ≤ C ^ 2 * sourceNormSquare D γ M₀ F) :
    BoundedReferenceInverse D γ M₀ M₁ := by
  classical
  obtain ⟨C, hC, hsolve⟩ := hsolve
  let G (F : RadialSource) : RadialUnknown :=
    if hF : SourceMember D γ M₀ F then (hsolve F hF).choose else 0
  have hGF (F : RadialSource) (hF : SourceMember D γ M₀ F) :
      ReferenceGraph D γ M₀ M₁ (G F) F := by
    dsimp only [G]
    rw [dif_pos hF]
    exact (hsolve F hF).choose_spec.choose_spec.1
  refine ⟨G, hGF, ?_, ?_, C, hC, ?_⟩
  · intro U F hUF
    exact hunique (G F) U F (hGF F hUF.2.1) hUF
  · intro F K hF hK c d
    have hinput : SourceMember D γ M₀ (c • F + d • K) :=
      (hF.smul c).add (Radial.matchingProfileGeometry hD).2.1.le
        hD.choose_spec.2.1 (hK.smul d)
    have hlinear : ReferenceGraph D γ M₀ M₁ (c • G F + d • G K) (c • F + d • K) :=
      ((hGF F hF).smul c).add hD hB hγ ((hGF K hK).smul d)
    exact hunique _ _ _ (hGF _ hinput) hlinear
  · intro F hF
    dsimp only [G]
    rw [dif_pos hF]
    exact ⟨(hsolve F hF).choose_spec.choose,
      (hsolve F hF).choose_spec.choose_spec.2⟩

/-- Once the actual modal inverses are known, only genuine bounded
solvability remains to construct the full inverse at any positive
attenuation. The threshold is chosen before the output exponent. -/
theorem exists_referenceInverse_solvability_threshold {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D)
    (hmode : ∀ j : ℕ, 2 ≤ j → Even j →
      ∃ G : RadialModePair D →L[ℝ] RadialModePair D,
        ModeInverseProperties D j G) :
    ∃ Mmin : ℝ, 0 < Mmin ∧
      ∀ γ : ℝ, 0 < γ → ∀ M₀ : ℝ, Mmin ≤ M₀ → ∀ M₁ : ℝ,
      (∃ C : ℝ, 0 < C ∧
        ∀ F : RadialSource, SourceMember D γ M₀ F →
          ∃ U : RadialUnknown, ∃ aL : ℝ,
            ReferenceGraph D γ M₀ M₁ U F ∧ OutputRealization D γ M₁ aL U ∧
              outputNormSquare D γ M₁ aL U ≤ C ^ 2 * sourceNormSquare D γ M₀ F) →
      BoundedReferenceInverse D γ M₀ M₁ := by
  obtain ⟨Mmin, hMmin, hunique⟩ := exists_referenceGraph_unique hD hB hmode
  refine ⟨Mmin, hMmin, ?_⟩
  intro γ hγ M₀ hM₀ M₁ hsolve
  exact boundedReferenceInverse_of_bounded_solvability hD hB hγ
    (hunique γ hγ M₀ hM₀ M₁) hsolve

end ContinuousFlexibility.Statements
