module

public import ContinuousFlexibility.Analysis.N05ReferenceLeftConstant

/-!
# One left constant for all positive reference exponents

The selected constant depends only on the physical output. Whenever that
output has any positive-weight realization, uniqueness identifies the
selection with its left constant. Every reference inverse estimate can
therefore use this same selection without changing its bound constant.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open ContinuousFlexibility.Statements

/-- Select from an actual positive-weight realization; use zero only when
no such realization exists. The choice has no exponent parameter. -/
def n05_referenceLeftConstant (D : ReferenceData) (U : RadialUnknown) : ℝ := by
  classical
  exact if h : ∃ a γ M : ℝ, 0 < γ ∧ OutputRealization D γ M a U
    then h.choose else 0

theorem n05_referenceLeftConstant_eq {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    {γ M a : ℝ} (hγ : 0 < γ) {U : RadialUnknown}
    (hU : OutputRealization D γ M a U) :
    n05_referenceLeftConstant D U = a := by
  classical
  have hex : ∃ a γ M : ℝ, 0 < γ ∧ OutputRealization D γ M a U :=
    ⟨a, γ, M, hγ, hU⟩
  rw [n05_referenceLeftConstant, dif_pos hex]
  obtain ⟨γ', M', hγ', hchosen⟩ := hex.choose_spec
  exact n05_outputRealization_leftConstant_unique hD hborder hγ' hγ hchosen hU

/-- For a fixed inverse function, every positive exponent uses the same
function `F ↦ n05_referenceLeftConstant D (G F)`. The estimate retains
the original constant for that exponent and the original coefficient loss. -/
theorem n05_referenceInverse_selectedLeftConstant {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    {γ M₀ M₁ : ℝ} (hγ : 0 < γ) {G : RadialSource → RadialUnknown}
    (hG : ReferenceInverseProperties D γ M₀ M₁ G) :
    ∃ C : ℝ, 0 < C ∧ ∀ F, SourceMember D γ M₀ F →
      OutputRealization D γ M₁ (n05_referenceLeftConstant D (G F)) (G F) ∧
        outputNormSquare D γ M₁ (n05_referenceLeftConstant D (G F)) (G F) ≤
          C ^ 2 * sourceNormSquare D γ M₀ F := by
  obtain ⟨C, hC, hbound⟩ := hG.2.2.2
  refine ⟨C, hC, fun F hF => ?_⟩
  obtain ⟨a, ha, hb⟩ := hbound F hF
  rw [n05_referenceLeftConstant_eq hD hborder hγ ha]
  exact ⟨ha, hb⟩

end ContinuousFlexibility.Radial
