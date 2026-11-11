import ContinuousFlexibility.Blueprint.Statements
import ContinuousFlexibility.Radial.R11bFirstNormal
import ContinuousFlexibility.Radial.R11bMaximumGraphUniqueness

/-!
# Blueprint node R11b

The first normal estimate for the same inverse.

Source: `paper/flexible-surface-readable/06-global-reference-inverse.tex` lines 850–1017.

Task file: `docs/tasks/R11b.md`.
-/

namespace ContinuousFlexibility.Blueprint

open ContinuousFlexibility.Statements ContinuousFlexibility.Radial

theorem R11b (hR11a : R11aStatement) : R11Statement := by
  obtain ⟨D, hD, hborder, ε, M₀, M₁, hε, hεquarter, G, hmatchedModes, hG⟩ := hR11a
  have hmodes : ∀ j : ℕ, 2 ≤ j → Even j →
      ∃ H : RadialModePair D →L[ℝ] RadialModePair D, ModeInverseProperties D j H := by
    intro j hj he
    obtain ⟨H, hH, _⟩ := hmatchedModes j hj he
    exact ⟨H, hH⟩
  obtain ⟨H₂, _, M₂, _, hMatch₂⟩ := hmatchedModes 2 le_rfl (by decide)
  obtain ⟨L, hL, hnormal⟩ :=
    r11b_firstNormalInverseEstimate hD hborder M₀ M₁ hmodes ⟨H₂, M₂, hMatch₂⟩
  refine ⟨D, hD, hborder, ε, M₀, M₁ + L, hε, hεquarter, G, hmatchedModes, ?_⟩
  intro γ hγ
  have hγpos : 0 < γ := by
    rcases hγ with rfl | rfl | rfl <;> unfold referenceBeta <;> linarith
  have hγabs : |γ| ≤ 1 := by
    rw [abs_of_pos hγpos]
    rcases hγ with rfl | rfl | rfl <;> unfold referenceBeta <;> linarith
  exact ⟨r11b_referenceInverse_enlarge hD hborder hmodes hγpos le_rfl
      (le_add_of_nonneg_right hL) (hG γ hγ),
    hnormal γ hγpos hγabs G (hG γ hγ)⟩

#print axioms ContinuousFlexibility.Blueprint.R11b

end ContinuousFlexibility.Blueprint
