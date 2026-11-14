module

public import ContinuousFlexibility.Analysis.N01cMixedPowerBounds

/-!
# Choosing a common coefficient base through an opaque conclusion

The interpolation witness and its orderwise constants are selected on
an arbitrary seminormed real module. The conclusion is passed as a
predicate of the base and loss, so specialization to the actual state
space does not repeat the existential construction.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

/-- Select one interpolation base above the supplied geometric base,
then pass its complete spatial-power estimate to the continuation. -/
theorem exists_base_ge_of_spatialPower_continuation
    (p : ℕ → Seminorm ℝ X) (hp : Monotone p) (hinterp : HasInterpolation p)
    (originalBase offset : ℕ) (P : ℕ → ℕ → Prop)
    (hP : ∀ base loss : ℕ, originalBase ≤ base →
      (∀ s : ℕ, ∃ B : ℝ, 1 ≤ B ∧
        ∀ n : ℕ, n ≤ s → ∀ x : X, p base x ≤ 1 →
        ∀ R : ℝ, 1 ≤ R → p (s + loss) x ≤ R →
          p (n + offset) x ≤ B * R ^ ((n : ℝ) / ((s : ℝ) + 1))) →
      P base loss) :
    ∃ base loss : ℕ, originalBase ≤ base ∧ P base loss := by
  obtain ⟨b, loss, hI⟩ := exists_seminorm_spatialPower_bound p hp hinterp offset
  refine ⟨max originalBase b, loss, le_max_left _ _, ?_⟩
  apply hP (max originalBase b) loss (le_max_left _ _)
  intro s
  obtain ⟨B, hB, hb⟩ := hI s
  refine ⟨B, hB, fun n hn x hx R hR hh => ?_⟩
  exact hb n hn x (((hp (le_max_right originalBase b)) x).trans hx) R hR hh

end ContinuousFlexibility.Analysis
