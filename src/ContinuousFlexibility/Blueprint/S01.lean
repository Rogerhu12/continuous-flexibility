module

public import ContinuousFlexibility.Statements.Milestones
public import ContinuousFlexibility.Scalar.Positivity
public import ContinuousFlexibility.Scalar.Coframe

/-!
# Blueprint node S01

Source: `paper/flexible-surface-rewrite/03-height-equation.tex` lines 13–24 (`eq:height-jet-notation`).

Task file: `docs/tasks/S01.md`. The statement is frozen. Proved.
-/

@[expose] public section

namespace ContinuousFlexibility.Blueprint

open ContinuousFlexibility ContinuousFlexibility.Statements

theorem S01 : S01Statement := by
  intro r E k p hr hE
  refine ⟨remainderPositive_iff_discriminant_pos hr hE,
    discriminant_pos_iff_height_norm_sq_lt_one hE, fun hD => ?_⟩
  exact ⟨radial_factor_pos_of_discriminant_pos hE hD,
    angular_factor_pos_of_discriminant_pos hE hD,
    fun x y => coframe_square_sum hE hD x y⟩

end ContinuousFlexibility.Blueprint
