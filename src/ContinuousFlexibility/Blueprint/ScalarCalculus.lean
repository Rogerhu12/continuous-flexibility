module

public import ContinuousFlexibility.Blueprint.Statements
public import ContinuousFlexibility.Scalar.S03CalculusProof
public import ContinuousFlexibility.Scalar.S04CalculusProof
public import ContinuousFlexibility.Scalar.S05CalculusProof

/-!
# Blueprint node ScalarCalculus

The pointwise and finite-rectangle calculus of the height equation: connection, residual, conservation, type correction.

Source: `paper/flexible-surface-readable/03-height-equation.tex` lines 23–189 and 406–543.

Task file: `docs/tasks/ScalarCalculus.md`. The statement is frozen.
-/

@[expose] public section

namespace ContinuousFlexibility.Blueprint

open ContinuousFlexibility.Statements

theorem ScalarCalculus : S03CalculusStatement ∧ S04CalculusStatement ∧ S05CalculusStatement := by
  exact ⟨s03CalculusStatement, s04CalculusStatement, s05CalculusStatement⟩

#print axioms ScalarCalculus

end ContinuousFlexibility.Blueprint
