module

public import ContinuousFlexibility.Blueprint.Statements
public import ContinuousFlexibility.Radial.TailDeepInverse

/-!
# Blueprint node R06a

Deep tail: identification of the Friedrichs form, the inverse with norm C/Λ, and convergence of the Dirichlet truncations.

Source: `paper/flexible-surface-readable/05-flat-end-chain.tex` lines 472–725.

Task file: `docs/tasks/R06a.md`. The full operator construction is in
`Radial.TailDeepInverse`; the compact-test correction is recorded in `docs/STATUS.md`.
-/

@[expose] public section

namespace ContinuousFlexibility.Blueprint

open ContinuousFlexibility.Statements

theorem R06a : R06aStatement := by
  refine ⟨4, 1 / 10, 10 * ContinuousFlexibility.Radial.tailSmoothStepConstant + 2,
    by norm_num, by norm_num, by norm_num, ?_, ContinuousFlexibility.Radial.deepTail_operator⟩
  have h := ContinuousFlexibility.Radial.tailSmoothStepConstant_pos
  linarith

end ContinuousFlexibility.Blueprint
