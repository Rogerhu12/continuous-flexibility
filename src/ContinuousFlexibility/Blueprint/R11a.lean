module

public import ContinuousFlexibility.Blueprint.Statements
public import ContinuousFlexibility.Radial.R11aActualAssembly
public import Lean.Util.CollectAxioms

/-!
# Blueprint node R11a

The weighted bound of the actual matched inverse at the three exponents
on the same retained geometry.

Source: `paper/flexible-surface-readable/06-global-reference-inverse.tex` lines 850–1017.
Task file: `docs/tasks/R11a.md`.
-/

@[expose] public section

namespace ContinuousFlexibility.Blueprint

open ContinuousFlexibility.Statements

theorem R11a (hR05 : R05Statement) (hR10 : R10Statement) : R11aStatement := by
  exact ContinuousFlexibility.Radial.r11a_actual_assembly

end ContinuousFlexibility.Blueprint

open Lean in
run_cmd do
  let axioms ← collectAxioms ``ContinuousFlexibility.Blueprint.R11a
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in ContinuousFlexibility.Blueprint.R11a"

#print axioms ContinuousFlexibility.Blueprint.R11a
