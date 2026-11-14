module

public import ContinuousFlexibility.Analysis.N06WeakGraph

/-!
# N06: the maximal weak modal graph

Source: `paper/flexible-surface-readable/08-stable-inverse.tex` lines 256–318.
Task: `docs/tasks/N06-WeakGraph.md`.
-/

@[expose] public section

namespace ContinuousFlexibility.Blueprint

open ContinuousFlexibility.Statements

theorem N06WeakGraph : N06WeakGraphStatement :=
  ContinuousFlexibility.Analysis.n06_weakGraphStatement

end ContinuousFlexibility.Blueprint

/--
info: 'ContinuousFlexibility.Blueprint.N06WeakGraph' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ContinuousFlexibility.Blueprint.N06WeakGraph
