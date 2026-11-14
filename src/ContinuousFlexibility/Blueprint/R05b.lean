module

public import ContinuousFlexibility.Blueprint.Statements
public import ContinuousFlexibility.Radial.MorseChainMassResistance

/-!
# Blueprint node R05b

Mass and resistance of every cell and join of a realized chain.

Source: `paper/flexible-surface-readable/05-flat-end-chain.tex` lines 323–472.

Task file: `docs/tasks/R05b.md`. The statement is unchanged. One baseline
realization controls the fixed radius charts; physical change of variables
and connector monotonicity give uniform bounds for every admissible height
choice, including the initial left interval with no connector.
-/

@[expose] public section

namespace ContinuousFlexibility.Blueprint

open ContinuousFlexibility.Statements

theorem R05b : R05bStatement := by
  intro T C family hfamily
  exact Radial.exists_morseChainMassResistanceConstants T C family hfamily

/--
info: 'ContinuousFlexibility.Blueprint.R05b' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms R05b

end ContinuousFlexibility.Blueprint
