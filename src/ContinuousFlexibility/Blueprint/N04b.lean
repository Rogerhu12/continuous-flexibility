module

public import ContinuousFlexibility.Blueprint.N04b.FieldRealization
public import ContinuousFlexibility.Blueprint.N04b.CanonicalConstruction

/-!
# Blueprint node N04b

Assemble the actual smooth corrected field and its canonical construction.
The physical halves are the actual domains of the characteristic charts;
the canonical intervals and the cut transmission matrix are state independent.

The two genuine sub-statements construct the field and its actual atlas.
The exact node axiom assertion below checks their full transitive closure.
Source: paper/flexible-surface-readable/07-fixed-geometry.tex, lines 992--1303.
Task: docs/tasks/N04b.md.
-/

@[expose] public section

namespace ContinuousFlexibility.Blueprint

open ContinuousFlexibility.Statements

theorem N04b (hN04a : N04aStatement) : N04bStatement := by
  obtain ⟨A, T, S, C, R, L, base, loss, ε, hT, hS, h03, hfield⟩ :=
    N04bFieldRealization hN04a
  obtain ⟨K, hA, hB⟩ :=
    N04bCanonicalConstruction A T S C R L base loss ε hT hS h03 hfield
  exact ⟨A, T, S, C, R, L, K, base, loss, ε, hT, hS, h03, hA, hB⟩

end ContinuousFlexibility.Blueprint

/--
info: 'ContinuousFlexibility.Blueprint.N04b' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ContinuousFlexibility.Blueprint.N04b

-- Emit the actual endpoint axiom sets in CI's full build-log artifact.
#print axioms ContinuousFlexibility.Blueprint.N04b
#print axioms ContinuousFlexibility.Blueprint.N04bFieldRealization
#print axioms ContinuousFlexibility.Blueprint.N04bCanonicalConstruction
