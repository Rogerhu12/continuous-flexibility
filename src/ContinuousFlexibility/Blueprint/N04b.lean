import ContinuousFlexibility.Blueprint.N04b.FieldRealization
import ContinuousFlexibility.Blueprint.N04b.CanonicalConstruction

/-!
# Blueprint node N04b

Assemble the actual smooth corrected field and its canonical construction.
The physical halves are the actual domains of the characteristic charts;
the canonical intervals and the cut transmission matrix are state independent.

This assembly has no local proof placeholder. The node remains open until
both genuine sub-statements are proved without additional axioms.
Source: paper/flexible-surface-readable/07-fixed-geometry.tex, lines 992--1303.
Task: docs/tasks/N04b.md.
-/

namespace ContinuousFlexibility.Blueprint

open ContinuousFlexibility.Statements

theorem N04b (hN04a : N04aStatement) : N04bStatement := by
  obtain ⟨A, T, S, C, R, L, base, loss, ε, hT, hS, h03, hfield⟩ :=
    N04bFieldRealization hN04a
  obtain ⟨K, hA, hB⟩ :=
    N04bCanonicalConstruction A T S C R L base loss ε hT hS h03 hfield
  exact ⟨A, T, S, C, R, L, K, base, loss, ε, hT, hS, h03, hA, hB⟩

end ContinuousFlexibility.Blueprint
