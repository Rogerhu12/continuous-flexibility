module

public import ContinuousFlexibility.Blueprint.Statements
public import ContinuousFlexibility.Blueprint.N06.WeakGraph
public import ContinuousFlexibility.Blueprint.N06.CanonicalRelative
public import ContinuousFlexibility.Analysis.N06SmallNeighborhood

/-!
# Blueprint node N06

The perturbed operator as a relatively small perturbation on one Banach space.

Source: `paper/flexible-surface-readable/08-stable-inverse.tex` lines 256–489.

Task file: `docs/tasks/N06.md`. The exact statement is assembled from the
weak-graph and canonical-relative substatements. Completion requires both
substatements to have proofs with only the three standard logical axioms.
-/

@[expose] public section

namespace ContinuousFlexibility.Blueprint

open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

theorem N06 (hN05 : N05Statement) : N06Statement := by
  obtain ⟨A, T, S, C, R, L, K, V, b, B, base, loss, ε,
    hT, hS, hthrough, P, order, M, hM, hphysical, hbound⟩ :=
      N06CanonicalRelative hN05 N06WeakGraph
  obtain ⟨base', ε', Relative, _, _, _, hresult⟩ :=
    n06_exists_on_smaller_neighborhood hT hthrough P order M hM hphysical hbound
  exact ⟨A, T, S, C, R, L, K, V, b, B, Relative, base', loss, ε', hT, hS, hresult⟩

end ContinuousFlexibility.Blueprint

#print axioms ContinuousFlexibility.Blueprint.N06
