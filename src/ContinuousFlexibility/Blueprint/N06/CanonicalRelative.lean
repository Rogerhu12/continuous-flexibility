module

public import ContinuousFlexibility.Statements.N06Parts
public import ContinuousFlexibility.Analysis.N06PrimitiveCanonicalRelative

/-!
# N06: the actual canonical relative operator

Source: `paper/flexible-surface-readable/08-stable-inverse.tex` lines 319–489,
using the controlled coordinates of section 7 on the same N05 construction.
Task: `docs/tasks/N06-CanonicalRelative.md`.
-/

@[expose] public section

namespace ContinuousFlexibility.Blueprint

open ContinuousFlexibility.Statements

theorem N06CanonicalRelative (hN05 : N05Statement)
    (hgraph : N06WeakGraphStatement) : N06CanonicalRelativeStatement := by
  obtain ⟨A, T, S, C, R, L, K, V, b, B, base, loss, ε,
    hT, hS, hThrough05⟩ := hN05
  exact ⟨A, T, S, C, R, L, K, V, b, B, base, loss, ε,
    hT, hS, hThrough05,
    n06_exists_canonicalRelative_of_primitiveGeometry hT hS hThrough05
      hThrough05.1.2.2.2.2.2.1⟩

end ContinuousFlexibility.Blueprint
