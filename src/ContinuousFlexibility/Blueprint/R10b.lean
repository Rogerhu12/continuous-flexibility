module

public import ContinuousFlexibility.Radial.MatchingInverseTheorem

/-!
# Blueprint node R10b

Inversion of the matching matrix and the exact matched inverse.

Source: `paper/flexible-surface-readable/06-global-reference-inverse.tex` lines 776–850.
Task file: `docs/tasks/R10b.md`.
-/

@[expose] public section

namespace ContinuousFlexibility.Blueprint

open ContinuousFlexibility.Statements
open ContinuousFlexibility.Radial

theorem R10b : R10bStatement := by
  intro D hD hB j _hj _heven M hfrequency hM
  obtain ⟨G, M', hfreq, hactual⟩ :=
    MatchedPieces.exists_actualMatchedRepresentation D M hM
  have hfreq' : M'.frequency = j := hfreq.trans hfrequency
  refine ⟨G, ?_, M', hfreq', hactual⟩
  simpa only [hfreq'] using
    actualMatchedRepresentation_modeInverseProperties hD hB hactual

#print axioms ContinuousFlexibility.Blueprint.R10b

end ContinuousFlexibility.Blueprint
