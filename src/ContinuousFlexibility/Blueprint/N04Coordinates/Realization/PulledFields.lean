import ContinuousFlexibility.Analysis.N04PulledFieldsClosure

/-!
# N04Coordinates-Realization: pulled fields

Given the geometry interface and its same-atlas reference jets, the actual
physical coefficient and column constructions prove their pulled current
jets on all pieces and on one common neighborhood.

The statement is defined in
`src/ContinuousFlexibility/Analysis/N04RealizationLeadCurrentSplit.lean`.
Source: paper/flexible-surface-readable/07-fixed-geometry.tex, lines 1700-1717 (Step 5 of the current geometric jets lemma).
Task: docs/tasks/N04Realization-PulledFields.md.
-/

namespace ContinuousFlexibility.Blueprint

open ContinuousFlexibility.Analysis

theorem N04RealizationPulledFields : N04RealizationPulledFieldObligation := by
  exact n04PulledFields_obligation

end ContinuousFlexibility.Blueprint
