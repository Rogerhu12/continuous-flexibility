import ContinuousFlexibility.Analysis.N04NegativeHeightProof

/-!
# N04Coordinates-Realization, negative geometry: height

Prove the current jets of the atoms `height` and `heightInverse` on negative pieces.

The statement is defined in
`src/ContinuousFlexibility/Analysis/N04RealizationLeadNegativeSplit.lean`.
Source: paper/flexible-surface-readable/07-fixed-geometry.tex, lines 1545-1678.
Task: docs/tasks/N04Realization-NegativeHeight.md.
-/

namespace ContinuousFlexibility.Blueprint

open ContinuousFlexibility.Analysis

theorem N04RealizationNegativeHeight : N04RealizationNegativeHeightObligation :=
  n04Realization_negativeHeight

end ContinuousFlexibility.Blueprint

/-- info: 'ContinuousFlexibility.Blueprint.N04RealizationNegativeHeight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Blueprint.N04RealizationNegativeHeight
