import ContinuousFlexibility.Analysis.N04NegativeInverseForwardClosure

/-!
# N04Coordinates-Realization, negative geometry: inverse chart

Given the chart and height atoms on the same neighborhood, prove the current jets of the atoms
`inverseRadial` and `inverseAngleDefect` and of the pulled height on negative pieces.

The statement is defined in
`src/ContinuousFlexibility/Analysis/N04RealizationLeadNegativeSplit.lean`.
Source: paper/flexible-surface-readable/07-fixed-geometry.tex, lines 1545-1678.
Task: docs/tasks/N04Realization-NegativeInverse.md.
-/

namespace ContinuousFlexibility.Blueprint

open ContinuousFlexibility.Analysis

theorem N04RealizationNegativeInverse : N04RealizationNegativeInverseObligation := by
  intro G b ε hadm hchart hheight
  obtain ⟨low, radius, hb, hadm', hradius, hsmall, hforward⟩ :=
    G.negativeInverse_forwardPrefixes hadm (hchart 0) (hheight 0)
  obtain ⟨hpoint, hheight⟩ :=
    G.negativeInverse_jointPrefixes_of_forward hadm' hsmall hforward
  exact ⟨low, radius, hb, hadm'.2.1, hradius,
    G.negativeInverse_collect_joint hadm' hsmall hpoint hheight⟩

end ContinuousFlexibility.Blueprint

/-- info: 'ContinuousFlexibility.Blueprint.N04RealizationNegativeInverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Blueprint.N04RealizationNegativeInverse
