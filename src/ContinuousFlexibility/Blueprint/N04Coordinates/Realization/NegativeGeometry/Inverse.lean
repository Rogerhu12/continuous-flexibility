module

public import ContinuousFlexibility.Analysis.N04NegativeInverseForwardClosure
public import ContinuousFlexibility.Analysis.N04NegativeInverseJointCollector

/-!
# N04Coordinates-Realization, negative geometry: inverse chart

Given the chart and height atoms on the same neighborhood, prove the current jets of the atoms
`inverseRadial` and `inverseAngleDefect` and of the pulled height on negative pieces.

The statement is defined in
`src/ContinuousFlexibility/Analysis/N04RealizationLeadNegativeSplit.lean`.
Source: paper/flexible-surface-readable/07-fixed-geometry.tex, lines 1545-1678.
Task: docs/tasks/N04Realization-NegativeInverse.md.
-/

@[expose] public section

namespace ContinuousFlexibility.Blueprint

open ContinuousFlexibility.Analysis

theorem N04RealizationNegativeInverse : N04RealizationNegativeInverseObligation := by
  intro G b ε hadm hchart hheight
  let data := G.negativeInverse_forwardPrefixes hadm (hchart 0) (hheight 0)
  let low : ℕ := data.choose
  let radius : ℝ := data.choose_spec.choose
  have hb : b ≤ low := data.choose_spec.choose_spec.1
  let hadm' : G.Admissible low radius := data.choose_spec.choose_spec.2.choose
  let spec := data.choose_spec.choose_spec.2.choose_spec
  have estimates := G.negativeInverse_jointPrefixes_of_forward hadm' spec.2.1 spec.2.2
  exact ⟨low, radius, hb, hadm'.2.1, spec.1,
    G.negativeInverse_collect_joint hadm' spec.2.1 estimates.1 estimates.2⟩

end ContinuousFlexibility.Blueprint

/-- info: 'ContinuousFlexibility.Blueprint.N04RealizationNegativeInverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Blueprint.N04RealizationNegativeInverse
