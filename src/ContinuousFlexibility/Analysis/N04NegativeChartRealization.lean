module

public import ContinuousFlexibility.Analysis.N04NegativeChartRootProjectedPrefix
public import ContinuousFlexibility.Analysis.N04NegativeChartRootValueData
public import ContinuousFlexibility.Analysis.N04NegativeChartCoverage

/-!
# Actual physical estimates for the negative chart

The retained optical factors supply both the full mixed root prefix and
its positive value band. Their scale is the same low-input choice. The
root and interior estimates then cover the complete reference half on
one parameter sector chosen before every derivative order.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis.N04RealizationStart

open Set ContinuousFlexibility.Statements NegativeOpticalFactors

set_option backward.isDefEq.respectTransparency true

attribute [local instance]
  interiorRaw_parameterTopology interiorRaw_parameterAddGroup interiorRaw_parameterSMul

/-- The physical chart bound has no additional analytic hypothesis.
All field, flow, positivity and overlap inputs come from the retained
realization data, and the selected half sample is unchanged. -/
theorem negativeChart_physical_positive_bounds (W : N04RealizationStart)
    (e : ℕ ≃ N04PieceIndex W.D) :
    ∃ base : ℕ, ∃ ε : ℝ, W.base ≤ base ∧ 0 < ε ∧
      ε ≤ min W.ε (1 / 2 : ℝ) ∧
      N04NegativeChartPhysicalPositiveBounds W e base ε := by
  let F : W.NegativeOpticalFactors e :=
    Classical.choice (W.negativeOpticalFactors_nonempty e)
  have hQ := F.fullHalfFields_powerControl
  let sourceBase := hQ.choose
  let loss := hQ.choose_spec.choose
  let Q : F.FullHalfFieldPowerControl sourceBase loss :=
    Classical.choice hQ.choose_spec.choose_spec.2
  let P : RootProjectedPrefixData Q :=
    Classical.choice Q.rootProjectedPrefix_nonempty
  let V : RootValueData W e P.base P.ε Q.rootCompositionScaleCoefficient :=
    Classical.choice (Q.root_valueData P.base_le P.lowBase_le
      P.ε_pos P.ε_half P.ε_low)
  have hεW : P.ε ≤ W.ε :=
    (P.ε_half.trans (min_le_left _ _)).trans (by linarith only [W.ε_pos])
  let A : RootCoordinatePrefixData W e P.base P.ε
      Q.rootCompositionScaleCoefficient V.σ := {
    base_le := P.base_le
    ε_pos := P.ε_pos
    ε_le := hεW
    ε_small := P.ε_half.trans (min_le_right _ _)
    scale := P.scale
    band := V.band
    values := V.values
    «prefix» := by
      intro K hK
      have hprefix := P.«prefix» K hK
      refine ⟨hprefix.choose, fun s => ?_⟩
      have hs := hprefix.choose_spec s
      refine ⟨hs.choose, hs.choose_spec.1, fun m side odd q hq => ?_⟩
      exact hs.choose_spec.2 m side odd q ⟨hq.1, hq.2.trans (V.band m side).2⟩ }
  exact A.physical_coverage V.overlap_material

end ContinuousFlexibility.Analysis.N04RealizationStart

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationStart.negativeChart_physical_positive_bounds'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationStart.negativeChart_physical_positive_bounds
