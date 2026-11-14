import ContinuousFlexibility.Analysis.N04RealizationLeadNegativeSplit
import ContinuousFlexibility.Analysis.N04NegativeChartRealization
import ContinuousFlexibility.Analysis.N04NegativeChartAssembly

/-!
# N04Coordinates-Realization, negative geometry: forward chart

Prove the current jets of the chart atoms `chartRadial`, `chartAngleDefect`, `jacobian` and
`jacobianInverse` on negative pieces.

The statement is defined in
`src/ContinuousFlexibility/Analysis/N04RealizationLeadNegativeSplit.lean`.
Source: paper/flexible-surface-readable/07-fixed-geometry.tex, lines 1545-1678.
Task: docs/tasks/N04Realization-NegativeChart.md.
-/

namespace ContinuousFlexibility.Blueprint

open ContinuousFlexibility.Analysis

theorem N04RealizationNegativeChart : N04RealizationNegativeChartObligation := by
  intro G b ε hadm
  have hex := G.W.negativeChart_physical_positive_bounds G.X.e₀
  let b₀ := hex.choose
  let ε₀ := hex.choose_spec.choose
  have hs := hex.choose_spec.choose_spec
  let b₁ := max b b₀
  let ε₁ := min ε ε₀
  have hb₁ : G.W.base ≤ b₁ := hs.1.trans (le_max_right _ _)
  have hε₁ : 0 < ε₁ := lt_min hadm.2.1 hs.2.1
  have hε₁W : ε₁ ≤ G.W.ε :=
    (min_le_right _ _).trans (hs.2.2.1.trans (min_le_left _ _))
  have hε₁half : ε₁ ≤ 1 / 2 :=
    (min_le_right _ _).trans (hs.2.2.1.trans (min_le_right _ _))
  have hphysical : N04NegativeChartPhysicalPositiveBounds G.W G.X.e₀ b₁ ε₁ :=
    hs.2.2.2.mono hs.1 (hs.2.2.1.trans (min_le_left _ _))
      (le_max_right b b₀) (min_le_right ε ε₀)
  have hdata := G.negativeChart_data_of_physical_bounds hb₁ hε₁ hε₁W hε₁half hphysical
  let b₂ := hdata.choose
  let ε₂ := hdata.choose_spec.choose
  have hd := hdata.choose_spec.choose_spec
  exact ⟨b₂, ε₂, (le_max_left _ _).trans hd.1, hd.2.1,
    hd.2.2.1.trans (min_le_left _ _), hd.2.2.2⟩

end ContinuousFlexibility.Blueprint

/-- info: 'ContinuousFlexibility.Blueprint.N04RealizationNegativeChart'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Blueprint.N04RealizationNegativeChart
