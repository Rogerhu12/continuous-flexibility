import ContinuousFlexibility.Radial.TerminalPhysicalCutoff

/-!
# Closed supports of the actual terminal cutoffs

The transition layers determine the full closed value supports, not only
the derivative supports. Two ordered layers therefore give disjoint
cutoffs, and a central column between the layers is disjoint from both.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter Real
open scoped Topology ContDiff

theorem terminalPhysicalCutoff_tsupport (rising : Bool) {a b : ℝ} (hab : a < b) :
    tsupport (terminalPhysicalCutoff rising a b) ⊆
      if rising then Ici a else Iic b := by
  cases rising
  · apply closure_minimal _ isClosed_Iic
    exact (terminalPhysicalCutoff_support false hab).trans (fun _ hx => hx.le)
  · apply closure_minimal _ isClosed_Ici
    exact (terminalPhysicalCutoff_support true hab).trans (fun _ hx => hx.le)

theorem terminalPhysicalCutoffs_disjoint {a b c d : ℝ}
    (hab : a < b) (hbc : b < c) (hcd : c < d) :
    Disjoint (tsupport (terminalPhysicalCutoff false a b))
      (tsupport (terminalPhysicalCutoff true c d)) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hl : x ≤ b := terminalPhysicalCutoff_tsupport false hab hx
  have hr : c ≤ x := terminalPhysicalCutoff_tsupport true hcd hy
  exact (not_le_of_gt hbc) (hr.trans hl)

theorem terminalPhysicalCutoffs_column_disjoint {a b c d : ℝ} {g : ℝ → ℝ}
    (hab : a < b) (hcd : c < d) (hg : tsupport g ⊆ Ioo b c) :
    Disjoint (tsupport g) (tsupport (terminalPhysicalCutoff false a b)) ∧
      Disjoint (tsupport g) (tsupport (terminalPhysicalCutoff true c d)) := by
  constructor
  · apply Set.disjoint_left.mpr
    intro x hx hy
    exact (not_le_of_gt (hg hx).1) (terminalPhysicalCutoff_tsupport false hab hy)
  · apply Set.disjoint_left.mpr
    intro x hx hy
    exact (not_le_of_gt (hg hx).2) (terminalPhysicalCutoff_tsupport true hcd hy)

end ContinuousFlexibility.Radial
