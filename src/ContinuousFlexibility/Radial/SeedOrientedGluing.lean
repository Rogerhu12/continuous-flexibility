module

public import ContinuousFlexibility.Radial.SeedPairGluing

/-! # Gluing toward either radial endpoint -/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter
open scoped Topology ContDiff

def seedOrientedGlue (right : Bool) (c : ℝ) (inside outside : ℝ → ℝ) : ℝ → ℝ :=
  if right then morseGlueCut c inside outside else morseGlueCut c outside inside

theorem seedOrientedGlue_inward_germ {right : Bool} {c r : ℝ} {inside outside : ℝ → ℝ}
    (h : inside =ᶠ[𝓝 c] outside) (hr : if right then r ≤ c else c ≤ r) :
    seedOrientedGlue right c inside outside =ᶠ[𝓝 r] inside := by
  cases right with
  | false => exact morseGlueCut_eventually_right h.symm hr
  | true => exact morseGlueCut_eventually_left h hr

theorem seedOrientedGlue_outward_germ {right : Bool} {c r : ℝ} {inside outside : ℝ → ℝ}
    (h : inside =ᶠ[𝓝 c] outside) (hr : if right then c ≤ r else r ≤ c) :
    seedOrientedGlue right c inside outside =ᶠ[𝓝 r] outside := by
  cases right with
  | false => exact morseGlueCut_eventually_left h.symm hr
  | true => exact morseGlueCut_eventually_right h hr

theorem contDiffOn_seedOrientedGlue {right : Bool} {c : ℝ} {inside outside : ℝ → ℝ}
    (hi : ContDiffOn ℝ ∞ inside (Ioi 0)) (ho : ContDiffOn ℝ ∞ outside (Ioi 0))
    (h : inside =ᶠ[𝓝 c] outside) :
    ContDiffOn ℝ ∞ (seedOrientedGlue right c inside outside) (Ioi 0) := by
  cases right with
  | false => exact contDiffOn_morseGlueCut_positive ho hi h.symm
  | true => exact contDiffOn_morseGlueCut_positive hi ho h

theorem seedOrientedGlue_sides (right : Bool) (c r : ℝ) :
    (if right then r ≤ c else c ≤ r) ∨ (if right then c ≤ r else r ≤ c) := by
  cases right <;> exact le_total _ _

end ContinuousFlexibility.Radial
