module

public import ContinuousFlexibility.Radial.SeedConeTail

/-!
# A natural tail continued inward to an exact pure cone mode

The exponent is a real number with p²=4.  The signed amplitude is kept
explicit so subsequent rescaling and gluing use one power formula.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

structure SeedPureTail (D : ReferenceData) (right : Bool) (entry : ℝ) (u : ℝ → ℝ) where
  profile : ℝ → ℝ
  height : ℝ → ℝ
  profile_smooth : ContDiffOn ℝ ∞ profile (Ioi 0)
  height_smooth : ContDiffOn ℝ ∞ height (Ioi 0)
  outward_zero : ∀ r, (if right then D.b ≤ r else r ≤ D.a) →
    profile r = 0 ∧ height r = 0
  tail_eq : ∀ r ∈ radialTailInterval D right entry, profile r = D.w r ∧ height r = u r
  positive : ∀ r ∈ seedConeTailDomain D right, 0 < profile r
  inward_increasing : ∀ r, 0 < r → (if right then r ≤ entry else entry ≤ r) →
    0 < deriv profile r
  simple_critical : ∀ r ∈ seedConeTailDomain D right,
    deriv profile r = 0 → deriv (deriv profile) r ≠ 0
  homogeneous : ∀ r ∈ seedConeTailDomain D right, radialJacobi 4 profile height r = 0
  cut : ℝ
  cut_pos : 0 < cut
  cut_order : if right then cut < entry else entry < cut
  cone_scale : ℝ
  amplitude : ℝ
  mode : ℝ
  scale_pos : 0 < cone_scale
  amplitude_ne_zero : amplitude ≠ 0
  mode_sq : mode ^ 2 = 4
  pure_eq : ∀ r, 0 < r → (if right then r < cut else cut < r) →
    profile r = cone_scale * r ∧ height r = amplitude * r ^ mode

end ContinuousFlexibility.Radial
