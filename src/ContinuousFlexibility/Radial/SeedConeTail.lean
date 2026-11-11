import ContinuousFlexibility.Statements.RadialTargets
import ContinuousFlexibility.Radial.SeedRadialContinuation

/-!
# A natural tail continued inward to an exact cone

The one-sided domain includes the entire inward ray. The original tail and
its outward flat endpoint are retained exactly.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

def seedConeTailDomain (D : ReferenceData) (right : Bool) : Set ℝ :=
  if right then Ioo 0 D.b else Ioi D.a

structure SeedConeTail (D : ReferenceData) (right : Bool) (entry : ℝ) (u : ℝ → ℝ) where
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
  coneA : ℝ
  coneB : ℝ
  scale_pos : 0 < cone_scale
  coeff_ne_zero : (coneA, coneB) ≠ (0, 0)
  cone_eq : ∀ r, 0 < r → (if right then r < cut else cut < r) →
    profile r = cone_scale * r ∧ height r = coneA * r ^ 2 + coneB / r ^ 2

end ContinuousFlexibility.Radial
