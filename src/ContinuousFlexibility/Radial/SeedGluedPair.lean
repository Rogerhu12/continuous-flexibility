import ContinuousFlexibility.Radial.SeedCentralHeads
import ContinuousFlexibility.Radial.SeedPureTail
import ContinuousFlexibility.Radial.SeedThreePiece

/-!
# Data of the actual central seed joined to two selected tails

Every field records a property of the explicitly glued functions. The
construction is provided by `exists_seedGluedPair`; no new assumption is
added to the radial milestone.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter
open scoped Topology ContDiff
open Statements

structure SeedGluedPair (D : ReferenceData) (c d : ℝ) (uL uR : ℝ → ℝ)
    (K : SeedCentralCutoff) (q : ℝ) where
  profile : ℝ → ℝ
  height : ℝ → ℝ
  radiusL : ℝ
  radiusR : ℝ
  heightL : ℝ
  heightR : ℝ
  amplitudeL : ℝ
  amplitudeR : ℝ
  radiusL_pos : 0 < radiusL
  radius_order : radiusL ≤ radiusR
  heightL_pos : 0 < heightL
  heightR_pos : 0 < heightR
  amplitudeL_ne : amplitudeL ≠ 0
  amplitudeR_ne : amplitudeR ≠ 0
  geometry : RadialProfileGeometry
    { D with a := radiusL * D.a, b := radiusR * D.b, w := profile, phi := height }
  equation : ∀ r ∈ Ioo (radiusL * D.a) (radiusR * D.b),
    radialJacobi 4 profile height r = 0
  left_entry : radiusL * c < exp (K.left - q - 4)
  right_entry : exp (K.right + q + 4) < radiusR * d
  middle_germ : ∀ r ∈ Ioo (exp (K.left - q - 4)) (exp (K.right + q + 4)),
    profile =ᶠ[𝓝 r] K.profile ∧ height =ᶠ[𝓝 r] K.height
  left_tail : ∀ r ∈ Ioo D.a c,
    profile (radiusL * r) = heightL * radiusL * D.w r ∧
    height (radiusL * r) = amplitudeL * uL r
  right_tail : ∀ r ∈ Ioo d D.b,
    profile (radiusR * r) = heightR * radiusR * D.w r ∧
    height (radiusR * r) = amplitudeR * uR r

end ContinuousFlexibility.Radial
