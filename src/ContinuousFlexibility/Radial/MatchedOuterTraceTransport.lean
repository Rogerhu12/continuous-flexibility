import ContinuousFlexibility.Radial.MatchedOuterWithinReflection
import ContinuousFlexibility.Radial.OuterNormalizedState

/-!
# The frozen exterior flux and the actual outward Robin state

The same one-sided derivative at a regular cut can be computed in the
outward coordinate for an arbitrary representative. The square-root
normalization in the frozen matching row is exactly a nonzero multiple
of the Robin pairing for the first-order flux scaled by the boundary scale.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory Real
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

theorem matchedOuterFlux_outward {D : ReferenceData} {M : RadialMatchingData D}
    (ha : D.a < M.innerLeft) (hm : M.innerLeft < M.innerRight)
    (hb : M.innerRight < D.b) (right : Bool) (u : ℝ → ℝ) :
    matchingOuterFlux D M u (if right then 1 else 0) =
      D.w (if right then M.innerRight else M.innerLeft) *
        derivWithin (fun x => u (outerOutwardRadius right x))
          (Ico (outerOutwardRadius right (if right then M.innerRight else M.innerLeft))
            (outerOutwardRadius right (tailPhysicalEndpoint D right)))
          (outerOutwardRadius right (if right then M.innerRight else M.innerLeft)) /
        sqrt (M.boundaryScale (if right then 1 else 0)) := by
  have he : EqOn u (matchedOuterSideGlue M.innerLeft M.innerRight u u)
      (Ioc D.a M.innerLeft ∪ Ico M.innerRight D.b) := by
    rintro x (hx | hx)
    · exact (matchedOuterSideGlue_of_le u u hx.2).symm
    · exact (matchedOuterSideGlue_of_ge hm u u hx.1).symm
  cases right
  · exact (matchingOuterFlux_congr ha hm hb he 0).trans
      (matchedOuterSideGlue_flux_left ha hm hb u u)
  · exact (matchingOuterFlux_congr ha hm hb he 1).trans
      (matchedOuterSideGlue_flux_right ha hm hb u u)

theorem matchedOuterRobin_scale {lam A B x z : ℝ} (hlam : 0 < lam) :
    A * sqrt lam * x + B * (z / sqrt lam) =
      sqrt lam * (A * x + B * (z / lam)) := by
  let s : ℝ := sqrt lam
  have hs : s ≠ 0 := (sqrt_pos.mpr hlam).ne'
  have hls : lam = s ^ 2 := (sq_sqrt hlam.le).symm
  have hratio : s / lam = s⁻¹ := by
    rw [hls]
    field_simp [hs]
    ring
  change A * s * x + B * (z / s) = s * (A * x + B * (z / lam))
  calc
    A * s * x + B * (z / s) = s * (A * x) + s⁻¹ * (B * z) := by ring
    _ = s * (A * x) + (s / lam) * (B * z) := by rw [hratio]
    _ = s * (A * x + B * (z / lam)) := by ring

theorem matchedOuterRobin_scale_iff {lam A B x z : ℝ} (hlam : 0 < lam) :
    A * sqrt lam * x + B * (z / sqrt lam) = 0 ↔
      A * x + B * (z / lam) = 0 := by
  rw [matchedOuterRobin_scale hlam]
  exact mul_eq_zero.trans (or_iff_right (sqrt_pos.mpr hlam).ne')

theorem matchedOuter_boundary_outward_iff {D : ReferenceData} {M : RadialMatchingData D}
    (ha : D.a < M.innerLeft) (hm : M.innerLeft < M.innerRight)
    (hb : M.innerRight < D.b) (right : Bool) (u : ℝ → ℝ)
    (hlam : 0 < M.boundaryScale (if right then 1 else 0)) :
    (M.A (if right then 1 else 0) (if right then 1 else 0) *
        sqrt (M.boundaryScale (if right then 1 else 0)) *
        u (matchingCut D M (if right then 1 else 0)) +
      M.B (if right then 1 else 0) (if right then 1 else 0) *
        matchingOuterFlux D M u (if right then 1 else 0) = 0) ↔
    outerStatePair
      (M.A (if right then 1 else 0) (if right then 1 else 0),
        M.B (if right then 1 else 0) (if right then 1 else 0))
      (u (if right then M.innerRight else M.innerLeft),
        D.w (if right then M.innerRight else M.innerLeft) *
          derivWithin (fun x => u (outerOutwardRadius right x))
            (Ico (outerOutwardRadius right (if right then M.innerRight else M.innerLeft))
              (outerOutwardRadius right (tailPhysicalEndpoint D right)))
            (outerOutwardRadius right (if right then M.innerRight else M.innerLeft)) /
          M.boundaryScale (if right then 1 else 0)) = 0 := by
  rw [matchedOuterFlux_outward ha hm hb right u]
  have hcut : matchingCut D M (if right then 1 else 0) =
      (if right then M.innerRight else M.innerLeft) := by
    cases right <;> rfl
  rw [hcut]
  exact matchedOuterRobin_scale_iff hlam

end ContinuousFlexibility.Radial
