import ContinuousFlexibility.Blueprint.Statements
import ContinuousFlexibility.Radial.DeepTailPhysicalBounds

/-!
# The physical part of the R06 pipeline

Shrinking the smallness threshold and increasing the depth threshold
preserve the full operator conclusion. Its actual natural line then gives
physical flatness, while the source identity follows from the same
physical coordinate relation.
-/

namespace ContinuousFlexibility.Blueprint

open ContinuousFlexibility.Statements ContinuousFlexibility.Radial

theorem r06Full_mono {C η K η' K' : ℝ} (h : R06Full C η K)
    (hη : η' ≤ η) (hK : K ≤ K') : R06Full C η' K' := by
  intro T hT hsmall hlarge
  exact h T hT (hsmall.trans hη) (hK.trans hlarge)

/-- The exact original-radius conclusion, including its source identity,
is a consequence of the full natural-line hypothesis. -/
theorem r06Physical_of_r06Full {C η K : ℝ} (h : R06Full C η K)
    (hη : η ≤ 1 / 2) : R06Physical η K := by
  intro D T right j start hD hT hsmall hlarge hphysical
  obtain ⟨_, _, G, _, _, _, _, hline, _⟩ := h T hT hsmall hlarge
  exact ⟨tailPhysicalFlatConclusion_of_natural_line hD hT hphysical
    (hsmall.trans hη) hline, tailPhysicalSourceIdentity_of_relation hD hphysical⟩

end ContinuousFlexibility.Blueprint
