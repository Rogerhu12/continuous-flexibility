import ContinuousFlexibility.Radial.MatchedOuterSeparatedInverse
import ContinuousFlexibility.Radial.MatchedOuterModalCells

/-!
# The whole-tail bounds apply to the actual global modal localizers

Restriction and extension intertwine the original localizers.  Their
norms are respectively contractive and isometric, so the localized
whole inverse controls the same physical side inverse without a density
or coordinate loss. The two sides are then added in the existing
separated inverse.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements

theorem matchedOuterWholeRestrict_cell
    (D : ReferenceData) (hP : RadialPartition D) (right : Bool) (entry : ℝ)
    (m : ℕ) (f : RadialModeL2 D) :
    matchedOuterWholeRestrict D right entry (matchedModeCellL2 D hP m f) =
      matchedOuterCell D hP right (outerWholeMeasure D right entry) m
        (matchedOuterWholeRestrict D right entry f) := by
  apply Lp.ext
  apply (measurableEmbedding_outerOutwardRadius right).ae_map_iff.mpr
  have hc := (measurableEmbedding_outerOutwardRadius right).ae_map_iff.mp
    (matchedOuterCell_ae D hP right (outerWholeMeasure D right entry) m
      (matchedOuterWholeRestrict D right entry f))
  filter_upwards [
    matchedOuterWholeRestrict_ae D right entry (matchedModeCellL2 D hP m f),
    (matchedModeCellL2_ae D hP m f).restrict,
    matchedOuterWholeRestrict_ae D right entry f, hc] with r hleft hmul hf hright
  rw [← hleft, hmul, hright, outerOutwardRadius_twice, ← hf]

theorem matchedOuterWholeExtend_cell
    (D : ReferenceData) (hP : RadialPartition D) (right : Bool) (entry : ℝ)
    (m : ℕ) (f : OuterWholeL2 D right entry) :
    matchedModeCellL2 D hP m (matchedOuterWholeExtend D right entry f) =
      matchedOuterWholeExtend D right entry
        (matchedOuterCell D hP right (outerWholeMeasure D right entry) m f) := by
  apply Lp.ext
  have hc := (measurableEmbedding_outerOutwardRadius right).ae_map_iff.mp
    (matchedOuterCell_ae D hP right (outerWholeMeasure D right entry) m f)
  filter_upwards [
    matchedModeCellL2_ae D hP m (matchedOuterWholeExtend D right entry f),
    matchedOuterWholeExtend_ae D right entry f,
    matchedOuterWholeExtend_ae D right entry
      (matchedOuterCell D hP right (outerWholeMeasure D right entry) m f),
    ae_imp_of_ae_restrict hc] with r hmul hf hright hc
  rw [hmul, hf, hright]
  by_cases hr : r ∈ radialTailInterval D right entry
  · rw [indicator_of_mem hr, indicator_of_mem hr, hc hr, outerOutwardRadius_twice]
  · rw [indicator_of_notMem hr, indicator_of_notMem hr, mul_zero]

theorem norm_matchedOuterWholeExtend_cell
    (D : ReferenceData) (hP : RadialPartition D) (right : Bool) (entry : ℝ)
    (m : ℕ) (f : OuterWholeL2 D right entry) :
    ‖matchedModeCellL2 D hP m (matchedOuterWholeExtend D right entry f)‖ =
      ‖matchedOuterCell D hP right (outerWholeMeasure D right entry) m f‖ := by
  rw [matchedOuterWholeExtend_cell, norm_matchedOuterWholeExtend_apply]

theorem norm_matchedOuterSideInverse_cells_le
    (D : ReferenceData) (hP : RadialPartition D) (right : Bool) (entry : ℝ)
    (R : OuterWholeL2 D right entry →L[ℝ] OuterWholeL2 D right entry) (k m : ℕ) :
    ‖(matchedModeCellL2 D hP k).comp
        ((matchedOuterSideInverse D right entry R).comp (matchedModeCellL2 D hP m))‖ ≤
      ‖(matchedOuterCell D hP right (outerWholeMeasure D right entry) k).comp
        (R.comp (matchedOuterCell D hP right (outerWholeMeasure D right entry) m))‖ := by
  let B := (matchedOuterCell D hP right (outerWholeMeasure D right entry) k).comp
    (R.comp (matchedOuterCell D hP right (outerWholeMeasure D right entry) m))
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg B)
  intro f
  simp only [ContinuousLinearMap.comp_apply, matchedOuterSideInverse_apply]
  rw [matchedOuterWholeExtend_cell, matchedOuterWholeRestrict_cell,
    norm_matchedOuterWholeExtend_apply]
  exact (B.le_opNorm (matchedOuterWholeRestrict D right entry f)).trans
    (mul_le_mul_of_nonneg_left
      (norm_matchedOuterWholeRestrict_apply_le D right entry f) (norm_nonneg B))

/-- This estimate is for the original pair operator, including its actual
zero scalar component, with the original global field cell maps. -/
theorem norm_matchedOuterSeparatedInverse_cells_le
    (D : ReferenceData) (hP : RadialPartition D) (cut : Bool → ℝ)
    (R : ∀ side, OuterWholeL2 D side (cut side) →L[ℝ] OuterWholeL2 D side (cut side))
    (k m : ℕ) :
    ‖(matchedModeCell D hP k).comp
        ((matchedOuterSeparatedInverse D cut R).comp (matchedModeCell D hP m))‖ ≤
      ‖(matchedOuterCell D hP false (outerWholeMeasure D false (cut false)) k).comp
        ((R false).comp (matchedOuterCell D hP false
          (outerWholeMeasure D false (cut false)) m))‖ +
      ‖(matchedOuterCell D hP true (outerWholeMeasure D true (cut true)) k).comp
        ((R true).comp (matchedOuterCell D hP true
          (outerWholeMeasure D true (cut true)) m))‖ := by
  let B (side : Bool) := (matchedOuterCell D hP side
    (outerWholeMeasure D side (cut side)) k).comp
      ((R side).comp (matchedOuterCell D hP side
        (outerWholeMeasure D side (cut side)) m))
  have hside (side : Bool) (f : RadialModeL2 D) :
      ‖matchedModeCellL2 D hP k
        (matchedOuterSideInverse D side (cut side) (R side)
          (matchedModeCellL2 D hP m f))‖ ≤ ‖B side‖ * ‖f‖ := by
    let A := (matchedModeCellL2 D hP k).comp
      ((matchedOuterSideInverse D side (cut side) (R side)).comp (matchedModeCellL2 D hP m))
    exact (A.le_opNorm f).trans
      (mul_le_mul_of_nonneg_right
        (norm_matchedOuterSideInverse_cells_le D hP side (cut side) (R side) k m)
        (norm_nonneg f))
  apply ContinuousLinearMap.opNorm_le_bound _ (add_nonneg (norm_nonneg _) (norm_nonneg _))
  intro F
  simp only [ContinuousLinearMap.comp_apply, matchedModeCell_apply,
    matchedOuterSeparatedInverse_apply, map_add, Prod.norm_def, norm_zero,
    max_eq_left (norm_nonneg _)]
  calc
    _ ≤ ‖matchedModeCellL2 D hP k
          (matchedOuterWholeExtend D false (cut false)
            (R false (matchedOuterWholeRestrict D false (cut false)
              (matchedModeCellL2 D hP m F.1))))‖ +
        ‖matchedModeCellL2 D hP k
          (matchedOuterWholeExtend D true (cut true)
            (R true (matchedOuterWholeRestrict D true (cut true)
              (matchedModeCellL2 D hP m F.1))))‖ := norm_add_le _ _
    _ ≤ ‖B false‖ * ‖F.1‖ + ‖B true‖ * ‖F.1‖ :=
      add_le_add (hside false F.1) (hside true F.1)
    _ = (‖B false‖ + ‖B true‖) * ‖F.1‖ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_left _ _)
      (add_nonneg (norm_nonneg _) (norm_nonneg _))

end ContinuousFlexibility.Radial
