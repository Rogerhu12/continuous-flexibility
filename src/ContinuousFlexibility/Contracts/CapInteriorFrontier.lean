import ContinuousFlexibility.Contracts.CapInteriorClosure
import ContinuousFlexibility.Geometry.GraphCapAttachment

/-!
# The frontier of the actual cap body is the actual disk cap plus its top disk

Every point on the closed meridian is represented in the existing Cartesian
cap disk, including the bottom axis. Conversely its three meridian regions
lie on the explicit closed wall. This identifies an actual frontier, rather
than postulating a region bounded by the cap.
-/

noncomputable section

namespace ContinuousFlexibility

open Set

set_option backward.isDefEq.respectTransparency false

theorem capClosedHeightParameter_drop {s : ℝ}
    (hs : s ∈ Icc (1 / 4 : ℝ) (3 / 4)) :
    capClosedHeightParameter (capHeightDrop s) = s := by
  have hy : capHeightDrop s ∈ Icc (0 : ℝ) capDrop := capHeightDrop_bounds s
  exact strictMonoOn_capHeightDrop.injOn (capClosedHeightParameter_mem _) hs
    (capHeightDrop_closedParameter hy)

theorem capExtendedWallRadius_at_meridian (R h : ℝ) {L s : ℝ} (hL : 0 < L)
    (hs : s / L ∈ Icc (1 / 4 : ℝ) (3 / 4)) :
    capExtendedWallRadius R h L (capMeridianHeight h L s) = capMeridianRadius R L s := by
  have he : (h - capMeridianHeight h L s) / L = capHeightDrop (s / L) := by
    unfold capMeridianHeight
    field_simp [hL.ne']; ring
  rw [capExtendedWallRadius, he, capClosedHeightParameter_drop hs]
  rfl

theorem mem_capDiskImage_of_meridian {R L : ℝ} (hR : 0 < R) (hL : 0 < L) (h : ℝ)
    {v : E3} {s : ℝ} (hs : s ∈ Icc 0 (L + R))
    (hr : cartesianRadius (graphBaseProjection v) = capMeridianRadius R L s)
    (hz : v 2 = capMeridianHeight h L s) : v ∈ capDiskImage R h L := by
  have hS := add_pos hL hR
  by_cases hx : graphBaseProjection v = 0
  · have hrad : capMeridianRadius R L s = 0 := by
      simpa only [hx, cartesianRadius, map_zero, norm_zero] using hr.symm
    have he : s = L + R := by
      rcases (capMeridianRadius_zero_iff hR hL ⟨by linarith [hs.1], hs.2⟩).mp hrad with he | he
      · linarith [hs.1]
      · exact he
    change ∃ y : capDiskDomain, capDiskMap R h L y = v
    refine ⟨⟨0, by simp [cartesianRadius]⟩, ?_⟩
    apply e3_eq_of_base_height
    · simp only [capDiskMap, graphBaseProjection_graphMap]
      rw [capDisk_axis_base hR hL (y := 0) (by norm_num [cartesianRadius]), smul_zero]
      exact hx.symm
    · rw [capDiskMap_two, capDisk_axis_height hR hL h (by norm_num [cartesianRadius]), hz, he]
      exact (capMeridianHeight_eq_right h hL (by linarith)).symm
  · have hp := cartesianRadius_pos hx
    have hlt : s < L + R := by
      apply lt_of_le_of_ne hs.2
      intro he
      have he0 : capMeridianRadius R L s = 0 :=
        (capMeridianRadius_zero_iff hR hL ⟨by linarith [hs.1], hs.2⟩).mpr (Or.inr he)
      rw [he0] at hr
      exact hp.ne' hr
    let q := (L + R - s) / (L + R)
    have hq : 0 < q := div_pos (sub_pos.mpr hlt) hS
    have hq1 : q ≤ 1 := (div_le_one hS).mpr (by linarith [hs.1])
    let y : PolarPoint := (q / cartesianRadius (graphBaseProjection v)) • graphBaseProjection v
    have hy : cartesianRadius y = q := by
      dsimp [y]
      rw [capDisk_radius_smul, abs_of_pos (div_pos hq hp), div_mul_cancel₀ _ hp.ne']
    have hparam : capDiskParameter R L y = s := by
      rw [capDiskParameter, hy]
      dsimp [q]
      field_simp [hS.ne']; ring
    have hbase : capDiskBase R L y = graphBaseProjection v := by
      rw [capDiskBase, hparam, hy, ← hr]
      dsimp [y]
      rw [smul_smul]
      have he : cartesianRadius (graphBaseProjection v) / q *
          (q / cartesianRadius (graphBaseProjection v)) = 1 := by
        field_simp [hp.ne', hq.ne']
      rw [he, one_smul]
    change ∃ y : capDiskDomain, capDiskMap R h L y = v
    refine ⟨⟨y, by simpa only [hy] using hq1⟩, ?_⟩
    apply e3_eq_of_base_height
    · simpa only [capDiskMap, graphBaseProjection_graphMap] using hbase
    · simpa only [capDiskMap_two, capDiskHeight, hparam] using hz.symm

theorem capDiskImage_subset_frontier_capRevolutionInterior {R L : ℝ}
    (hR : 0 < R) (hL : 0 < L) (h : ℝ) :
    capDiskImage R h L ⊆ frontier (capRevolutionInterior R h L) := by
  rintro v ⟨y, rfl⟩
  change capDiskMap R h L y ∈ frontier (capRevolutionInterior R h L)
  rw [frontier_capRevolutionInterior hR hL h]
  let s := capDiskParameter R L y
  have hs : s ∈ Icc 0 (L + R) := capDiskParameter_mem hR hL y.2
  have hz : capDiskMap R h L y 2 = capMeridianHeight h L s := by
    simp only [capDiskMap_two, capDiskHeight, s]
  have hr : cartesianRadius (graphBaseProjection (capDiskMap R h L y)) =
      capMeridianRadius R L s := by
    simpa only [capDiskMap, graphBaseProjection_graphMap, s] using capDiskBase_radius hR hL y.2
  change capDiskMap R h L y 2 ∈ Icc (h - L * capDrop) h ∧ _
  refine ⟨by rw [hz]; exact capMeridianHeight_bounds h hL s, ?_⟩
  by_cases hl : s ≤ L / 4
  · have he : capDiskMap R h L y 2 = h := by
      rw [hz, capMeridianHeight_eq_left h hL hl]
    rw [he, capExtendedWallRadius_top, hr, capMeridianRadius_eq_left R hL hl]
    exact ⟨by linarith, Or.inr (Or.inl rfl)⟩
  by_cases hr' : 3 * L / 4 ≤ s
  · have he : capDiskMap R h L y 2 = h - L * capDrop := by
      rw [hz, capMeridianHeight_eq_right h hL hr']
    rw [he, capExtendedWallRadius_bottom R h hL, hr, capMeridianRadius_eq_right R hL hr']
    exact ⟨by linarith, Or.inl rfl⟩
  · have hm : s / L ∈ Icc (1 / 4 : ℝ) (3 / 4) := by
      constructor
      · apply (le_div_iff₀ hL).mpr
        linarith [lt_of_not_ge hl]
      · apply (div_le_iff₀ hL).mpr
        linarith [lt_of_not_ge hr']
    have he : cartesianRadius (graphBaseProjection (capDiskMap R h L y)) =
        capExtendedWallRadius R h L (capDiskMap R h L y 2) := by
      rw [hz, capExtendedWallRadius_at_meridian R h hL hm, hr]
    exact ⟨he.le, Or.inr (Or.inr he)⟩

theorem topDisk_subset_frontier_capRevolutionInterior {R L : ℝ}
    (hR : 0 < R) (hL : 0 < L) (h : ℝ) :
    {v : E3 | v 2 = h ∧ cartesianRadius (graphBaseProjection v) ≤ R} ⊆
      frontier (capRevolutionInterior R h L) := by
  intro v hv
  rw [frontier_capRevolutionInterior hR hL h]
  refine ⟨by rw [hv.1]; exact ⟨by linarith [mul_pos hL capDrop_pos], le_rfl⟩,
    ?_, Or.inr (Or.inl hv.1)⟩
  rw [hv.1, capExtendedWallRadius_top]
  linarith [hv.2]

theorem frontier_capRevolutionInterior_eq_topDisk_union_capDisk {R L : ℝ}
    (hR : 0 < R) (hL : 0 < L) (h : ℝ) :
    frontier (capRevolutionInterior R h L) =
      {v : E3 | v 2 = h ∧ cartesianRadius (graphBaseProjection v) ≤ R} ∪ capDiskImage R h L := by
  apply Subset.antisymm
  · intro v hv
    rw [frontier_capRevolutionInterior hR hL h] at hv
    rcases hv with ⟨hz, hr, hb | ht | hw⟩
    · right
      rw [hb, capExtendedWallRadius_bottom R h hL] at hr
      let s := L + R - cartesianRadius (graphBaseProjection v)
      have hs : 3 * L / 4 ≤ s := by dsimp [s]; linarith
      apply mem_capDiskImage_of_meridian hR hL h
        (s := s) ⟨by linarith, by dsimp [s]; linarith [capDisk_radius_nonneg (graphBaseProjection v)]⟩
      · rw [capMeridianRadius_eq_right R hL hs]
        dsimp [s]
        ring
      · rw [capMeridianHeight_eq_right h hL hs]
        exact hb
    · by_cases hin : cartesianRadius (graphBaseProjection v) ≤ R
      · exact Or.inl ⟨ht, hin⟩
      · right
        rw [ht, capExtendedWallRadius_top] at hr
        let s := cartesianRadius (graphBaseProjection v) - R
        have hs : s ≤ L / 4 := by dsimp [s]; linarith
        apply mem_capDiskImage_of_meridian hR hL h
          (s := s) ⟨by dsimp [s]; linarith [lt_of_not_ge hin], by linarith⟩
        · rw [capMeridianRadius_eq_left R hL hs]
          dsimp [s]
          ring
        · rw [capMeridianHeight_eq_left h hL hs]
          exact ht
    · right
      let s := L * capClosedHeightParameter ((h - v 2) / L)
      have hm := capClosedHeightParameter_mem ((h - v 2) / L)
      have hs0 : 0 ≤ s := by dsimp [s]; nlinarith [hL, hm.1]
      have hs1 : s ≤ L + R := by dsimp [s]; nlinarith [hL, hm.2, hR]
      apply mem_capDiskImage_of_meridian hR hL h (s := s) ⟨hs0, hs1⟩
      · rw [hw]
        change R + L * capRadialOffset (capClosedHeightParameter ((h - v 2) / L)) =
          R + L * capRadialOffset (s / L)
        dsimp [s]
        rw [mul_div_cancel_left₀ _ hL.ne']
      · have hy : (h - v 2) / L ∈ Icc (0 : ℝ) capDrop := by
          exact ⟨div_nonneg (sub_nonneg.mpr hz.2) hL.le,
            (div_le_iff₀ hL).mpr (by linarith [hz.1])⟩
        change v 2 = h - L * capHeightDrop (s / L)
        dsimp [s]
        rw [mul_div_cancel_left₀ _ hL.ne', capHeightDrop_closedParameter hy]
        field_simp [hL.ne']; ring
  · exact union_subset (topDisk_subset_frontier_capRevolutionInterior hR hL h)
      (capDiskImage_subset_frontier_capRevolutionInterior hR hL h)

end ContinuousFlexibility
