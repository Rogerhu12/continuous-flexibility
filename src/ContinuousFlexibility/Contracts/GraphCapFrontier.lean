module

public import ContinuousFlexibility.Contracts.GraphCapHomeomorph
public import ContinuousFlexibility.Contracts.CapInteriorFrontier

/-!
# The actual moving graph and fixed unmarked cap bound the constructed body

The vertical homeomorphism fixes the entire existing cap pointwise: outside
the attaching cylinder it is the identity, and inside it the cap is the bottom
disk. The flat top disk maps onto the actual developed graph disk. Frontier
transport therefore gives equality with the actual glued surface image.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility

open Set

set_option backward.isDefEq.respectTransparency false

theorem IsometricGraphDevelopment.graphCapHomeomorph_fixes_bottom
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) {R L : ℝ}
    (hR : A.b < R) (hL : 0 < L) (t : ℝ)
    (hb : ∀ x : PolarPoint, cartesianRadius x ≤ R →
      A.cRight - L * capDrop < D.physicalHeight (planarRotation t x)) {v : E3}
    (hv : v 2 = A.cRight - L * capDrop) : D.graphCapHomeomorph hR hL t hb v = v := by
  apply e3_eq_of_base_height
  · exact D.graphCapHomeomorph_base hR hL t hb v
  · simp only [D.graphCapHomeomorph_height, hv, sub_self, mul_zero, add_zero]

theorem IsometricGraphDevelopment.graphCapHomeomorph_fixes_cap
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) {R L : ℝ}
    (hR : A.b < R) (hL : 0 < L) (t : ℝ)
    (hb : ∀ x : PolarPoint, cartesianRadius x ≤ R →
      A.cRight - L * capDrop < D.physicalHeight (planarRotation t x))
    {v : E3} (hv : v ∈ capDiskImage R A.cRight L) :
    D.graphCapHomeomorph hR hL t hb v = v := by
  by_cases hr : cartesianRadius (graphBaseProjection v) < R
  · obtain ⟨y, rfl⟩ := hv
    exact D.graphCapHomeomorph_fixes_bottom hR hL t hb
      (capDisk_inside_cylinder_bottom (A.b_pos.trans hR) hL A.cRight y.2 hr)
  · exact D.graphCapHomeomorph_outside hR hL t hb (hR.trans_le (le_of_not_gt hr))

theorem IsometricGraphDevelopment.graphCapHomeomorph_image_cap
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) {R L : ℝ}
    (hR : A.b < R) (hL : 0 < L) (t : ℝ)
    (hb : ∀ x : PolarPoint, cartesianRadius x ≤ R →
      A.cRight - L * capDrop < D.physicalHeight (planarRotation t x)) :
    D.graphCapHomeomorph hR hL t hb '' capDiskImage R A.cRight L =
      capDiskImage R A.cRight L := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    simpa only [D.graphCapHomeomorph_fixes_cap hR hL t hb hw] using hw
  · intro hv
    exact ⟨v, hv, D.graphCapHomeomorph_fixes_cap hR hL t hb hv⟩

theorem IsometricGraphDevelopment.graphCapHomeomorph_image_topDisk
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) {R L : ℝ}
    (hR : A.b < R) (hL : 0 < L) (t : ℝ)
    (hb : ∀ x : PolarPoint, cartesianRadius x ≤ R →
      A.cRight - L * capDrop < D.physicalHeight (planarRotation t x)) :
    D.graphCapHomeomorph hR hL t hb ''
      {v : E3 | v 2 = A.cRight ∧ cartesianRadius (graphBaseProjection v) ≤ R} =
        graphPhaseDiskImage D R t := by
  have htop : ∀ v : E3, v 2 = A.cRight →
      D.graphCapHomeomorph hR hL t hb v 2 =
        D.physicalHeight (planarRotation t (graphBaseProjection v)) := by
    intro v hv
    rw [D.graphCapHomeomorph_height, IsometricGraphDevelopment.graphHeightScale, hv]
    have he : A.cRight - (A.cRight - L * capDrop) = L * capDrop := by ring
    rw [he, div_mul_cancel₀ _ (mul_pos hL capDrop_pos).ne']
    ring
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    have hproj : graphBaseProjection w ∈ graphBaseProjection '' graphPhaseDiskImage D R t := by
      change graphBaseProjection w ∈ graphBaseProjection ''
        (D.rotationFamily t '' {x : PolarPoint | cartesianRadius x ≤ R})
      rw [D.rotationFamily_projects_onto_disk t hR.le]
      exact hw.2
    obtain ⟨p, ⟨x, hx, hxp⟩, hpw⟩ := hproj
    refine ⟨x, hx, ?_⟩
    apply e3_eq_of_base_height
    · rw [D.graphCapHomeomorph_base, hxp, hpw]
    · rw [D.rotationFamily_physical_height, hxp, hpw, htop w hw.1]
  · rintro ⟨x, hx, rfl⟩
    let w := euclideanVectorOfCoordinates (graphBaseProjection (D.rotationFamily t x), A.cRight)
    have hbase : graphBaseProjection w = graphBaseProjection (D.rotationFamily t x) := by
      simp [w, euclideanVectorOfCoordinates, graphBaseProjection, e3Basis]
    have hheight : w 2 = A.cRight := by simp [w, euclideanVectorOfCoordinates, e3Basis]
    refine ⟨w, ⟨hheight, by rw [hbase]; exact D.phase_disk_projection_bound t hR.le hx⟩, ?_⟩
    apply e3_eq_of_base_height
    · rw [D.graphCapHomeomorph_base, hbase]
    · rw [htop w hheight, hbase, D.rotationFamily_physical_height]

theorem IsometricGraphDevelopment.frontier_graphCapInterior
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) {R L : ℝ}
    (hR : A.b < R) (hL : 0 < L) (t : ℝ)
    (hb : ∀ x : PolarPoint, cartesianRadius x ≤ R →
      A.cRight - L * capDrop < D.physicalHeight (planarRotation t x)) :
    frontier (D.graphCapInterior t R L) = graphPhaseDiskImage D R t ∪ capDiskImage R A.cRight L := by
  have he : D.graphCapInterior t R L = D.graphCapHomeomorph hR hL t hb ''
      capRevolutionInterior R A.cRight L := by
    rw [D.graphCapInterior_eq_preimage hR hL t hb]
    exact congrFun (D.graphCapHomeomorph hR hL t hb).preimage_symm _
  rw [he, ← (D.graphCapHomeomorph hR hL t hb).image_frontier,
    frontier_capRevolutionInterior_eq_topDisk_union_capDisk (A.b_pos.trans hR) hL A.cRight,
    image_union, D.graphCapHomeomorph_image_topDisk hR hL t hb,
    D.graphCapHomeomorph_image_cap hR hL t hb]

end ContinuousFlexibility
