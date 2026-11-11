import ContinuousFlexibility.Contracts.CapInteriorProfile
import ContinuousFlexibility.Contracts.GraphBoundaryNormals

/-!
# Gluing the moving subgraph to the actual revolution body

The overlap is an open flat annulus. The glued body is genuinely open and
bounded, and it has a disjoint partition into the moving cylinder portion and
one fixed outside region. Its Lebesgue volume is therefore phase independent.
The complete frontier identification and insertion of the fixed marker remain
separate obligations before calling this the enclosed region of the final sphere.
-/

noncomputable section

namespace ContinuousFlexibility

open Set MeasureTheory Filter
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

theorem IsometricGraphDevelopment.physicalHeight_outside
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) {x : PolarPoint}
    (hx : A.b < cartesianRadius x) : D.physicalHeight x = A.cRight := by
  have hi : D.planar.symm x = x := by
    apply D.planar.injective
    simpa only [D.planar.apply_symm_apply] using (D.normalized_outside x hx).symm
  change A.cartesianHeight (D.planar.symm x) = A.cRight
  rw [hi]
  exact A.cartesianHeight_right hx.le

theorem IsometricGraphDevelopment.rotated_physicalHeight_outside
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) (t : ℝ) {x : PolarPoint}
    (hx : A.b < cartesianRadius x) : D.physicalHeight (planarRotation t x) = A.cRight :=
  D.physicalHeight_outside (by simpa only [cartesianRadius_planarRotation] using hx)

def IsometricGraphDevelopment.graphCapInterior
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) (t R L : ℝ) : Set E3 :=
  D.graphCylinderInterior t R (A.cRight - L * capDrop) ∪
    (capRevolutionInterior R A.cRight L ∩
      {v | (A.b + R) / 2 < cartesianRadius (graphBaseProjection v)})

def graphCapFixedOutside (R h L : ℝ) : Set E3 :=
  capRevolutionInterior R h L ∩ {v | R ≤ cartesianRadius (graphBaseProjection v)}

theorem IsometricGraphDevelopment.isOpen_graphCapInterior
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) (t R : ℝ) {L : ℝ} (hL : 0 < L) :
    IsOpen (D.graphCapInterior t R L) :=
  (D.isOpen_graphCylinderInterior t R _).union
    ((isOpen_capRevolutionInterior R A.cRight hL).inter
      (isOpen_lt continuous_const (continuous_cartesianRadius.comp continuous_graphBaseProjection)))

theorem IsometricGraphDevelopment.graphCapInterior_partition
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) {R L : ℝ}
    (hR : A.b < R) (t : ℝ) :
    D.graphCapInterior t R L =
      D.graphCylinderInterior t R (A.cRight - L * capDrop) ∪
        graphCapFixedOutside R A.cRight L := by
  ext v
  constructor
  · rintro (hv | ⟨hv, hr⟩)
    · exact Or.inl hv
    · change (A.b + R) / 2 < cartesianRadius (graphBaseProjection v) at hr
      by_cases hin : cartesianRadius (graphBaseProjection v) < R
      · have hb : A.b < cartesianRadius (graphBaseProjection v) := by linarith
        exact Or.inl ⟨hin, hv.1.1, by
          rw [D.rotated_physicalHeight_outside t hb]
          exact hv.1.2⟩
      · exact Or.inr ⟨hv, le_of_not_gt hin⟩
  · rintro (hv | ⟨hv, hr⟩)
    · exact Or.inl hv
    · change R ≤ cartesianRadius (graphBaseProjection v) at hr
      exact Or.inr ⟨hv, by
        change (A.b + R) / 2 < cartesianRadius (graphBaseProjection v)
        linarith⟩

theorem disjoint_graphCylinder_fixedOutside
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) (t R L : ℝ) :
    Disjoint (D.graphCylinderInterior t R (A.cRight - L * capDrop))
      (graphCapFixedOutside R A.cRight L) := by
  apply disjoint_left.mpr
  intro v hv hw
  exact not_lt_of_ge hw.2 hv.1

theorem measurableSet_graphCapFixedOutside (R h : ℝ) {L : ℝ} (hL : 0 < L) :
    MeasurableSet (graphCapFixedOutside R h L) :=
  (isOpen_capRevolutionInterior R h hL).measurableSet.inter
    (isClosed_le continuous_const
      (continuous_cartesianRadius.comp continuous_graphBaseProjection)).measurableSet

theorem IsometricGraphDevelopment.graphCapInterior_volume
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) {R L : ℝ}
    (hR : A.b < R) (hL : 0 < L) (t : ℝ) :
    volume (D.graphCapInterior t R L) = volume (D.graphCapInterior 0 R L) := by
  rw [D.graphCapInterior_partition hR, D.graphCapInterior_partition hR]
  rw [measure_union (disjoint_graphCylinder_fixedOutside D t R L)
    (measurableSet_graphCapFixedOutside R A.cRight hL),
    measure_union (disjoint_graphCylinder_fixedOutside D 0 R L)
      (measurableSet_graphCapFixedOutside R A.cRight hL)]
  rw [D.graphCylinderInterior_volume]

theorem IsometricGraphDevelopment.exists_compact_graphCapInterior_bound
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) (R : ℝ) {L : ℝ} (hL : 0 < L) :
    ∃ K : Set E3, IsCompact K ∧ ∀ t : ℝ, D.graphCapInterior t R L ⊆ K := by
  obtain ⟨K, hK, hsub⟩ := D.exists_compact_graphCylinder_bound R (A.cRight - L * capDrop)
  obtain ⟨J, hJ, hjsub⟩ := capRevolutionInterior_subset_compact R A.cRight hL
  refine ⟨K ∪ J, hK.union hJ, fun t v hv => ?_⟩
  rcases hv with hv | hv
  · exact Or.inl (hsub t hv)
  · exact Or.inr (hjsub hv.1)

theorem IsometricGraphDevelopment.graphCapInterior_volume_lt_top
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) (t R : ℝ) {L : ℝ} (hL : 0 < L) :
    volume (D.graphCapInterior t R L) < ⊤ := by
  obtain ⟨K, hK, hsub⟩ := D.exists_compact_graphCapInterior_bound R hL
  exact (measure_mono (hsub t)).trans_lt hK.measure_lt_top

theorem IsometricGraphDevelopment.exists_cap_bottom_below_physical_graph
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) (R : ℝ) :
    ∃ L : ℝ, 0 < L ∧ ∀ t : ℝ, ∀ y : PolarPoint, cartesianRadius y ≤ R →
      A.cRight - L * capDrop < D.physicalHeight (planarRotation t y) := by
  obtain ⟨lo, hlo⟩ := (isCompact_closedCartesianDisk R).bddBelow_image
    D.contDiff_physicalHeight.continuous.continuousOn
  refine ⟨capLength A.cRight lo 1, capLength_pos _ _ (by norm_num), fun t y hy => ?_⟩
  apply (capLength_bottom_lt A.cRight lo (by norm_num : (0 : ℝ) < 1)).trans_le
  exact hlo ⟨planarRotation t y, by simpa using hy, rfl⟩

theorem IsometricGraphDevelopment.graphCapInterior_volume_pos
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) {R L : ℝ}
    (hR : 0 < R) (hL : 0 < L) (hb : A.cRight - L * capDrop < D.physicalHeight 0) (t : ℝ) :
    0 < volume (D.graphCapInterior t R L) := by
  apply (D.isOpen_graphCapInterior t R hL).measure_pos volume
  let z := (A.cRight - L * capDrop + D.physicalHeight 0) / 2
  refine ⟨euclideanVectorOfCoordinates (0, z), Or.inl ?_⟩
  have hp : graphBaseProjection (euclideanVectorOfCoordinates (0, z)) = 0 := by
    simp [euclideanVectorOfCoordinates, graphBaseProjection, e3Basis]
  have hz : euclideanVectorOfCoordinates (0, z) 2 = z := by
    simp [euclideanVectorOfCoordinates, e3Basis]
  change cartesianRadius (graphBaseProjection (euclideanVectorOfCoordinates (0, z))) < R ∧ _
  rw [hp, hz]
  simp only [map_zero]
  exact ⟨by simpa [cartesianRadius] using hR,
    by dsimp [z]; linarith, by dsimp [z]; linarith⟩

/-- The constructed upward normal is truly outward for the glued body at
every central graph point. The fixed outer portion cannot meet its small rays. -/
theorem IsometricGraphDevelopment.rotationNormal_pointsOutwardFrom_graphCapInterior
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) {R L : ℝ} (hR : A.b < R)
    (t : ℝ) (x : PolarPoint)
    (hr : cartesianRadius (graphBaseProjection (D.rotationFamily t x)) < R)
    (hb : A.cRight - L * capDrop < D.rotationFamily t x 2) :
    PointsOutwardFrom (D.graphCapInterior t R L) (D.rotationFamily t x) (D.rotationNormal t x) := by
  obtain ⟨ε, hε, hrays⟩ := D.rotationNormal_pointsOutwardFrom t x hr hb
  have hc : Continuous (fun s : ℝ => cartesianRadius
      (graphBaseProjection (D.rotationFamily t x + s • D.rotationNormal t x))) :=
    continuous_cartesianRadius.comp (continuous_graphBaseProjection.comp
      (continuous_const.add (continuous_id.smul continuous_const)))
  have hnear : ∀ᶠ s in 𝓝 (0 : ℝ), cartesianRadius
      (graphBaseProjection (D.rotationFamily t x + s • D.rotationNormal t x)) < R := by
    exact hc.continuousAt.eventually_lt continuousAt_const (by simpa using hr)
  obtain ⟨δ, hδ, hδbound⟩ := Metric.eventually_nhds_iff.mp hnear
  have houter : closure (graphCapFixedOutside R A.cRight L) ⊆
      {v | R ≤ cartesianRadius (graphBaseProjection v)} :=
    closure_minimal (fun _ hv => hv.2) (isClosed_le continuous_const
      (continuous_cartesianRadius.comp continuous_graphBaseProjection))
  refine ⟨min ε δ, lt_min hε hδ, fun s hs => ?_⟩
  have hsε : s ∈ Ioo (0 : ℝ) ε := ⟨hs.1, hs.2.trans_le (min_le_left ε δ)⟩
  have hsδ : s < δ := hs.2.trans_le (min_le_right ε δ)
  refine ⟨Or.inl (hrays s hsε).1, fun hm => ?_⟩
  rw [D.graphCapInterior_partition hR, closure_union] at hm
  rcases hm with hm | hm
  · exact (hrays s hsε).2 hm
  · have hsmall := hδbound (y := s) (by simpa [Real.dist_eq, abs_of_pos hs.1] using hsδ)
    exact not_le_of_gt hsmall (houter hm)

/-- One actual cap length gives open bounded positive-volume bodies for
all phases, equal volumes and the correct central outward normal. -/
theorem IsometricGraphDevelopment.exists_graphCapInterior_family
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) {R : ℝ} (hR : A.b < R) :
    ∃ L : ℝ, 0 < L ∧ ∀ t : ℝ,
      IsOpen (D.graphCapInterior t R L) ∧
      0 < volume (D.graphCapInterior t R L) ∧
      volume (D.graphCapInterior t R L) < ⊤ ∧
      volume (D.graphCapInterior t R L) = volume (D.graphCapInterior 0 R L) ∧
      ∀ x : PolarPoint, cartesianRadius x < R →
        PointsOutwardFrom (D.graphCapInterior t R L) (D.rotationFamily t x) (D.rotationNormal t x) ∧
        D.rotationFamily t x ∈ frontier (D.graphCapInterior t R L) := by
  obtain ⟨L, hL, hbelow⟩ := D.exists_cap_bottom_below_physical_graph R
  have hb0 : A.cRight - L * capDrop < D.physicalHeight 0 := by
    simpa only [map_zero] using hbelow 0 0
      (by simpa [cartesianRadius] using (A.b_pos.trans hR).le)
  refine ⟨L, hL, fun t => ⟨D.isOpen_graphCapInterior t R hL,
    D.graphCapInterior_volume_pos (A.b_pos.trans hR) hL hb0 t,
    D.graphCapInterior_volume_lt_top t R hL, D.graphCapInterior_volume hR hL t, ?_⟩⟩
  intro x hx
  have hr := D.rotationFamily_base_radius_lt t hR hx
  have hb : A.cRight - L * capDrop < D.rotationFamily t x 2 := by
    rw [D.rotationFamily_physical_height]
    exact hbelow t _ hr.le
  have hn := D.rotationNormal_pointsOutwardFrom_graphCapInterior hR t x hr hb
  exact ⟨hn, hn.mem_frontier⟩

end ContinuousFlexibility
