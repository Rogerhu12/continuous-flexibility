module

public import ContinuousFlexibility.Geometry.MarkerAmbientDeformation
public import ContinuousFlexibility.Contracts.GraphCapFrontier
public import ContinuousFlexibility.Geometry.SphereCapGluing

/-!
# The actual inside after inserting the fixed marker

The fixed ambient deformation is applied to the same moving graph-cap body.
Its continuity and genuine inverse give the topology of the actual marked
inside. Compact image bounds, rather than an assertion that arbitrary
homeomorphisms preserve boundedness, give finite positive volume.
The complete marked frontier, volume identity and outward identification
are assembled from this same body, length and marker parameters.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility

open Set MeasureTheory

set_option backward.isDefEq.respectTransparency false

def IsometricGraphDevelopment.markedCapInterior
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) (t R L k ρ : ℝ)
    (hL : 0 < L) (hk : 0 ≤ k) (hρ : 0 < ρ) : Set E3 :=
  markerAmbientHomeomorph R A.cRight L k ρ hL hk hρ '' D.graphCapInterior t R L

theorem IsometricGraphDevelopment.markedCapInterior_eq_preimage
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) (t R L k ρ : ℝ)
    (hL : 0 < L) (hk : 0 ≤ k) (hρ : 0 < ρ) :
    D.markedCapInterior t R L k ρ hL hk hρ =
      (markerAmbientHomeomorph R A.cRight L k ρ hL hk hρ).symm ⁻¹'
        D.graphCapInterior t R L :=
  (congrFun (markerAmbientHomeomorph R A.cRight L k ρ hL hk hρ).preimage_symm _).symm

theorem IsometricGraphDevelopment.isOpen_markedCapInterior
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) (t R L k ρ : ℝ)
    (hL : 0 < L) (hk : 0 ≤ k) (hρ : 0 < ρ) :
    IsOpen (D.markedCapInterior t R L k ρ hL hk hρ) :=
  (markerAmbientHomeomorph R A.cRight L k ρ hL hk hρ).isOpenMap _
    (D.isOpen_graphCapInterior t R hL)

theorem IsometricGraphDevelopment.isConnected_markedCapInterior
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) {R L : ℝ}
    (hR : A.b < R) (hL : 0 < L) (t k ρ : ℝ) (hk : 0 ≤ k) (hρ : 0 < ρ)
    (hb : ∀ x : PolarPoint, cartesianRadius x ≤ R →
      A.cRight - L * capDrop < D.physicalHeight (planarRotation t x)) :
    IsConnected (D.markedCapInterior t R L k ρ hL hk hρ) :=
  (D.isConnected_graphCapInterior hR hL t hb).image _
    (markerAmbientHomeomorph R A.cRight L k ρ hL hk hρ).continuous.continuousOn

theorem IsometricGraphDevelopment.isConnected_markedCapExterior
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) {R L : ℝ}
    (hR : A.b < R) (hL : 0 < L) (t k ρ : ℝ) (hk : 0 ≤ k) (hρ : 0 < ρ)
    (hb : ∀ x : PolarPoint, cartesianRadius x ≤ R →
      A.cRight - L * capDrop < D.physicalHeight (planarRotation t x)) :
    IsConnected (closure (D.markedCapInterior t R L k ρ hL hk hρ))ᶜ := by
  rw [D.markedCapInterior_eq_preimage,
    ← (markerAmbientHomeomorph R A.cRight L k ρ hL hk hρ).symm.preimage_closure,
    ← preimage_compl]
  exact (markerAmbientHomeomorph R A.cRight L k ρ hL hk hρ).symm.isConnected_preimage.mpr
    (D.isConnected_graphCapExterior hR hL t hb)

theorem IsometricGraphDevelopment.exists_compact_markedCapInterior_bound
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) (R L k ρ : ℝ)
    (hL : 0 < L) (hk : 0 ≤ k) (hρ : 0 < ρ) :
    ∃ K : Set E3, IsCompact K ∧ ∀ t : ℝ, D.markedCapInterior t R L k ρ hL hk hρ ⊆ K := by
  obtain ⟨K, hK, hsub⟩ := D.exists_compact_graphCapInterior_bound R hL
  let H := markerAmbientHomeomorph R A.cRight L k ρ hL hk hρ
  refine ⟨H '' K, hK.image H.continuous, fun t => ?_⟩
  exact image_mono (hsub t)

theorem IsometricGraphDevelopment.isBounded_markedCapInterior
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) (t R L k ρ : ℝ)
    (hL : 0 < L) (hk : 0 ≤ k) (hρ : 0 < ρ) :
    Bornology.IsBounded (D.markedCapInterior t R L k ρ hL hk hρ) := by
  obtain ⟨K, hK, hsub⟩ := D.exists_compact_markedCapInterior_bound R L k ρ hL hk hρ
  exact hK.isBounded.subset (hsub t)

theorem IsometricGraphDevelopment.unbounded_markedCapExterior
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) (t R L k ρ : ℝ)
    (hL : 0 < L) (hk : 0 ≤ k) (hρ : 0 < ρ) :
    ¬Bornology.IsBounded (closure (D.markedCapInterior t R L k ρ hL hk hρ))ᶜ := by
  have hb := (D.isBounded_markedCapInterior t R L k ρ hL hk hρ).closure
  intro he
  apply NormedSpace.unbounded_univ ℝ E3
  simpa only [union_compl_self] using hb.union he

theorem IsometricGraphDevelopment.markedCapInterior_volume_lt_top
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) (t R L k ρ : ℝ)
    (hL : 0 < L) (hk : 0 ≤ k) (hρ : 0 < ρ) :
    volume (D.markedCapInterior t R L k ρ hL hk hρ) < ⊤ := by
  obtain ⟨K, hK, hsub⟩ := D.exists_compact_markedCapInterior_bound R L k ρ hL hk hρ
  exact (measure_mono (hsub t)).trans_lt hK.measure_lt_top

theorem IsometricGraphDevelopment.markedCapInterior_volume_pos
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) {R L : ℝ}
    (hR : A.b < R) (hL : 0 < L) (t k ρ : ℝ) (hk : 0 ≤ k) (hρ : 0 < ρ)
    (hb : ∀ x : PolarPoint, cartesianRadius x ≤ R →
      A.cRight - L * capDrop < D.physicalHeight (planarRotation t x)) :
    0 < volume (D.markedCapInterior t R L k ρ hL hk hρ) := by
  apply (D.isOpen_markedCapInterior t R L k ρ hL hk hρ).measure_pos volume
  exact (D.isConnected_markedCapInterior hR hL t k ρ hk hρ hb).nonempty

theorem markerAmbientHomeomorph_image_capDisk {R L k ρ : ℝ}
    (hR : 0 < R) (hL : 0 < L) (hk : 0 ≤ k) (hρ : 0 < ρ) (hsmall : ρ < L / 64) (h : ℝ) :
    markerAmbientHomeomorph R h L k ρ hL hk hρ '' capDiskImage R h L =
      markedCapMap R h L k ρ '' {y : PolarPoint | cartesianRadius y ≤ 1} := by
  ext v
  constructor
  · rintro ⟨w, ⟨y, rfl⟩, rfl⟩
    refine ⟨(y : PolarPoint), y.2, ?_⟩
    exact (markerAmbientHomeomorph_capDiskMap hR hL hk hρ hsmall h y.2).symm
  · rintro ⟨y, hy, rfl⟩
    refine ⟨capDiskMap R h L y, ⟨⟨y, hy⟩, rfl⟩, ?_⟩
    exact markerAmbientHomeomorph_capDiskMap hR hL hk hρ hsmall h hy

theorem IsometricGraphDevelopment.frontier_markedCapInterior
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) {R L : ℝ}
    (hR : A.b < R) (hL : 0 < L) (t k ρ : ℝ) (hk : 0 ≤ k) (hρ : 0 < ρ)
    (hsmall : ρ < L / 64)
    (hb : ∀ x : PolarPoint, cartesianRadius x ≤ R →
      A.cRight - L * capDrop < D.physicalHeight (planarRotation t x)) :
    frontier (D.markedCapInterior t R L k ρ hL hk hρ) = graphPhaseDiskImage D R t ∪
      markedCapMap R A.cRight L k ρ '' {y : PolarPoint | cartesianRadius y ≤ 1} := by
  change frontier (markerAmbientHomeomorph R A.cRight L k ρ hL hk hρ ''
    D.graphCapInterior t R L) = _
  rw [← (markerAmbientHomeomorph R A.cRight L k ρ hL hk hρ).image_frontier,
    D.frontier_graphCapInterior hR hL t hb, image_union,
    D.markerAmbientHomeomorph_image_graphDisk hR hL hk hρ hsmall t,
    markerAmbientHomeomorph_image_capDisk (A.b_pos.trans hR) hL hk hρ hsmall A.cRight]

theorem IsometricGraphDevelopment.frontier_markedCapInterior_eq_sphereRange
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) {R L : ℝ}
    (hR : A.b < R) (hL : 0 < L) (t k ρ : ℝ) (hk : 0 ≤ k) (hρ : 0 < ρ)
    (hsmall : ρ < L / 64)
    (hb : ∀ x : PolarPoint, cartesianRadius x ≤ R →
      A.cRight - L * capDrop < D.physicalHeight (planarRotation t x)) :
    frontier (D.markedCapInterior t R L k ρ hL hk hρ) =
      range (fun x => sphereGraphCapFamily D (markedCapMap R A.cRight L k ρ) R L (x, t)) := by
  rw [D.frontier_markedCapInterior hR hL t k ρ hk hρ hsmall hb]
  exact (sphereGraphCapFamily_range D hR hL
    (fun _ hy => markedCapMap_capSphereRadialMap_rim_germ (k := k)
      (A.b_pos.trans hR) hL hρ hsmall A.cRight hy) t).symm

def markedCapFixedOutside (R h L k ρ : ℝ) (hL : 0 < L) (hk : 0 ≤ k) (hρ : 0 < ρ) : Set E3 :=
  markerAmbientHomeomorph R h L k ρ hL hk hρ '' graphCapFixedOutside R h L

theorem IsometricGraphDevelopment.markerAmbientHomeomorph_image_graphCylinder
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) {R L k ρ : ℝ}
    (hR : A.b < R) (hL : 0 < L) (hk : 0 ≤ k) (hρ : 0 < ρ) (hsmall : ρ < L / 64)
    (t bottom : ℝ) :
    markerAmbientHomeomorph R A.cRight L k ρ hL hk hρ '' D.graphCylinderInterior t R bottom =
      D.graphCylinderInterior t R bottom := by
  have hfix : ∀ v ∈ D.graphCylinderInterior t R bottom,
      markerAmbientHomeomorph R A.cRight L k ρ hL hk hρ v = v := by
    intro v hv
    apply markerAmbientHomeomorph_eq_self_of_inner (A.b_pos.trans hR) hL hk hρ hsmall A.cRight
    have hr : cartesianRadius (graphBaseProjection v) < R := hv.1
    linarith
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    simpa only [hfix w hw] using hw
  · intro hv
    exact ⟨v, hv, hfix v hv⟩

theorem IsometricGraphDevelopment.markedCapInterior_partition
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) {R L : ℝ}
    (hR : A.b < R) (hL : 0 < L) (t k ρ : ℝ) (hk : 0 ≤ k) (hρ : 0 < ρ)
    (hsmall : ρ < L / 64) :
    D.markedCapInterior t R L k ρ hL hk hρ =
      D.graphCylinderInterior t R (A.cRight - L * capDrop) ∪
        markedCapFixedOutside R A.cRight L k ρ hL hk hρ := by
  unfold IsometricGraphDevelopment.markedCapInterior markedCapFixedOutside
  rw [D.graphCapInterior_partition hR, image_union,
    D.markerAmbientHomeomorph_image_graphCylinder hR hL hk hρ hsmall]

theorem measurableSet_markedCapFixedOutside (R h L k ρ : ℝ)
    (hL : 0 < L) (hk : 0 ≤ k) (hρ : 0 < ρ) :
    MeasurableSet (markedCapFixedOutside R h L k ρ hL hk hρ) := by
  exact (markerAmbientHomeomorph R h L k ρ hL hk hρ).toMeasurableEquiv.measurableEmbedding
    |>.measurableSet_image.mpr (measurableSet_graphCapFixedOutside R h hL)

theorem disjoint_graphCylinder_markedOutside
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) (t R L k ρ : ℝ)
    (hL : 0 < L) (hk : 0 ≤ k) (hρ : 0 < ρ) :
    Disjoint (D.graphCylinderInterior t R (A.cRight - L * capDrop))
      (markedCapFixedOutside R A.cRight L k ρ hL hk hρ) := by
  apply disjoint_left.mpr
  intro v hv hw
  obtain ⟨w, hw, rfl⟩ := hw
  have hin : cartesianRadius (graphBaseProjection
      (markerAmbientHomeomorph R A.cRight L k ρ hL hk hρ w)) < R := hv.1
  rw [markerAmbientHomeomorph_base] at hin
  exact not_lt_of_ge hw.2 hin

theorem IsometricGraphDevelopment.markedCapInterior_volume
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) {R L : ℝ}
    (hR : A.b < R) (hL : 0 < L) (t k ρ : ℝ) (hk : 0 ≤ k) (hρ : 0 < ρ)
    (hsmall : ρ < L / 64) :
    volume (D.markedCapInterior t R L k ρ hL hk hρ) =
      volume (D.markedCapInterior 0 R L k ρ hL hk hρ) := by
  rw [D.markedCapInterior_partition hR hL t k ρ hk hρ hsmall,
    D.markedCapInterior_partition hR hL 0 k ρ hk hρ hsmall]
  rw [measure_union (disjoint_graphCylinder_markedOutside D t R L k ρ hL hk hρ)
    (measurableSet_markedCapFixedOutside R A.cRight L k ρ hL hk hρ),
    measure_union (disjoint_graphCylinder_markedOutside D 0 R L k ρ hL hk hρ)
      (measurableSet_markedCapFixedOutside R A.cRight L k ρ hL hk hρ)]
  rw [D.graphCylinderInterior_volume]

end ContinuousFlexibility
