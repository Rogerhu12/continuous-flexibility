module

public import ContinuousFlexibility.Contracts.GraphDiskIntegrals
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# The actual subgraph region inside the central cylinder

This is a genuine open subset of Euclidean three-space bounded between a bottom
plane and the physical developed graph. Its finite Lebesgue volume is invariant
under the actual phase rotations. It is only the central-cylinder portion of
the eventual inside: the outside cap region and the full frontier identification
still have to be assembled.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility

open Set MeasureTheory
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

def IsometricGraphDevelopment.graphCylinderInterior
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) (t R bottom : ℝ) : Set E3 :=
  {v | cartesianRadius (graphBaseProjection v) < R ∧ bottom < v 2 ∧
    v 2 < D.physicalHeight (planarRotation t (graphBaseProjection v))}

theorem IsometricGraphDevelopment.rotationFamily_physical_height
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) (t : ℝ) (x : PolarPoint) :
    D.rotationFamily t x 2 =
      D.physicalHeight (planarRotation t (graphBaseProjection (D.rotationFamily t x))) := by
  simp only [IsometricGraphDevelopment.rotationFamily, graphMap_two,
    graphBaseProjection_graphMap, rotationConjugate_apply, planarRotation_neg_cancel,
    IsometricGraphDevelopment.physicalHeight, rotatedHeight, D.planar.symm_apply_apply]

theorem IsometricGraphDevelopment.isOpen_graphCylinderInterior
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) (t R bottom : ℝ) :
    IsOpen (D.graphCylinderInterior t R bottom) := by
  have hz : Continuous (fun v : E3 => v 2) := (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).continuous
  have hr := continuous_cartesianRadius.comp continuous_graphBaseProjection
  have htop := D.contDiff_physicalHeight.continuous.comp
    ((planarRotation t).continuous.comp continuous_graphBaseProjection)
  exact (isOpen_lt hr continuous_const).inter
    ((isOpen_lt continuous_const hz).inter (isOpen_lt hz htop))

theorem IsometricGraphDevelopment.graphCylinderInterior_eq_axial_image
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) (t R bottom : ℝ) :
    D.graphCylinderInterior t R bottom =
      axialRotation (-t) '' D.graphCylinderInterior 0 R bottom := by
  ext v
  constructor
  · intro hv
    refine ⟨axialRotation t v, ?_, ?_⟩
    · simpa only [IsometricGraphDevelopment.graphCylinderInterior, mem_ofPred_eq,
        axialRotation_apply, axialRotationMap_base, axialRotationMap_height,
        cartesianRadius_planarRotation, planarRotation_zero] using hv
    · change axialRotationMap (-t) (axialRotationMap t v) = v
      rw [← axialRotationMap_add, neg_add_cancel, axialRotationMap_zero]
  · rintro ⟨u, hu, rfl⟩
    simpa only [IsometricGraphDevelopment.graphCylinderInterior, mem_ofPred_eq,
      axialRotation_apply, axialRotationMap_base, axialRotationMap_height,
      cartesianRadius_planarRotation, planarRotation_neg_cancel, planarRotation_zero] using hu

theorem IsometricGraphDevelopment.graphCylinderInterior_volume
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) (t R bottom : ℝ) :
    volume (D.graphCylinderInterior t R bottom) = volume (D.graphCylinderInterior 0 R bottom) := by
  rw [D.graphCylinderInterior_eq_axial_image]
  have h := (axialRotation (-t)).measurePreserving.measure_preimage_emb
    (axialRotation (-t)).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv.measurableEmbedding
    (axialRotation (-t) '' D.graphCylinderInterior 0 R bottom)
  rw [Set.preimage_image_eq _ (axialRotation (-t)).injective] at h
  exact h.symm

def euclideanVectorOfCoordinates (q : PolarPoint × ℝ) : E3 :=
  q.1.1 • e3Basis 0 + q.1.2 • e3Basis 1 + q.2 • e3Basis 2

theorem continuous_euclideanVectorOfCoordinates : Continuous euclideanVectorOfCoordinates :=
  ((continuous_fst.fst.smul continuous_const).add
    (continuous_fst.snd.smul continuous_const)).add (continuous_snd.smul continuous_const)

@[simp] theorem euclideanVectorOfCoordinates_of_vector (v : E3) :
    euclideanVectorOfCoordinates (graphBaseProjection v, v 2) = v := by
  apply e3_eq_of_base_height
  · simp [euclideanVectorOfCoordinates, graphBaseProjection, e3Basis]
  · simp [euclideanVectorOfCoordinates, e3Basis]

/-- A single actual compact set bounds all phase interiors simultaneously. -/
theorem IsometricGraphDevelopment.exists_compact_graphCylinder_bound
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) (R bottom : ℝ) :
    ∃ K : Set E3, IsCompact K ∧ ∀ t : ℝ, D.graphCylinderInterior t R bottom ⊆ K := by
  obtain ⟨M, hM⟩ := (isCompact_closedCartesianDisk R).bddAbove_image
    D.contDiff_physicalHeight.continuous.continuousOn
  let K := euclideanVectorOfCoordinates ''
    ({x : PolarPoint | cartesianRadius x ≤ R} ×ˢ Icc bottom (max bottom M))
  refine ⟨K, ((isCompact_closedCartesianDisk R).prod isCompact_Icc).image
    continuous_euclideanVectorOfCoordinates, ?_⟩
  intro t v hv
  rcases hv with ⟨hr, hb, htop⟩
  have hM' : D.physicalHeight (planarRotation t (graphBaseProjection v)) ≤ M := by
    apply hM
    refine ⟨planarRotation t (graphBaseProjection v), ?_, rfl⟩
    change cartesianRadius (planarRotation t (graphBaseProjection v)) ≤ R
    simpa only [cartesianRadius_planarRotation] using hr.le
  refine ⟨(graphBaseProjection v, v 2), ?_, euclideanVectorOfCoordinates_of_vector v⟩
  exact ⟨hr.le, hb.le, (htop.le.trans hM').trans (le_max_right bottom M)⟩

theorem IsometricGraphDevelopment.graphCylinderInterior_volume_lt_top
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) (t R bottom : ℝ) :
    volume (D.graphCylinderInterior t R bottom) < ⊤ := by
  obtain ⟨K, hK, hsub⟩ := D.exists_compact_graphCylinder_bound R bottom
  exact (measure_mono (hsub t)).trans_lt hK.measure_lt_top

theorem IsometricGraphDevelopment.exists_bottom_with_positive_graphCylinder_volume
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) {R : ℝ} (hR : 0 < R) :
    ∃ bottom : ℝ, ∀ t : ℝ, 0 < volume (D.graphCylinderInterior t R bottom) := by
  obtain ⟨lo, hlo⟩ := (isCompact_closedCartesianDisk R).bddBelow_image
    D.contDiff_physicalHeight.continuous.continuousOn
  have hzero : lo ≤ D.physicalHeight 0 := by
    apply hlo
    exact ⟨0, by simpa [cartesianRadius] using hR.le, rfl⟩
  refine ⟨lo - 1, fun t => (D.isOpen_graphCylinderInterior t R (lo - 1)).measure_pos volume ?_⟩
  refine ⟨graphMap id (fun _ => lo - 1 / 2) 0, ?_⟩
  change cartesianRadius (graphBaseProjection (graphMap id (fun _ => lo - 1 / 2) 0)) < R ∧
    lo - 1 < graphMap id (fun _ => lo - 1 / 2) 0 2 ∧
    graphMap id (fun _ => lo - 1 / 2) 0 2 <
      D.physicalHeight (planarRotation t (graphBaseProjection (graphMap id (fun _ => lo - 1 / 2) 0)))
  simp only [graphBaseProjection_graphMap, id_eq, graphMap_two, map_zero]
  exact ⟨by simpa [cartesianRadius] using hR, by linarith, by linarith⟩

end ContinuousFlexibility
