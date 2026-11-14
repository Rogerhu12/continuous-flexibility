module

public import ContinuousFlexibility.Geometry.CapDiskOutward
public import ContinuousFlexibility.Geometry.OutwardNormalRays
public import ContinuousFlexibility.Geometry.SphereNormals
public import ContinuousFlexibility.Contracts.GraphCapHomeomorph

/-!
# Actual outward normals of the moving graph and the whole unmarked cap

At every cap point, the actual graph-cap body agrees locally with the original
cap body. Outside the graph support this follows from local identity of the
actual ambient homeomorphism. At a bottom point inside the attaching cylinder,
both roofs stay strictly above a whole neighborhood of that point.

These are equalities of actual regions in neighborhoods, so they transport the
same Euclidean normal rays. The closed graph disk includes the common rim.
All statements retain the same given cap length and actual bottom-height gap.
The inserted marker and the final marked inside region are separate steps.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility

open Filter Set
open scoped Topology

set_option backward.isDefEq.respectTransparency false

/-- Away from the actual graph support, the two inside regions have the same
germ. This uses identity on a whole neighborhood, not only fixed boundary points. -/
theorem IsometricGraphDevelopment.graphCapInterior_outside_germ
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) {R L : ℝ}
    (hR : A.b < R) (hL : 0 < L) (t : ℝ)
    (hb : ∀ q : PolarPoint, cartesianRadius q ≤ R →
      A.cRight - L * capDrop < D.physicalHeight (planarRotation t q))
    {p : E3} (hp : A.b < cartesianRadius (graphBaseProjection p)) :
    D.graphCapInterior t R L =ᶠ[𝓝 p] capRevolutionInterior R A.cRight L := by
  apply Filter.eventuallyEqSet_iff.mpr
  have hnear : ∀ᶠ v in 𝓝 p, A.b < cartesianRadius (graphBaseProjection v) :=
    (isOpen_lt continuous_const
      (continuous_cartesianRadius.comp continuous_graphBaseProjection)).mem_nhds hp
  filter_upwards [hnear] with v hv
  have hm := D.graphCapHomeomorph_mem hR hL t hb v
  rw [D.graphCapHomeomorph_outside hR hL t hb hv] at hm
  exact hm

/-- The actual moving inside region and the original cap body agree in a
neighborhood of every point of the closed cap disk, including its axis and rim. -/
theorem IsometricGraphDevelopment.graphCapInterior_capDisk_germ
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) {R L : ℝ}
    (hR : A.b < R) (hL : 0 < L) (t : ℝ)
    (hb : ∀ q : PolarPoint, cartesianRadius q ≤ R →
      A.cRight - L * capDrop < D.physicalHeight (planarRotation t q))
    {y : PolarPoint} (hy : cartesianRadius y ≤ 1) :
    D.graphCapInterior t R L =ᶠ[𝓝 (capDiskMap R A.cRight L y)]
      capRevolutionInterior R A.cRight L := by
  let p := capDiskMap R A.cRight L y
  change D.graphCapInterior t R L =ᶠ[𝓝 p] capRevolutionInterior R A.cRight L
  by_cases hr : cartesianRadius (graphBaseProjection p) < R
  · have hp : p 2 = A.cRight - L * capDrop :=
      capDisk_inside_cylinder_bottom (A.b_pos.trans hR) hL A.cRight hy hr
    have hheight : Continuous (fun v : E3 => v 2) :=
      (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).continuous
    have hradius := continuous_cartesianRadius.comp continuous_graphBaseProjection
    have hroof := D.contDiff_physicalHeight.continuous.comp
      ((planarRotation t).continuous.comp continuous_graphBaseProjection)
    let V : Set E3 := {v | cartesianRadius (graphBaseProjection v) < R ∧
      v 2 < A.cRight ∧ v 2 < D.physicalHeight (planarRotation t (graphBaseProjection v))}
    have hV : IsOpen V :=
      (isOpen_lt hradius continuous_const).inter
        ((isOpen_lt hheight continuous_const).inter (isOpen_lt hheight hroof))
    have hpV : p ∈ V := by
      refine ⟨hr, ?_, ?_⟩
      · rw [hp]
        linarith [mul_pos hL capDrop_pos]
      · rw [hp]
        exact hb _ hr.le
    apply Filter.eventuallyEqSet_iff.mpr
    filter_upwards [hV.mem_nhds hpV] with v hv
    change cartesianRadius (graphBaseProjection v) < R ∧
      v 2 < A.cRight ∧ v 2 < D.physicalHeight (planarRotation t (graphBaseProjection v)) at hv
    rw [D.graphCapInterior_partition hR t]
    constructor
    · rintro (hcyl | hout)
      · exact (capRevolutionInterior_mem_of_radius_lt hL hv.1).mpr ⟨hcyl.2.1, hv.2.1⟩
      · exact hout.1
    · intro hcap
      exact Or.inl ⟨hv.1, hcap.1.1, hv.2.2⟩
  · exact D.graphCapInterior_outside_germ hR hL t hb
      (hR.trans_le (le_of_not_gt hr))

/-- The explicit cap normal is outward for the same actual moving graph-cap
body at every point of the closed cap disk. -/
theorem IsometricGraphDevelopment.capDiskNormal_pointsOutwardFrom_graphCapInterior
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) {R L : ℝ}
    (hR : A.b < R) (hL : 0 < L) (t : ℝ)
    (hb : ∀ q : PolarPoint, cartesianRadius q ≤ R →
      A.cRight - L * capDrop < D.physicalHeight (planarRotation t q))
    {y : PolarPoint} (hy : cartesianRadius y ≤ 1) :
    PointsOutwardFrom (D.graphCapInterior t R L)
      (capDiskMap R A.cRight L y) (capDiskNormal R L y) :=
  (capDiskNormal_pointsOutwardFrom (A.b_pos.trans hR) hL A.cRight hy).congr_germ
    (D.graphCapInterior_capDisk_germ hR hL t hb hy).symm

/-- The actual developed graph normal is outward on the entire closed graph
disk. The rim is handled by the same cap neighborhood and the same vertical normal. -/
theorem IsometricGraphDevelopment.rotationNormal_pointsOutwardFrom_graphCapInterior_closed
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) {R L : ℝ}
    (hR : A.b < R) (hL : 0 < L) (t : ℝ)
    (hb : ∀ q : PolarPoint, cartesianRadius q ≤ R →
      A.cRight - L * capDrop < D.physicalHeight (planarRotation t q))
    {x : PolarPoint} (hx : cartesianRadius x ≤ R) :
    PointsOutwardFrom (D.graphCapInterior t R L)
      (D.rotationFamily t x) (D.rotationNormal t x) := by
  rcases lt_or_eq_of_le hx with hxlt | hxR
  · have hr := D.rotationFamily_base_radius_lt t hR hxlt
    apply D.rotationNormal_pointsOutwardFrom_graphCapInterior hR t x hr
    rw [D.rotationFamily_physical_height]
    exact hb _ hr.le
  · have hbx : A.b < cartesianRadius x := by rw [hxR]; exact hR
    obtain ⟨hy, hcap⟩ := capDisk_physical_boundary (A.b_pos.trans hR) A.cRight L hxR
    have ht : capDiskParameter R L (R⁻¹ • x) ≤ L / 4 := by
      simp only [capDiskParameter, hy, sub_self, mul_zero]
      exact div_nonneg hL.le (by norm_num)
    have hn := capDiskNormal_top_collar R hL ht
    have hout := D.capDiskNormal_pointsOutwardFrom_graphCapInterior hR hL t hb hy.le
    rw [D.phase_flat_outside t hbx, D.rotationNormal_outside t hbx]
    simpa only [hcap, hn] using hout

end ContinuousFlexibility
