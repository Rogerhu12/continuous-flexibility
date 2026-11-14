module

public import ContinuousFlexibility.Geometry.CapDisk
public import ContinuousFlexibility.Contracts.GraphFamilyImage
public import Mathlib.Topology.Sets.VietorisTopology
public import Mathlib.Topology.Separation.Connected

/-!
# Attachment of one fixed cap to the whole graph rotation family

The length is chosen from the actual simultaneous height bound. The same
core, development, radius, and cap are used for every real phase. This
proves the common rim and open physical collar; it does not construct the
marked sphere or supply the still-unproved analytic core.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility

open Set TopologicalSpace
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-! ## Attachment to the same actual graph family -/

def capAttachingRim (R h : ℝ) : Set E3 :=
  graphMap id (fun _ => h) '' {x : PolarPoint | cartesianRadius x = R}

def capDiskImage (R h L : ℝ) : Set E3 := Set.range (capDiskEmbeddingMap R h L)

def graphPhaseDiskImage {A : FlatAnnularCore} (D : IsometricGraphDevelopment A)
    (R t : ℝ) : Set E3 :=
  D.rotationFamily t '' {x : PolarPoint | cartesianRadius x ≤ R}

theorem capDisk_physical_boundary {R : ℝ} (hR : 0 < R) (h L : ℝ)
    {x : PolarPoint} (hx : cartesianRadius x = R) :
    cartesianRadius (R⁻¹ • x) = 1 ∧
      capDiskMap R h L (R⁻¹ • x) = graphMap id (fun _ => h) x := by
  have hy : cartesianRadius (R⁻¹ • x) = 1 := by
    rw [capDisk_radius_smul, abs_of_pos (inv_pos.mpr hR), hx, inv_mul_cancel₀ hR.ne']
  refine ⟨hy, ?_⟩
  simpa only [smul_smul, mul_inv_cancel₀ hR.ne', one_smul]
    using capDisk_boundary R h L hy

theorem IsometricGraphDevelopment.phase_flat_outside {A : FlatAnnularCore}
    (D : IsometricGraphDevelopment A) (t : ℝ) {x : PolarPoint}
    (hx : A.b < cartesianRadius x) :
    D.rotationFamily t x = graphMap id (fun _ => A.cRight) x := by
  rw [D.rotationFamily_fixed_outside t hx]
  simpa [graphMap] using D.map_standard_outside hx

theorem IsometricGraphDevelopment.phase_disk_projection_bound {A : FlatAnnularCore}
    (D : IsometricGraphDevelopment A) (t : ℝ) {R : ℝ} (hR : A.b ≤ R)
    {x : PolarPoint} (hx : cartesianRadius x ≤ R) :
    cartesianRadius (graphBaseProjection (D.rotationFamily t x)) ≤ R := by
  have hm : graphBaseProjection (D.rotationFamily t x) ∈
      graphBaseProjection '' (D.rotationFamily t '' {y : PolarPoint | cartesianRadius y ≤ R}) :=
    ⟨D.rotationFamily t x, ⟨x, hx, rfl⟩, rfl⟩
  rw [D.rotationFamily_projects_onto_disk t hR] at hm
  exact hm

/-- The actual compact cap and the actual graph disk meet exactly along the
same rim. The common lower bound is instantiated in the existence theorem. -/
theorem IsometricGraphDevelopment.graph_cap_intersection {A : FlatAnnularCore}
    (D : IsometricGraphDevelopment A) {R L lo : ℝ} (hR : A.b < R) (hL : 0 < L)
    (hlo : ∀ t : ℝ, ∀ x : PolarPoint, cartesianRadius x ≤ R → lo ≤ D.rotationFamily t x 2)
    (hbottom : A.cRight - L * capDrop < lo) (t : ℝ) :
    graphPhaseDiskImage D R t ∩ capDiskImage R A.cRight L = capAttachingRim R A.cRight := by
  have hRp : 0 < R := A.b_pos.trans hR
  ext v
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, ⟨y, hy⟩⟩
    change capDiskMap R A.cRight L (y : PolarPoint) = D.rotationFamily t x at hy
    have hb : A.cRight - L * capDrop < D.rotationFamily t x 2 :=
      hbottom.trans_le (hlo t x hx)
    have hrad : cartesianRadius
        (graphBaseProjection (capDiskMap R A.cRight L (y : PolarPoint))) ≤ R := by
      rw [hy]
      exact D.phase_disk_projection_bound t hR.le hx
    have hheight : A.cRight - L * capDrop < capDiskMap R A.cRight L (y : PolarPoint) 2 := by
      rw [hy]
      exact hb
    obtain ⟨hparam, htop⟩ := capDisk_upper_cylinder_meeting hRp hL A.cRight y.property hrad hheight
    have hpr : cartesianRadius (graphBaseProjection (D.rotationFamily t x)) = R := by
      rw [← hy]
      simp only [capDiskMap, graphBaseProjection_graphMap]
      rw [capDiskBase_radius hRp hL y.property, hparam]
      simp [capMeridianRadius]
    refine ⟨graphBaseProjection (D.rotationFamily t x), hpr, ?_⟩
    apply e3_eq_of_base_height
    · simp
    · simp only [graphMap_two]
      rw [← hy]
      exact htop.symm
  · rintro ⟨x, hx, rfl⟩
    constructor
    · refine ⟨x, hx.le, ?_⟩
      exact D.phase_flat_outside t (by rw [hx]; exact hR)
    · obtain ⟨hy, he⟩ := capDisk_physical_boundary hRp A.cRight L hx
      exact ⟨⟨R⁻¹ • x, hy.le⟩, he⟩

/-- Both branches agree on a genuine open physical collar for every phase.
The cap branch here is its smooth Cartesian extension across the disk rim. -/
theorem IsometricGraphDevelopment.graph_cap_open_collar {A : FlatAnnularCore}
    (D : IsometricGraphDevelopment A) {R L : ℝ} (hR : A.b < R) (hL : 0 < L)
    (t : ℝ) {x : PolarPoint} (hx : cartesianRadius x ∈ Ioo A.b (R + L / 4)) :
    D.rotationFamily t x = capDiskMap R A.cRight L (capDiskRimChart R L x) := by
  rw [D.phase_flat_outside t hx.1,
    capDiskMap_rimChart (A.b_pos.trans hR) hL A.cRight (A.b_pos.trans hx.1) hx.2]

/-- One actual length and one fixed cap work for all real phases of the
same constructed development. No cap-existence hypothesis is supplied. -/
theorem IsometricGraphDevelopment.exists_fixed_cap_attachment {A : FlatAnnularCore}
    (D : IsometricGraphDevelopment A) {R : ℝ} (hR : A.b < R) :
    ∃ L : ℝ, 0 < L ∧
      (∀ t : ℝ, graphPhaseDiskImage D R t ∩ capDiskImage R A.cRight L =
        capAttachingRim R A.cRight) ∧
      (∀ t : ℝ, ∀ x : PolarPoint, cartesianRadius x ∈ Ioo A.b (R + L / 4) →
        D.rotationFamily t x = capDiskMap R A.cRight L (capDiskRimChart R L x)) ∧
      ContDiff ℝ ∞ (capDiskMap R A.cRight L) ∧
      Topology.IsEmbedding (capDiskEmbeddingMap R A.cRight L) ∧
      ∀ y : PolarPoint, cartesianRadius y ≤ 1 →
        Function.Injective (fderiv ℝ (capDiskMap R A.cRight L) y) := by
  obtain ⟨lo, hi, hbounds⟩ := D.exists_rotationFamily_height_bounds R
  let L := capLength A.cRight lo 1
  have hL : 0 < L := capLength_pos A.cRight lo (by norm_num)
  have hbottom : A.cRight - L * capDrop < lo := capLength_bottom_lt A.cRight lo (by norm_num)
  refine ⟨L, hL, ?_, ?_, ?_⟩
  · intro t
    exact D.graph_cap_intersection hR hL (fun t x hx => (hbounds t x hx).1) hbottom t
  · intro t x hx
    exact D.graph_cap_open_collar hR hL t hx
  · exact capDiskMap_smooth_embedding (A.b_pos.trans hR) hL A.cRight

theorem isCompact_graphPhaseDiskImage {A : FlatAnnularCore}
    (D : IsometricGraphDevelopment A) (R t : ℝ) : IsCompact (graphPhaseDiskImage D R t) :=
  (isCompact_closedCartesianDisk R).image (D.rotationFamily_smooth t).continuous

theorem isCompact_capDiskImage {R L : ℝ} (hR : 0 < R) (hL : 0 < L) (h : ℝ) :
    IsCompact (capDiskImage R h L) := by
  let : CompactSpace capDiskDomain := isCompact_iff_compactSpace.mp isCompact_capDiskDomain_set
  exact isCompact_range (((contDiff_capDiskMap hR hL h).continuous).comp continuous_subtype_val)

def graphPhaseCompact {A : FlatAnnularCore} (D : IsometricGraphDevelopment A)
    (R t : ℝ) : Compacts E3 :=
  Compacts.map (D.rotationFamily t) (D.rotationFamily_smooth t).continuous
    ⟨{x : PolarPoint | cartesianRadius x ≤ R}, isCompact_closedCartesianDisk R⟩

@[simp] theorem coe_graphPhaseCompact {A : FlatAnnularCore} (D : IsometricGraphDevelopment A)
    (R t : ℝ) : (graphPhaseCompact D R t : Set E3) = graphPhaseDiskImage D R t := rfl

/-- Continuity of actual compact images is obtained from joint continuity,
rather than assumed for the family of sets. -/
theorem continuous_graphPhaseCompact {A : FlatAnnularCore}
    (D : IsometricGraphDevelopment A) (R : ℝ) : Continuous (graphPhaseCompact D R) := by
  let K : Compacts PolarPoint :=
    ⟨{x : PolarPoint | cartesianRadius x ≤ R}, isCompact_closedCartesianDisk R⟩
  have hg : Continuous (Function.uncurry (fun t : ℝ => D.rotationFamily t)) :=
    D.rotationFamily_joint_smooth.continuous
  exact Continuous.compacts_map' (f := fun _ : ℝ => K)
    (g := fun t : ℝ => D.rotationFamily t) continuous_const hg

def cappedGraphCompact {A : FlatAnnularCore} (D : IsometricGraphDevelopment A)
    {R L : ℝ} (hR : 0 < R) (hL : 0 < L) (t : ℝ) : Compacts E3 :=
  graphPhaseCompact D R t ⊔ ⟨capDiskImage R A.cRight L, isCompact_capDiskImage hR hL A.cRight⟩

@[simp] theorem coe_cappedGraphCompact {A : FlatAnnularCore} (D : IsometricGraphDevelopment A)
    {R L : ℝ} (hR : 0 < R) (hL : 0 < L) (t : ℝ) :
    (cappedGraphCompact D hR hL t : Set E3) =
      graphPhaseDiskImage D R t ∪ capDiskImage R A.cRight L := rfl

theorem continuous_cappedGraphCompact {A : FlatAnnularCore}
    (D : IsometricGraphDevelopment A) {R L : ℝ} (hR : 0 < R) (hL : 0 < L) :
    Continuous (cappedGraphCompact D hR hL) :=
  (continuous_graphPhaseCompact D R).sup continuous_const

theorem continuous_finite_compact_family_constant {T : Type*} [TopologicalSpace T]
    [PreconnectedSpace T] {f : T → Compacts E3} (hf : Continuous f)
    (hfinite : (Set.range f).Finite) (t s : T) : f t = f s := by
  by_contra hne
  have hn : (Set.range f).Nontrivial := ⟨f t, ⟨t, rfl⟩, f s, ⟨s, rfl⟩, hne⟩
  exact ((isPreconnected_range hf).infinite_of_nontrivial hn) hfinite

/-- The topological implication needed after a genuine finite-congruence
argument. Finite candidate images themselves still have to be supplied. -/
theorem cappedGraphCompact_constant_of_finite_range {A : FlatAnnularCore}
    (D : IsometricGraphDevelopment A) {R L : ℝ} (hR : 0 < R) (hL : 0 < L)
    (hfinite : (Set.range (cappedGraphCompact D hR hL)).Finite) (t s : ℝ) :
    cappedGraphCompact D hR hL t = cappedGraphCompact D hR hL s :=
  continuous_finite_compact_family_constant (continuous_cappedGraphCompact D hR hL) hfinite t s

end ContinuousFlexibility
