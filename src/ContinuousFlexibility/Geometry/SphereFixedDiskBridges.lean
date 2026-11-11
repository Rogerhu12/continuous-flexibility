import ContinuousFlexibility.Geometry.SphereFixedDisks
import ContinuousFlexibility.Statements.MainGeometry

/-!
# Fixed disk regions for the actual sphere family

The graph disk and complementary cap are the closed northern and southern
hemispheres. The inner disk has physical radius `a` in the scaled northern
chart. The homeomorphisms identify these subsets with the closed Euclidean
unit disk in the direction required by `Statements.DiskRegions`. The open rim
agreement gives pointwise stationarity on the entire complementary cap,
including the equator.
-/

noncomputable section

namespace ContinuousFlexibility

open Set Filter
open scoped Topology

private def euclideanUnitDiskClosedBallHomeomorph :
    {u : Statements.E2 // ‖u‖ ≤ 1} ≃ₜ
      ↥(Metric.closedBall (0 : Statements.E2) 1) := by
  refine Homeomorph.setCongr ?_
  ext u
  change ‖u‖ ≤ (1 : ℝ) ↔ dist u 0 ≤ 1
  rw [dist_zero_right]

/-- The three actual disks, with interior and closure taken in the standard sphere. -/
def sphereDiskRegions {R a : ℝ} (hR : 0 < R) (ha : 0 < a) (haR : a < R) :
    Statements.DiskRegions where
  graphDisk := sphereGraphDisk
  innerDisk := sphereInnerDisk R a
  cap := sphereComplementaryCap
  graph_closed := isClosed_sphereGraphDisk
  inner_closed := isClosed_sphereInnerDisk hR a
  cap_closed := isClosed_sphereComplementaryCap
  graph_disk := ⟨euclideanUnitDiskClosedBallHomeomorph.trans sphereGraphDiskStandardHomeomorph.symm⟩
  inner_disk := ⟨euclideanUnitDiskClosedBallHomeomorph.trans
    (sphereInnerDiskStandardHomeomorph hR ha).symm⟩
  cap_disk := ⟨euclideanUnitDiskClosedBallHomeomorph.trans
    sphereComplementaryCapStandardHomeomorph.symm⟩
  graph_interior := sphereGraphDisk_interior_nonempty
  inner_interior := sphereInnerDisk_interior_nonempty hR ha
  cap_interior := sphereComplementaryCap_interior_nonempty
  graph_regular := closure_interior_sphereGraphDisk
  inner_regular := closure_interior_sphereInnerDisk hR ha
  cap_regular := closure_interior_sphereComplementaryCap
  nested := sphereInnerDisk_subset_interior_graphDisk hR haR
  complement := sphereComplementaryCap_eq_compl_interior

/-- The scaled inner disk has radius `a / R` in the original northern chart. -/
theorem sphereDiskRegions_inner_region {R a : ℝ} (hR : 0 < R) (ha : 0 < a) (haR : a < R) :
    (sphereDiskRegions hR ha haR).innerDisk =
      {x : Statements.S2 | x ∈ sphereNorthSource ∧
        cartesianRadius (sphereNorthChart x) ≤ a / R} := by
  change sphereInnerDisk R a = sphereNorthClosedDisk (a / R)
  exact sphereInnerDisk_eq_northClosedDisk hR a

/-- The actual inner disk and the closed complementary cap stay fixed on the
same graph and cap family used in the geometric closure theorem. -/
def sphereGraphCapFamily_fixedDiskRegions {A : FlatAnnularCore}
    (D : IsometricGraphDevelopment A) {C : PolarPoint → E3} {R L : ℝ}
    (hR : A.b < R)
    (hcollar : ∀ y : PolarPoint, cartesianRadius y = 1 →
      (C ∘ capSphereRadialMap (capSphereRatio R L)) =ᶠ[𝓝 y]
        fun z => graphMap id (fun _ => A.cRight) ((R / cartesianRadius z ^ 2) • z)) :
    Statements.FixedDiskRegions (sphereGraphCapFamily D C R L) where
  toDiskRegions := sphereDiskRegions (A.b_pos.trans hR) A.a_pos (A.a_lt_b.trans hR)
  fixed_inner t x hx := sphereGraphCapFamily_fixed_innerDisk D C hR L t (x := x) hx
  fixed_cap t x hx := sphereGraphCapFamily_fixed_closed_south D hR hcollar x hx t

/-- The fixed disk data for the marked family at the supplied `R`, `L`, `k`,
and `ρ`. The actual marked cap agrees with the graph on the open rim collar. -/
def IsometricGraphDevelopment.markedSphereFixedDiskRegions {A : FlatAnnularCore}
    (D : IsometricGraphDevelopment A) {R L k ρ : ℝ}
    (hR : A.b < R) (hL : 0 < L) (hρ : 0 < ρ) (hsmall : ρ < L / 64) :
    Statements.FixedDiskRegions
      (sphereGraphCapFamily D (markedCapMap R A.cRight L k ρ) R L) :=
  sphereGraphCapFamily_fixedDiskRegions D hR (fun _ hy =>
    markedCapMap_capSphereRadialMap_rim_germ (k := k)
      (A.b_pos.trans hR) hL hρ hsmall A.cRight hy)

end ContinuousFlexibility
