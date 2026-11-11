import ContinuousFlexibility.Contracts.PlanarDevelopment
import ContinuousFlexibility.Geometry.GraphEmbedding

/-!
# An actual Euclidean graph from the analytic annular core

All fields of the output below are constructed from the same planar map.
In particular, this is a proved output interface, not an assumed embedding
or an additional existence input. The remaining analytic obligation is to
construct a `FlatAnnularCore`; sphere closure and noncongruence are separate.
-/

noncomputable section

namespace ContinuousFlexibility

open Set
open scoped ContDiff

structure IsometricGraphDevelopment (A : FlatAnnularCore) where
  planar : PolarPoint ≃ₜ PolarPoint
  smooth_planar : ContDiff ℝ ∞ (planar : PolarPoint → PolarPoint)
  smooth_inverse : ContDiff ℝ ∞ (planar.symm : PolarPoint → PolarPoint)
  normalized_outside : ∀ x, A.b < cartesianRadius x → planar x = x
  preserves_disk : planar '' {x | cartesianRadius x ≤ A.b} = {x | cartesianRadius x ≤ A.b}
  remainder_metric : ∀ x u v : PolarPoint,
    coordinateEuclideanPair (fderiv ℝ (planar : PolarPoint → PolarPoint) x u)
      (fderiv ℝ (planar : PolarPoint → PolarPoint) x v) =
        cartesianRemainder A.w A.cartesianHeight x u v
  smooth_graph : ContDiff ℝ ∞ (graphMap planar A.cartesianHeight)
  embedding_graph : Topology.IsEmbedding (graphMap planar A.cartesianHeight)
  immersion_graph : ∀ x, Function.Injective (fderiv ℝ (graphMap planar A.cartesianHeight) x)
  graph_metric : ∀ x u v : PolarPoint,
    inner ℝ (fderiv ℝ (graphMap planar A.cartesianHeight) x u)
      (fderiv ℝ (graphMap planar A.cartesianHeight) x v) = cartesianMetric A.w x u v

theorem FlatAnnularCore.exists_isometricGraphDevelopment (A : FlatAnnularCore) :
    Nonempty (IsometricGraphDevelopment A) := by
  obtain ⟨e, he, hei, hout, himage, hmetric⟩ := A.exists_planarDevelopment
  obtain ⟨hG, hGe, hGi, hGm⟩ :=
    graphMap_smooth_embedding_with_metric e he A.contDiff_cartesianHeight hmetric
  exact ⟨{
    planar := e
    smooth_planar := he
    smooth_inverse := hei
    normalized_outside := hout
    preserves_disk := himage
    remainder_metric := hmetric
    smooth_graph := hG
    embedding_graph := hGe
    immersion_graph := hGi
    graph_metric := hGm }⟩

/-- Fix one common constructed development for all later geometric uses. -/
def FlatAnnularCore.graphDevelopment (A : FlatAnnularCore) : IsometricGraphDevelopment A :=
  Classical.choice A.exists_isometricGraphDevelopment

def IsometricGraphDevelopment.map {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) :
    PolarPoint → E3 := graphMap D.planar A.cartesianHeight

theorem IsometricGraphDevelopment.embedding_restrict
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) (S : Set PolarPoint) :
    Topology.IsEmbedding (fun x : S => D.map x) :=
  isEmbedding_graphMap_restrict D.planar A.contDiff_cartesianHeight.continuous S

theorem graphBaseProjection_image_graphMap
    (P : PolarPoint → PolarPoint) (Z : PolarPoint → ℝ) (S : Set PolarPoint) :
    graphBaseProjection '' (graphMap P Z '' S) = P '' S := by
  rw [Set.image_image]
  congr 1
  funext x
  exact graphBaseProjection_graphMap P Z x

theorem IsometricGraphDevelopment.graph_projects_onto_disk
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) {R : ℝ} (hR : A.b ≤ R) :
    graphBaseProjection '' (D.map '' {x | cartesianRadius x ≤ R}) =
      {x | cartesianRadius x ≤ R} := by
  rw [IsometricGraphDevelopment.map, graphBaseProjection_image_graphMap]
  exact image_larger_disk_of_normalized_homeomorph D.planar hR D.normalized_outside

theorem IsometricGraphDevelopment.map_standard_outside
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) {x : PolarPoint}
    (hx : A.b < cartesianRadius x) :
    D.map x = x.1 • e3Basis 0 + x.2 • e3Basis 1 + A.cRight • e3Basis 2 := by
  simp only [IsometricGraphDevelopment.map, graphMap, D.normalized_outside x hx,
    A.cartesianHeight_right hx.le]

/-- Use the enlarged outer radius so that the graph disk has a genuine
open horizontal collar inside its attaching boundary. The original core
radius `b` alone would not supply such an inner collar. -/
theorem AnnularSolution.exists_isometricGraphDisk (A : AnnularSolution) :
    ∃ D : IsometricGraphDevelopment A.toFlatAnnularCore,
      Topology.IsEmbedding (fun x : {x : PolarPoint | cartesianRadius x ≤ A.outerRadius} => D.map x) ∧
      graphBaseProjection '' (D.map '' {x | cartesianRadius x ≤ A.outerRadius}) =
        {x | cartesianRadius x ≤ A.outerRadius} ∧
      ∀ x : PolarPoint, cartesianRadius x ∈ Ioo A.b A.outerRadius →
        D.map x = x.1 • e3Basis 0 + x.2 • e3Basis 1 + A.cRight • e3Basis 2 := by
  let D := A.toFlatAnnularCore.graphDevelopment
  refine ⟨D, D.embedding_restrict _, D.graph_projects_onto_disk A.b_lt_outer.le, ?_⟩
  intro x hx
  exact D.map_standard_outside hx.1

end ContinuousFlexibility
