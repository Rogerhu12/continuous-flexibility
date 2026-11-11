import ContinuousFlexibility.Geometry.MarkerAmbientDeformation
import ContinuousFlexibility.Geometry.MarkedCapDiskCurvature
import ContinuousFlexibility.Contracts.GraphBoundaryNormals

/-!
# The actual marked-cap normal in physical graph coordinates

On the open flat top branch, the actual marked cap is locally the physical
graph of h + markerAmbientBump. The differential of the actual cap base is
bijective there, so its existing unit normal is also a normal of that graph.
Its positive vertical component gives a positive defining-function derivative
along the same actual normal ray. No enclosed-region identification is assumed
or supplied here; that separate identification will turn this into outwardness.
-/

noncomputable section

namespace ContinuousFlexibility

open Filter Set
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

theorem markedCapMap_physical_top_germ {R L : ℝ} (hL : 0 < L) (h k ρ : ℝ)
    {y : PolarPoint} (ht : capDiskParameter R L y < L / 4) :
    markedCapMap R h L k ρ =ᶠ[𝓝 y]
      (graphMap id (fun q => h + markerAmbientBump R L k ρ q)) ∘ capDiskBase R L := by
  have hc : Continuous (capDiskParameter R L) :=
    continuous_const.mul (continuous_const.sub continuous_cartesianRadius)
  have hn : ∀ᶠ z in 𝓝 y, capDiskParameter R L z < L / 4 :=
    (isOpen_lt hc continuous_const).mem_nhds ht
  filter_upwards [hn] with z hz
  have hh : capDiskHeight R h L z = h := capMeridianHeight_eq_left h hL hz.le
  apply e3_eq_of_base_height
  · simp only [Function.comp_apply, markedCapMap_base, graphBaseProjection_graphMap, id_eq]
  · simp only [Function.comp_apply, markedCapMap_height, graphMap_two, markedCapBump,
      markedCapCutoff_eq_one hL hz.le, one_mul, hh, markerAmbientBump]

theorem markedCapMap_physical_top {R L : ℝ} (hL : 0 < L) (h k ρ : ℝ)
    {y : PolarPoint} (ht : capDiskParameter R L y < L / 4) :
    markedCapMap R h L k ρ y =
      graphMap id (fun q => h + markerAmbientBump R L k ρ q) (capDiskBase R L y) :=
  (markedCapMap_physical_top_germ hL h k ρ ht).eq_of_nhds

/-- The actual cap normal is transported through the actual full-rank cap
base. This is a derivative calculation for the physical graph, not an ambient
homeomorphism rule for Euclidean normals. -/
theorem markedCapNormal_physical_top {R L k ρ : ℝ}
    (hR : 0 < R) (hL : 0 < L) (hρ : 0 < ρ) (hsmall : ρ < L / 64)
    (h : ℝ) {y : PolarPoint} (hy : cartesianRadius y ≤ 1)
    (ht : capDiskParameter R L y < L / 4) :
    IsUnitSurfaceNormal (graphMap id (fun q => h + markerAmbientBump R L k ρ q))
      (capDiskBase R L y) (markedCapNormal R L k ρ y) := by
  let F : PolarPoint → E3 := graphMap id (fun q => h + markerAmbientBump R L k ρ q)
  have hF : ContDiff ℝ ∞ F :=
    contDiff_graphMap contDiff_id (contDiff_const.add (contDiff_markerAmbientBump R L k ρ))
  have hφ : DifferentiableAt ℝ (capDiskBase R L) y :=
    (markedCap_contDiff_base hR hL).differentiable (by simp) y
  have hg : markedCapMap R h L k ρ =ᶠ[𝓝 y] F ∘ capDiskBase R L :=
    markedCapMap_physical_top_germ hL h k ρ ht
  have hn := isUnitSurfaceNormal_markedCap (k := k) hR hL hρ hsmall h y
  have hcomp : IsUnitSurfaceNormal (F ∘ capDiskBase R L) y (markedCapNormal R L k ρ y) := by
    refine ⟨hn.1, fun v => ?_⟩
    rw [← hg.fderiv_eq (𝕜 := ℝ)]
    exact hn.2 v
  have hs : Function.Surjective (fderiv ℝ (capDiskBase R L) y) :=
    LinearMap.surjective_of_injective
      (f := (fderiv ℝ (capDiskBase R L) y).toLinearMap)
      (markedCap_base_fderiv_injective_top hR hL h hy ht)
  exact hcomp.of_comp (hF.differentiable (by simp) (capDiskBase R L y)) hφ hs

theorem markedCapNormal_top_height_pos {R L : ℝ} (hL : 0 < L) (k ρ : ℝ)
    {y : PolarPoint} (ht : capDiskParameter R L y < L / 4) :
    0 < markedCapNormal R L k ρ y 2 := by
  rw [markedCapNormal_eq_top hL k ρ ht.le, graphUpwardNormal_two]
  exact div_pos (by norm_num) (graphAreaDensity_pos _ _)

theorem markedCapMap_top_defining_eq_zero {R L : ℝ} (hL : 0 < L) (h k ρ : ℝ)
    {y : PolarPoint} (ht : capDiskParameter R L y < L / 4) :
    graphDefiningFunction (fun q => h + markerAmbientBump R L k ρ q)
      (markedCapMap R h L k ρ y) = 0 := by
  rw [markedCapMap_physical_top hL h k ρ ht]
  exact graphDefiningFunction_graph _ _

/-- The derivative is along the same explicit marked-cap normal and through
the actual marked point. The actual inside-region germ remains a separate input. -/
theorem markedCapNormal_top_defining_derivative_pos {R L k ρ : ℝ}
    (hR : 0 < R) (hL : 0 < L) (hρ : 0 < ρ) (hsmall : ρ < L / 64)
    (h : ℝ) {y : PolarPoint} (hy : cartesianRadius y ≤ 1)
    (ht : capDiskParameter R L y < L / 4) :
    ∃ c : ℝ, 0 < c ∧ HasDerivAt (fun s : ℝ =>
      graphDefiningFunction (fun q => h + markerAmbientBump R L k ρ q)
        (markedCapMap R h L k ρ y + s • markedCapNormal R L k ρ y)) c 0 := by
  let z : PolarPoint → ℝ := fun q => h + markerAmbientBump R L k ρ q
  let q := capDiskBase R L y
  let n := markedCapNormal R L k ρ y
  have hz : DifferentiableAt ℝ z q :=
    (contDiff_const.add (contDiff_markerAmbientBump R L k ρ)).differentiable (by simp) q
  have hn : IsUnitSurfaceNormal (graphMap id z) q n :=
    markedCapNormal_physical_top hR hL hρ hsmall h hy ht
  have hnz : 0 < n 2 := markedCapNormal_top_height_pos hL k ρ ht
  have hc : 0 < n 2 - fderiv ℝ z q (graphBaseProjection n) :=
    graph_normal_defining_derivative_pos hz hn hnz
  refine ⟨n 2 - fderiv ℝ z q (graphBaseProjection n), hc, ?_⟩
  have hpoint : markedCapMap R h L k ρ y = graphMap id z q :=
    markedCapMap_physical_top hL h k ρ ht
  have hfun : graphNormalRayLevel z q n = (fun s : ℝ =>
      graphDefiningFunction z (markedCapMap R h L k ρ y + s • n)) := by
    funext s
    rw [graphNormalRayLevel_eq_defining, hpoint]
  have hd := hasDerivAt_graphNormalRayLevel hz n
  rw [hfun] at hd
  exact hd

end ContinuousFlexibility
