module

public import ContinuousFlexibility.Contracts.GraphCylinderVolume
public import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Actual inward and outward normal rays at the graph boundary

Outwardness is proved by the two sides of the explicitly constructed open
subgraph, rather than supplied as a name or an unverified orientation field.
The eventual full cap-inside region must still be identified with this region
near its central graph portion.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility

open Set Filter MeasureTheory
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

theorem positive_derivative_two_sided_sign
    {f : ℝ → ℝ} {c : ℝ} (hf : HasDerivAt f c 0) (hzero : f 0 = 0) (hc : 0 < c) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ s ∈ Ioo (0 : ℝ) ε, 0 < f s ∧ f (-s) < 0 := by
  have hp : ∀ᶠ s in 𝓝[≠] (0 : ℝ), 0 < slope f 0 s :=
    hf.tendsto_slope.eventually (Ioi_mem_nhds hc)
  rw [eventually_nhdsWithin_iff] at hp
  simp only [mem_compl_iff, mem_singleton_iff] at hp
  obtain ⟨ε, hε, hbound⟩ := Metric.eventually_nhds_iff.mp hp
  refine ⟨ε, hε, fun s hs => ?_⟩
  have hpos := hbound (y := s) (by simpa [Real.dist_eq, abs_of_pos hs.1] using hs.2) hs.1.ne'
  have hneg := hbound (y := -s) (by simpa [Real.dist_eq, abs_neg, abs_of_pos hs.1] using hs.2)
    (neg_ne_zero.mpr hs.1.ne')
  simp only [slope, sub_zero, hzero, smul_eq_mul, vsub_eq_sub] at hpos hneg
  constructor
  · exact (mul_pos_iff_of_pos_left (inv_pos.mpr hs.1)).mp hpos
  · have hi : (-s)⁻¹ < 0 := by simpa only [inv_neg] using neg_neg_of_pos (inv_pos.mpr hs.1)
    by_contra hn
    exact (not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg hi.le (le_of_not_gt hn))) hneg

def PointsOutwardFrom (Ω : Set E3) (p n : E3) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ s ∈ Ioo (0 : ℝ) ε,
    p - s • n ∈ Ω ∧ p + s • n ∉ closure Ω

def graphDefiningFunction (z : PolarPoint → ℝ) (v : E3) : ℝ :=
  v 2 - z (graphBaseProjection v)

theorem continuous_graphDefiningFunction {z : PolarPoint → ℝ} (hz : Continuous z) :
    Continuous (graphDefiningFunction z) :=
  (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).continuous.sub
    (hz.comp continuous_graphBaseProjection)

@[simp] theorem graphDefiningFunction_graph (z : PolarPoint → ℝ) (x : PolarPoint) :
    graphDefiningFunction z (graphMap id z x) = 0 := by
  simp [graphDefiningFunction]

theorem graph_normal_defining_derivative_pos {z : PolarPoint → ℝ} {x : PolarPoint}
    (hz : DifferentiableAt ℝ z x) {n : E3}
    (hn : IsUnitSurfaceNormal (graphMap id z) x n) (hnz : 0 < n 2) :
    0 < n 2 - fderiv ℝ z x (graphBaseProjection n) := by
  have h0 := hn.2 ((1, 0) : PolarPoint)
  have h1 := hn.2 ((0, 1) : PolarPoint)
  rw [fderiv_graphMap differentiableAt_id hz, e3_inner_coordinates] at h0 h1
  simp only [graphDifferential_apply_zero, graphDifferential_apply_one,
    graphDifferential_apply_two, fderiv_id, ContinuousLinearMap.id_apply,
    one_mul, zero_mul, add_zero, zero_add] at h0 h1
  have heq : n 2 - fderiv ℝ z x (graphBaseProjection n) = n 2 * graphAreaSq z x := by
    rw [height_fderiv_coordinates]
    change n 2 - (radialPartial z x * n 0 + angularPartial z x * n 1) = _
    unfold graphAreaSq radialPartial angularPartial
    linear_combination -fderiv ℝ z x (1, 0) * h0 - fderiv ℝ z x (0, 1) * h1
  rw [heq]
  exact mul_pos hnz (graphAreaSq_pos z x)

def graphNormalRayLevel (z : PolarPoint → ℝ) (x : PolarPoint) (n : E3) (s : ℝ) : ℝ :=
  z x + s * n 2 - z (x + s • graphBaseProjection n)

theorem hasDerivAt_graphNormalRayLevel {z : PolarPoint → ℝ} {x : PolarPoint}
    (hz : DifferentiableAt ℝ z x) (n : E3) :
    HasDerivAt (graphNormalRayLevel z x n)
      (n 2 - fderiv ℝ z x (graphBaseProjection n)) 0 := by
  have hline : HasDerivAt (fun s : ℝ => x + s • graphBaseProjection n) (graphBaseProjection n) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (graphBaseProjection n)).const_add x
  have hz' : HasFDerivAt z (fderiv ℝ z x) (x + (0 : ℝ) • graphBaseProjection n) := by
    simpa using hz.hasFDerivAt
  have hcomp := hz'.comp_hasDerivAt 0 hline
  have hfirst : HasDerivAt (fun s : ℝ => z x + s * n 2) (n 2) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (n 2)).const_add (z x)
  exact hfirst.sub hcomp

theorem graphNormalRayLevel_eq_defining (z : PolarPoint → ℝ) (x : PolarPoint) (n : E3) (s : ℝ) :
    graphNormalRayLevel z x n s =
      graphDefiningFunction z (graphMap id z x + s • n) := by
  have hb : graphBaseProjection (graphMap id z x + s • n) = x + s • graphBaseProjection n := by
    apply Prod.ext <;> simp [graphBaseProjection]
  have hh : (graphMap id z x + s • n) 2 = z x + s * n 2 := by simp
  rw [graphDefiningFunction, hb, hh]
  rfl

def graphCylinderRegion (z : PolarPoint → ℝ) (R bottom : ℝ) : Set E3 :=
  {v | cartesianRadius (graphBaseProjection v) < R ∧ bottom < v 2 ∧ v 2 < z (graphBaseProjection v)}

theorem graph_normal_pointsOutwardFrom {z : PolarPoint → ℝ} (hz : ContDiff ℝ ∞ z)
    {x : PolarPoint} {n : E3} (hn : IsUnitSurfaceNormal (graphMap id z) x n) (hnz : 0 < n 2)
    {R bottom : ℝ} (hr : cartesianRadius x < R) (hb : bottom < z x) :
    PointsOutwardFrom (graphCylinderRegion z R bottom) (graphMap id z x) n := by
  obtain ⟨ε, hε, hsigns⟩ := positive_derivative_two_sided_sign
    (hasDerivAt_graphNormalRayLevel (hz.differentiable (by simp) x) n)
    (by simp [graphNormalRayLevel])
    (graph_normal_defining_derivative_pos (hz.differentiable (by simp) x) hn hnz)
  let U : Set E3 := {v | cartesianRadius (graphBaseProjection v) < R ∧ bottom < v 2}
  have hU : IsOpen U := (isOpen_lt
    (continuous_cartesianRadius.comp continuous_graphBaseProjection) continuous_const).inter
      (isOpen_lt continuous_const (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).continuous)
  have hc : Continuous (fun s : ℝ => graphMap id z x + s • n) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hnhood : ∀ᶠ s in 𝓝 (0 : ℝ), graphMap id z x + s • n ∈ U :=
    (hU.preimage hc).mem_nhds (by simpa [U] using (show cartesianRadius x < R ∧ bottom < z x from ⟨hr, hb⟩))
  obtain ⟨δ, hδ, hδbound⟩ := Metric.eventually_nhds_iff.mp hnhood
  have hclosure : closure (graphCylinderRegion z R bottom) ⊆
      {v | graphDefiningFunction z v ≤ 0} := by
    apply closure_minimal
    · intro v hv
      exact (sub_neg.mpr hv.2.2).le
    · exact isClosed_le (continuous_graphDefiningFunction hz.continuous) continuous_const
  refine ⟨min ε δ, lt_min hε hδ, fun s hs => ?_⟩
  have hsε : s ∈ Ioo (0 : ℝ) ε := ⟨hs.1, hs.2.trans_le (min_le_left ε δ)⟩
  have hsδ : s < δ := hs.2.trans_le (min_le_right ε δ)
  have hsign := hsigns s hsε
  rw [graphNormalRayLevel_eq_defining, graphNormalRayLevel_eq_defining] at hsign
  have hbase : graphMap id z x - s • n ∈ U := by
    have hh := hδbound (y := -s) (by simpa [Real.dist_eq, abs_neg, abs_of_pos hs.1] using hsδ)
    simpa only [neg_smul, sub_eq_add_neg] using hh
  constructor
  · refine ⟨hbase.1, hbase.2, ?_⟩
    have hh : graphDefiningFunction z (graphMap id z x - s • n) < 0 := by
      simpa only [neg_smul, sub_eq_add_neg] using hsign.2
    exact sub_neg.mp hh
  · intro hmem
    exact not_le_of_gt hsign.1 (hclosure hmem)

theorem PointsOutwardFrom.mem_frontier {Ω : Set E3} {p n : E3}
    (h : PointsOutwardFrom Ω p n) : p ∈ frontier Ω := by
  obtain ⟨ε, hε, hside⟩ := h
  have hin : ∀ᶠ s in 𝓝[>] (0 : ℝ), p - s • n ∈ Ω := by
    filter_upwards [Ioo_mem_nhdsGT hε] with s hs
    exact (hside s hs).1
  have hout : ∀ᶠ s in 𝓝[>] (0 : ℝ), p + s • n ∈ Ωᶜ := by
    filter_upwards [Ioo_mem_nhdsGT hε] with s hs
    exact fun hm => (hside s hs).2 (subset_closure hm)
  have hm : Tendsto (fun s : ℝ => p - s • n) (𝓝[>] (0 : ℝ)) (𝓝 p) := by
    have hc : Continuous (fun s : ℝ => p - s • n) :=
      continuous_const.sub (continuous_id.smul continuous_const)
    have ht := (hc.continuousAt : ContinuousAt (fun s : ℝ => p - s • n) 0).tendsto
    simpa only [zero_smul, sub_zero] using ht.mono_left
      (show 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ) from nhdsWithin_le_nhds)
  have hp : Tendsto (fun s : ℝ => p + s • n) (𝓝[>] (0 : ℝ)) (𝓝 p) := by
    have hc : Continuous (fun s : ℝ => p + s • n) :=
      continuous_const.add (continuous_id.smul continuous_const)
    have ht := (hc.continuousAt : ContinuousAt (fun s : ℝ => p + s • n) 0).tendsto
    simpa only [zero_smul, add_zero] using ht.mono_left
      (show 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ) from nhdsWithin_le_nhds)
  rw [frontier_eq_closure_inter_closure]
  exact ⟨mem_closure_of_tendsto hm hin, mem_closure_of_tendsto hp hout⟩

theorem IsUnitSurfaceNormal.of_comp
    {F : PolarPoint → E3} {φ : PolarPoint → PolarPoint} {x : PolarPoint} {N : E3}
    (hN : IsUnitSurfaceNormal (F ∘ φ) x N)
    (hF : DifferentiableAt ℝ F (φ x)) (hφ : DifferentiableAt ℝ φ x)
    (hs : Function.Surjective (fderiv ℝ φ x)) :
    IsUnitSurfaceNormal F (φ x) N := by
  refine ⟨hN.1, fun v => ?_⟩
  obtain ⟨u, hu⟩ := hs v
  have h := hN.2 u
  simpa only [fderiv_comp x hF hφ, ContinuousLinearMap.comp_apply, hu] using h

theorem IsometricGraphDevelopment.rotationFamily_eq_physical_graph
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) (t : ℝ) (x : PolarPoint) :
    D.rotationFamily t x = graphMap id (fun y => D.physicalHeight (planarRotation t y))
      (rotationConjugate t D.planar x) := by
  apply e3_eq_of_base_height
  · simp only [IsometricGraphDevelopment.rotationFamily, graphBaseProjection_graphMap, id_eq]
  · simpa only [IsometricGraphDevelopment.rotationFamily, graphBaseProjection_graphMap,
      graphMap_two] using D.rotationFamily_physical_height t x

theorem IsometricGraphDevelopment.rotationNormal_physical_graph
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) (t : ℝ) (x : PolarPoint) :
    IsUnitSurfaceNormal (graphMap id (fun y => D.physicalHeight (planarRotation t y)))
      (rotationConjugate t D.planar x) (D.rotationNormal t x) := by
  let φ := rotationConjugate t D.planar
  have hs : ContDiff ℝ ∞ (φ : PolarPoint → PolarPoint) :=
    contDiff_rotationConjugate t D.planar D.smooth_planar
  have hi : ContDiff ℝ ∞ (φ.symm : PolarPoint → PolarPoint) :=
    (planarRotation (-t)).contDiff.comp (D.smooth_inverse.comp (planarRotation t).contDiff)
  have hg : ContDiff ℝ ∞ (graphMap id (fun y => D.physicalHeight (planarRotation t y))) :=
    contDiff_graphMap contDiff_id (D.contDiff_physicalHeight.comp (planarRotation t).contDiff)
  have heq : D.rotationFamily t =
      (graphMap id (fun y => D.physicalHeight (planarRotation t y))) ∘ φ :=
    funext (D.rotationFamily_eq_physical_graph t)
  have hn := D.rotationNormal_isUnitSurfaceNormal t x
  rw [heq] at hn
  exact hn.of_comp (hg.differentiable (by simp) (φ x))
    (hs.differentiable (by simp) x)
    (fderiv_bijective_of_homeomorph_smooth_inverse φ (hs.differentiable (by simp) x)
      (hi.differentiable (by simp) (φ x))).surjective

/-- Actual outward rays at a developed graph point of the explicit cylinder body. -/
theorem IsometricGraphDevelopment.rotationNormal_pointsOutwardFrom
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) (t : ℝ) (x : PolarPoint)
    {R bottom : ℝ} (hr : cartesianRadius (graphBaseProjection (D.rotationFamily t x)) < R)
    (hb : bottom < D.rotationFamily t x 2) :
    PointsOutwardFrom (D.graphCylinderInterior t R bottom)
      (D.rotationFamily t x) (D.rotationNormal t x) := by
  have hr' : cartesianRadius (rotationConjugate t D.planar x) < R := by
    simpa only [IsometricGraphDevelopment.rotationFamily, graphBaseProjection_graphMap] using hr
  have hb' : bottom < D.physicalHeight (planarRotation t (rotationConjugate t D.planar x)) := by
    simpa only [D.rotationFamily_eq_physical_graph, graphMap_two] using hb
  have h := graph_normal_pointsOutwardFrom
    (D.contDiff_physicalHeight.comp (planarRotation t).contDiff)
    (D.rotationNormal_physical_graph t x) (D.rotationNormal_height_pos t x) hr' hb'
  simpa only [IsometricGraphDevelopment.graphCylinderInterior, graphCylinderRegion,
    D.rotationFamily_eq_physical_graph, Function.comp_def] using h

theorem IsometricGraphDevelopment.rotationFamily_base_radius_lt
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) (t : ℝ) {R : ℝ}
    (hR : A.b < R) {x : PolarPoint} (hx : cartesianRadius x < R) :
    cartesianRadius (graphBaseProjection (D.rotationFamily t x)) < R := by
  by_cases hb : cartesianRadius x ≤ A.b
  · have hm : graphBaseProjection (D.rotationFamily t x) ∈
        graphBaseProjection '' (D.rotationFamily t '' {y : PolarPoint | cartesianRadius y ≤ A.b}) :=
      ⟨D.rotationFamily t x, ⟨x, hb, rfl⟩, rfl⟩
    rw [D.rotationFamily_projects_onto_disk t le_rfl] at hm
    exact hm.trans_lt hR
  · have hb' := lt_of_not_ge hb
    rw [D.rotationFamily_fixed_outside t hb']
    simpa only [IsometricGraphDevelopment.map, graphBaseProjection_graphMap,
      D.normalized_outside x hb'] using hx

/-- One actual bottom plane works for every phase and every open graph-disk point. -/
theorem IsometricGraphDevelopment.exists_bottom_outward_graphDisk
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) {R : ℝ} (hR : A.b < R) :
    ∃ bottom : ℝ, ∀ t : ℝ, ∀ x : PolarPoint, cartesianRadius x < R →
      PointsOutwardFrom (D.graphCylinderInterior t R bottom)
        (D.rotationFamily t x) (D.rotationNormal t x) ∧
      D.rotationFamily t x ∈ frontier (D.graphCylinderInterior t R bottom) := by
  obtain ⟨lo, hi, hbound⟩ := D.exists_rotationFamily_height_bounds R
  refine ⟨lo - 1, fun t x hx => ?_⟩
  have hn := D.rotationNormal_pointsOutwardFrom t x
    (D.rotationFamily_base_radius_lt t hR hx)
    (show lo - 1 < D.rotationFamily t x 2 by
      have h := (hbound t x hx.le).1
      linarith)
  exact ⟨hn, hn.mem_frontier⟩

end ContinuousFlexibility
