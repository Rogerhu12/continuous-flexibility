import ContinuousFlexibility.Contracts.GraphFamilyImage
import ContinuousFlexibility.Geometry.GraphSurfaceGeometry
import ContinuousFlexibility.Geometry.SurfaceReparametrization

/-!
# Actual normals of the developed graph and its rotation family

The height is expressed in the physical planar coordinates of the constructed
development. Its genuine upward graph normal is pulled back and then transported
by the actual ambient Euclidean rotation. This is not yet an identification with
the outward normal of a closed surface; the separated cap and inside region are
still separate construction obligations.
-/

noncomputable section

namespace ContinuousFlexibility

open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

def IsometricGraphDevelopment.physicalHeight
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) : PolarPoint → ℝ :=
  fun y => A.cartesianHeight (D.planar.symm y)

theorem IsometricGraphDevelopment.contDiff_physicalHeight
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) :
    ContDiff ℝ ∞ D.physicalHeight := A.contDiff_cartesianHeight.comp D.smooth_inverse

theorem IsometricGraphDevelopment.map_eq_physical_graph
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) (x : PolarPoint) :
    D.map x = graphMap id D.physicalHeight (D.planar x) := by
  apply e3_eq_of_base_height
  · simp only [IsometricGraphDevelopment.map, graphBaseProjection_graphMap, id_eq]
  · simp only [IsometricGraphDevelopment.map, graphMap_two,
      IsometricGraphDevelopment.physicalHeight, D.planar.symm_apply_apply]

theorem IsometricGraphDevelopment.fderiv_map_physical_graph
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) (x : PolarPoint) :
    fderiv ℝ D.map x =
      (fderiv ℝ (graphMap id D.physicalHeight) (D.planar x)).comp
        (fderiv ℝ (D.planar : PolarPoint → PolarPoint) x) := by
  have heq : D.map = (graphMap id D.physicalHeight) ∘ D.planar :=
    funext D.map_eq_physical_graph
  rw [heq]
  exact (((contDiff_graphMap contDiff_id D.contDiff_physicalHeight).differentiable
    (by simp) (D.planar x)).hasFDerivAt.comp x
      (D.smooth_planar.differentiable (by simp) x).hasFDerivAt).fderiv

def IsometricGraphDevelopment.upwardGraphNormal
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) (x : PolarPoint) : E3 :=
  graphUpwardNormal D.physicalHeight (D.planar x)

theorem IsometricGraphDevelopment.contDiff_upwardGraphNormal
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) :
    ContDiff ℝ ∞ D.upwardGraphNormal :=
  (contDiff_graphUpwardNormal D.contDiff_physicalHeight).comp D.smooth_planar

theorem IsometricGraphDevelopment.upwardGraphNormal_isUnitSurfaceNormal
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) (x : PolarPoint) :
    IsUnitSurfaceNormal D.map x (D.upwardGraphNormal x) := by
  refine ⟨graphUpwardNormal_norm _ _, fun v => ?_⟩
  rw [D.fderiv_map_physical_graph]
  simp only [ContinuousLinearMap.comp_apply]
  exact graphUpwardNormal_orthogonal
    (D.contDiff_physicalHeight.differentiable (by simp) (D.planar x))
    (fderiv ℝ (D.planar : PolarPoint → PolarPoint) x v)

theorem IsometricGraphDevelopment.upwardGraphNormal_height_pos
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) (x : PolarPoint) :
    0 < D.upwardGraphNormal x 2 := by
  change 0 < graphUpwardNormal D.physicalHeight (D.planar x) 2
  rw [graphUpwardNormal_two]
  exact div_pos zero_lt_one (graphAreaDensity_pos _ _)

def IsometricGraphDevelopment.rotationNormal
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) (t : ℝ) (x : PolarPoint) : E3 :=
  axialRotation (-t) (D.upwardGraphNormal (planarRotation t x))

theorem IsometricGraphDevelopment.rotationNormal_joint_smooth
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) :
    ContDiff ℝ ∞ (fun q : ℝ × PolarPoint => D.rotationNormal q.1 q.2) := by
  have hn : ContDiff ℝ ∞ (fun q : ℝ × PolarPoint =>
      D.upwardGraphNormal (planarRotation q.1 q.2)) :=
    D.contDiff_upwardGraphNormal.comp contDiff_planarRotation_joint
  have ha : ContDiff ℝ ∞ (fun q : ℝ × PolarPoint => 2 * Real.pi * (-q.1)) :=
    contDiff_const.mul contDiff_fst.neg
  have h0 : ContDiff ℝ ∞ (fun q : ℝ × PolarPoint =>
      D.upwardGraphNormal (planarRotation q.1 q.2) 0) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3)).contDiff.comp hn
  have h1 : ContDiff ℝ ∞ (fun q : ℝ × PolarPoint =>
      D.upwardGraphNormal (planarRotation q.1 q.2) 1) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 3)).contDiff.comp hn
  have h2 : ContDiff ℝ ∞ (fun q : ℝ × PolarPoint =>
      D.upwardGraphNormal (planarRotation q.1 q.2) 2) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).contDiff.comp hn
  have h := ((((ha.cos.mul h0).sub (ha.sin.mul h1)).smul_const (e3Basis 0)).add
    (((ha.sin.mul h0).add (ha.cos.mul h1)).smul_const (e3Basis 1))).add
      (h2.smul_const (e3Basis 2))
  simpa only [IsometricGraphDevelopment.rotationNormal, axialRotation_apply,
    axialRotationMap, planarRotation, planeRotationLinearMap_apply, graphBaseProjection] using h

theorem IsometricGraphDevelopment.fderiv_rotationFamily
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) (t : ℝ) (x : PolarPoint) :
    fderiv ℝ (D.rotationFamily t) x =
      (axialRotation (-t) : E3 →L[ℝ] E3).comp
        ((fderiv ℝ D.map (planarRotation t x)).comp (planarRotation t)) := by
  have heq : D.rotationFamily t =
      fun y => axialRotation (-t) (D.map (planarRotation t y)) :=
    funext (D.rotationFamily_eq_axialRotation t)
  rw [heq]
  exact ((axialRotation (-t)).hasFDerivAt.comp x
    ((D.smooth_graph.differentiable (by simp) (planarRotation t x)).hasFDerivAt.comp x
      (planarRotation t).hasFDerivAt)).fderiv

theorem IsometricGraphDevelopment.rotationNormal_isUnitSurfaceNormal
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) (t : ℝ) (x : PolarPoint) :
    IsUnitSurfaceNormal (D.rotationFamily t) x (D.rotationNormal t x) := by
  refine ⟨?_, fun v => ?_⟩
  · simpa only [IsometricGraphDevelopment.rotationNormal, LinearIsometryEquiv.norm_map] using
      (D.upwardGraphNormal_isUnitSurfaceNormal (planarRotation t x)).1
  · rw [D.fderiv_rotationFamily]
    simp only [ContinuousLinearMap.comp_apply]
    change inner ℝ (axialRotation (-t) (fderiv ℝ D.map (planarRotation t x) (planarRotation t v)))
      (axialRotation (-t) (D.upwardGraphNormal (planarRotation t x))) = 0
    rw [(axialRotation (-t)).inner_map_map]
    exact (D.upwardGraphNormal_isUnitSurfaceNormal (planarRotation t x)).2 (planarRotation t v)

theorem IsometricGraphDevelopment.rotationNormal_height_pos
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) (t : ℝ) (x : PolarPoint) :
    0 < D.rotationNormal t x 2 := by
  change 0 < axialRotationMap (-t) (D.upwardGraphNormal (planarRotation t x)) 2
  rw [axialRotationMap_height]
  exact D.upwardGraphNormal_height_pos _

theorem axialRotation_neg_add_one (t : ℝ) : axialRotation (-(t + 1)) = axialRotation (-t) := by
  apply LinearIsometryEquiv.ext
  intro v
  apply e3_eq_of_base_height
  · simp only [axialRotation_apply, axialRotationMap_base, planarRotation_neg_add_one]
  · simp

theorem IsometricGraphDevelopment.rotationNormal_periodic
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) :
    Function.Periodic D.rotationNormal 1 := by
  intro t
  funext x
  simp only [IsometricGraphDevelopment.rotationNormal, axialRotation_neg_add_one,
    planarRotation_add_one]

@[simp] theorem IsometricGraphDevelopment.rotationNormal_zero
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) (x : PolarPoint) :
    D.rotationNormal 0 x = D.upwardGraphNormal x := by
  simp [IsometricGraphDevelopment.rotationNormal]

theorem IsometricGraphDevelopment.rotationFamily_eq_rigid_comp
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) (t : ℝ) :
    D.rotationFamily t = rigidSurfaceMap (axialRotation (-t)) 0 (D.map ∘ planarRotation t) := by
  funext x
  simp only [rigidSurfaceMap, Function.comp_apply, add_zero]
  exact D.rotationFamily_eq_axialRotation t x

/-- Gaussian curvature is transported along the actual intrinsic rotation.
No equality of curvatures is an input to this theorem. -/
theorem IsometricGraphDevelopment.rotationFamily_gaussianCurvature
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) (t : ℝ) (x : PolarPoint) :
    surfaceGaussianCurvature (D.rotationFamily t) (D.rotationNormal t x) x =
      surfaceGaussianCurvature D.map (D.upwardGraphNormal (planarRotation t x))
        (planarRotation t x) := by
  have hDs : ContDiff ℝ ∞ D.map := D.smooth_graph
  have hRs : ContDiff ℝ ∞ (planarRotation t : PolarPoint → PolarPoint) :=
    (planarRotation t).contDiff
  change surfaceGaussianCurvature (D.rotationFamily t)
    (axialRotation (-t) (D.upwardGraphNormal (planarRotation t x))) x = _
  rw [D.rotationFamily_eq_rigid_comp,
    surfaceGaussianCurvature_rigidSurfaceMap (axialRotation (-t)) 0 (hDs.comp hRs)]
  apply surfaceGaussianCurvature_comp
    (hDs.of_le (by simp : (2 : ℕ∞ω) ≤ ∞)).contDiffAt
    (hRs.of_le (by simp : (2 : ℕ∞ω) ≤ ∞)).contDiffAt
    (D.upwardGraphNormal_isUnitSurfaceNormal (planarRotation t x))
    (D.immersion_graph (planarRotation t x))
  rw [(planarRotation t).hasFDerivAt.fderiv]
  exact (planarRotationHomeomorph t).injective

/-- The signed mean curvature uses the transported upward normal. Identifying
it as the outward normal of the eventual closed sphere is a later obligation. -/
theorem IsometricGraphDevelopment.rotationFamily_meanCurvature
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) (t : ℝ) (x : PolarPoint) :
    surfaceMeanCurvature (D.rotationFamily t) (D.rotationNormal t x) x =
      surfaceMeanCurvature D.map (D.upwardGraphNormal (planarRotation t x))
        (planarRotation t x) := by
  have hDs : ContDiff ℝ ∞ D.map := D.smooth_graph
  have hRs : ContDiff ℝ ∞ (planarRotation t : PolarPoint → PolarPoint) :=
    (planarRotation t).contDiff
  change surfaceMeanCurvature (D.rotationFamily t)
    (axialRotation (-t) (D.upwardGraphNormal (planarRotation t x))) x = _
  rw [D.rotationFamily_eq_rigid_comp,
    surfaceMeanCurvature_rigidSurfaceMap (axialRotation (-t)) 0 (hDs.comp hRs)]
  apply surfaceMeanCurvature_comp
    (hDs.of_le (by simp : (2 : ℕ∞ω) ≤ ∞)).contDiffAt
    (hRs.of_le (by simp : (2 : ℕ∞ω) ≤ ∞)).contDiffAt
    (D.upwardGraphNormal_isUnitSurfaceNormal (planarRotation t x))
    (D.immersion_graph (planarRotation t x))
  rw [(planarRotation t).hasFDerivAt.fderiv]
  exact (planarRotationHomeomorph t).injective

theorem IsometricGraphDevelopment.gaussianCurvature_physical_graph
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) (x : PolarPoint) :
    surfaceGaussianCurvature D.map (D.upwardGraphNormal x) x =
      surfaceGaussianCurvature (graphMap id D.physicalHeight)
        (graphUpwardNormal D.physicalHeight (D.planar x)) (D.planar x) := by
  have hFs : ContDiff ℝ ∞ (graphMap id D.physicalHeight) :=
    contDiff_graphMap contDiff_id D.contDiff_physicalHeight
  have heq : D.map = (graphMap id D.physicalHeight) ∘ D.planar :=
    funext D.map_eq_physical_graph
  rw [heq]
  exact surfaceGaussianCurvature_comp
    (hFs.of_le (by simp : (2 : ℕ∞ω) ≤ ∞)).contDiffAt
    (D.smooth_planar.of_le (by simp : (2 : ℕ∞ω) ≤ ∞)).contDiffAt
    (graphUpwardNormal_isUnitSurfaceNormal
      (D.contDiff_physicalHeight.differentiable (by simp) (D.planar x)))
    (heightGraph_fderiv_injective
      (D.contDiff_physicalHeight.differentiable (by simp) (D.planar x)))
    (fderiv_bijective_of_homeomorph_smooth_inverse D.planar
      (D.smooth_planar.differentiable (by simp) x)
      (D.smooth_inverse.differentiable (by simp) (D.planar x))).injective

theorem IsometricGraphDevelopment.meanCurvature_physical_graph
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) (x : PolarPoint) :
    surfaceMeanCurvature D.map (D.upwardGraphNormal x) x =
      surfaceMeanCurvature (graphMap id D.physicalHeight)
        (graphUpwardNormal D.physicalHeight (D.planar x)) (D.planar x) := by
  have hFs : ContDiff ℝ ∞ (graphMap id D.physicalHeight) :=
    contDiff_graphMap contDiff_id D.contDiff_physicalHeight
  have heq : D.map = (graphMap id D.physicalHeight) ∘ D.planar :=
    funext D.map_eq_physical_graph
  rw [heq]
  exact surfaceMeanCurvature_comp
    (hFs.of_le (by simp : (2 : ℕ∞ω) ≤ ∞)).contDiffAt
    (D.smooth_planar.of_le (by simp : (2 : ℕ∞ω) ≤ ∞)).contDiffAt
    (graphUpwardNormal_isUnitSurfaceNormal
      (D.contDiff_physicalHeight.differentiable (by simp) (D.planar x)))
    (heightGraph_fderiv_injective
      (D.contDiff_physicalHeight.differentiable (by simp) (D.planar x)))
    (fderiv_bijective_of_homeomorph_smooth_inverse D.planar
      (D.smooth_planar.differentiable (by simp) x)
      (D.smooth_inverse.differentiable (by simp) (D.planar x))).injective

end ContinuousFlexibility
