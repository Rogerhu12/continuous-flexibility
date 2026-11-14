module

public import ContinuousFlexibility.Geometry.MarkedCapDisk
public import ContinuousFlexibility.Geometry.CapDiskNormal
public import ContinuousFlexibility.Geometry.MarkedCap
public import ContinuousFlexibility.Geometry.SurfaceReparametrization

/-!
# The actual normal and curvature peak of the marked cap

The normal below is a single globally smooth formula. On the top branch it
is the upward normal of the translated marker graph; off that branch it is
the actual meridian normal. Actual second derivatives, coordinate changes,
and the compact curvature bound of the unmarked cap identify its curvature.
The choice of marker strength precedes the choice of its support radius.
Identification as the outward normal of the completed sphere is separate.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility

open Set Filter
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

def markedCapCoordinates (R L : ℝ) (y : PolarPoint) : PolarPoint :=
  capDiskBase R L y - markedCapCenter R L

def markedCapNormal (R L k ρ : ℝ) (y : PolarPoint) : E3 :=
  capDiskNormal R L y + markedCapCutoff R L y •
    (graphUpwardNormal (markerBump 1 2 k ρ) (markedCapCoordinates R L y) - e3Basis 2)

private def markedCapLocalGraph (R h L k ρ : ℝ) : PolarPoint → E3 :=
  rigidSurfaceMap (LinearIsometryEquiv.refl ℝ E3)
    ((markedCapCenter R L).1 • e3Basis 0 + (markedCapCenter R L).2 • e3Basis 1 + h • e3Basis 2)
    (graphMap id (markerBump 1 2 k ρ))

theorem contDiff_markedCapCoordinates {R L : ℝ} (hR : 0 < R) (hL : 0 < L) :
    ContDiff ℝ ∞ (markedCapCoordinates R L) :=
  (markedCap_contDiff_base hR hL).sub contDiff_const

theorem contDiff_markedCapNormal {R L : ℝ} (hR : 0 < R) (hL : 0 < L) (k ρ : ℝ) :
    ContDiff ℝ ∞ (markedCapNormal R L k ρ) :=
  (contDiff_capDiskNormal hR hL).add ((contDiff_markedCapCutoff hR hL).smul
    (((contDiff_graphUpwardNormal (contDiff_markerBump 1 2 k ρ)).comp
      (contDiff_markedCapCoordinates hR hL)).sub contDiff_const))

theorem markedCapNormal_eq_top {R L : ℝ} (hL : 0 < L) (k ρ : ℝ)
    {y : PolarPoint} (hy : capDiskParameter R L y ≤ L / 4) :
    markedCapNormal R L k ρ y =
      graphUpwardNormal (markerBump 1 2 k ρ) (markedCapCoordinates R L y) := by
  unfold markedCapNormal
  rw [capDiskNormal_top_collar R hL hy, markedCapCutoff_eq_one hL hy, one_smul]
  abel

private theorem not_top_mem_disk {R L : ℝ} (hR : 0 < R) (hL : 0 < L)
    {y : PolarPoint} (hy : L / 4 ≤ capDiskParameter R L y) :
    cartesianRadius y ≤ 1 := by
  have hS := add_pos hL hR
  unfold capDiskParameter at hy
  nlinarith

private theorem middle_marker_quadratic_gt {R L ρ : ℝ}
    (hR : 0 < R) (hL : 0 < L) (hρ : 0 < ρ) (hsmall : ρ < L / 64)
    {y : PolarPoint} (hy : capDiskParameter R L y ∈ Icc (L / 4) (3 * L / 4)) :
    ρ ^ 2 < markerQuadratic 1 2 (markedCapCoordinates R L y) := by
  have hr := markedCap_meridian_middle_lower R hL hy
  rw [← capDiskBase_radius hR hL (not_top_mem_disk hR hL hy.1)] at hr
  have htri : cartesianRadius (capDiskBase R L y) ≤
      cartesianRadius (markedCapCoordinates R L y) + cartesianRadius (markedCapCenter R L) := by
    simpa only [cartesianRadius, markedCapCoordinates, map_sub, sub_add_cancel] using
      norm_add_le (Complex.equivRealProdCLM.symm (capDiskBase R L y) -
        Complex.equivRealProdCLM.symm (markedCapCenter R L))
        (Complex.equivRealProdCLM.symm (markedCapCenter R L))
  rw [markedCapCenter_radius hR hL] at htri
  have hd : L / 8 ≤ cartesianRadius (markedCapCoordinates R L y) := by linarith
  have hsq := cartesianRadius_sq_coordinates (markedCapCoordinates R L y)
  dsimp [markerQuadratic, coordinateEuclideanPair] at hsq ⊢
  nlinarith [sq_nonneg (markedCapCoordinates R L y).2]

private theorem marker_normal_eq_vertical {k ρ : ℝ} (hρ : ρ ≠ 0)
    {x : PolarPoint} (hx : ρ ^ 2 ≤ markerQuadratic 1 2 x) :
    graphUpwardNormal (markerBump 1 2 k ρ) x = e3Basis 2 := by
  have hd : fderiv ℝ (markerBump 1 2 k ρ) x = 0 := by
    apply ContinuousLinearMap.ext
    intro v
    simp [fderiv_markerBump_apply, markerKernel_eq_zero hρ hx]
  simp [graphUpwardNormal, graphAreaDensity, graphAreaSq, radialPartial,
    angularPartial, hd, graphMap]

theorem markedCapNormal_eq_capDiskNormal {R L k ρ : ℝ}
    (hR : 0 < R) (hL : 0 < L) (hρ : 0 < ρ) (hsmall : ρ < L / 64)
    {y : PolarPoint} (hy : L / 4 ≤ capDiskParameter R L y) :
    markedCapNormal R L k ρ y = capDiskNormal R L y := by
  by_cases hb : 3 * L / 4 ≤ capDiskParameter R L y
  · simp [markedCapNormal, markedCapCutoff_eq_zero hL hb]
  · have hq := middle_marker_quadratic_gt hR hL hρ hsmall ⟨hy, (lt_of_not_ge hb).le⟩
    simp [markedCapNormal, marker_normal_eq_vertical hρ.ne' hq.le]

private theorem contDiff_markedCapLocalGraph (R h L k ρ : ℝ) :
    ContDiff ℝ ∞ (markedCapLocalGraph R h L k ρ) :=
  (contDiff_graphMap contDiff_id (contDiff_markerBump 1 2 k ρ)).add contDiff_const

private theorem markedCapLocalGraph_normal (R h L k ρ : ℝ) (x : PolarPoint) :
    IsUnitSurfaceNormal (markedCapLocalGraph R h L k ρ) x
      (graphUpwardNormal (markerBump 1 2 k ρ) x) := by
  have hz := (contDiff_markerBump 1 2 k ρ).differentiable (by simp) x
  exact (graphUpwardNormal_isUnitSurfaceNormal hz).rigidSurfaceMap
    ((contDiff_graphMap contDiff_id (contDiff_markerBump 1 2 k ρ)).differentiable (by simp) x)
    (LinearIsometryEquiv.refl ℝ E3) _

private theorem markedCapLocalGraph_immersion (R h L k ρ : ℝ) (x : PolarPoint) :
    Function.Injective (fderiv ℝ (markedCapLocalGraph R h L k ρ) x) := by
  have hz := (contDiff_markerBump 1 2 k ρ).differentiable (by simp) x
  unfold markedCapLocalGraph
  rw [fderiv_rigidSurfaceMap _ _
    ((contDiff_graphMap contDiff_id (contDiff_markerBump 1 2 k ρ)).differentiable (by simp) x)]
  simpa using heightGraph_fderiv_injective hz

private theorem markedCapMap_top_germ {R L : ℝ} (hL : 0 < L) (h k ρ : ℝ)
    {y : PolarPoint} (hy : capDiskParameter R L y < L / 4) :
    markedCapMap R h L k ρ =ᶠ[𝓝 y]
      markedCapLocalGraph R h L k ρ ∘ markedCapCoordinates R L := by
  have hc : Continuous (capDiskParameter R L) :=
    continuous_const.mul (continuous_const.sub continuous_cartesianRadius)
  have hn : {z : PolarPoint | capDiskParameter R L z < L / 4} ∈ 𝓝 y :=
    (isOpen_lt hc continuous_const).mem_nhds hy
  filter_upwards [hn] with z hz
  have hheight : capDiskHeight R h L z = h := capMeridianHeight_eq_left h hL hz.le
  ext i
  fin_cases i <;>
    simp [markedCapMap, markedCapHeight, markedCapBump, markedCapCutoff_eq_one hL hz.le,
      markedCapLocalGraph, rigidSurfaceMap, markedCapCoordinates, graphMap, e3Basis, hheight, add_comm]

theorem isUnitSurfaceNormal_markedCap {R L k ρ : ℝ}
    (hR : 0 < R) (hL : 0 < L) (hρ : 0 < ρ) (hsmall : ρ < L / 64)
    (h : ℝ) (y : PolarPoint) :
    IsUnitSurfaceNormal (markedCapMap R h L k ρ) y (markedCapNormal R L k ρ y) := by
  by_cases ht : capDiskParameter R L y < L / 4
  · rw [markedCapNormal_eq_top hL k ρ ht.le]
    have hn := (markedCapLocalGraph_normal R h L k ρ (markedCapCoordinates R L y)).comp
      ((contDiff_markedCapLocalGraph R h L k ρ).differentiable (by simp) _)
      ((contDiff_markedCapCoordinates hR hL).differentiable (by simp) y)
    refine ⟨hn.1, fun v => ?_⟩
    rw [(markedCapMap_top_germ hL h k ρ ht).fderiv_eq (𝕜 := ℝ)]
    exact hn.2 v
  · have hs := le_of_not_gt ht
    rw [markedCapNormal_eq_capDiskNormal hR hL hρ hsmall hs]
    have hn := isUnitSurfaceNormal_capDisk hR hL h y
    refine ⟨hn.1, fun v => ?_⟩
    rw [(markedCapMap_germ_of_not_top hR hL hρ hsmall h
      (not_top_mem_disk hR hL hs) hs).fderiv_eq (𝕜 := ℝ)]
    exact hn.2 v

theorem markedCapNormal_norm {R L k ρ : ℝ}
    (hR : 0 < R) (hL : 0 < L) (hρ : 0 < ρ) (hsmall : ρ < L / 64)
    (y : PolarPoint) : ‖markedCapNormal R L k ρ y‖ = 1 :=
  (isUnitSurfaceNormal_markedCap hR hL hρ hsmall 0 y).1

theorem markedCapNormal_orthogonal {R L k ρ : ℝ}
    (hR : 0 < R) (hL : 0 < L) (hρ : 0 < ρ) (hsmall : ρ < L / 64)
    (h : ℝ) (y v : PolarPoint) :
    inner ℝ (fderiv ℝ (markedCapMap R h L k ρ) y v) (markedCapNormal R L k ρ y) = 0 :=
  (isUnitSurfaceNormal_markedCap hR hL hρ hsmall h y).2 v

private theorem markedCap_shape_congr_germ {F G : PolarPoint → E3} {x : PolarPoint}
    (hg : F =ᶠ[𝓝 x] G) (N : E3) : surfaceShapeMatrix F N x = surfaceShapeMatrix G N x := by
  have h1 := hg.fderiv_eq (𝕜 := ℝ)
  have h2 := (hg.fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)
  have hG : surfaceGram F x = surfaceGram G x := by
    ext i j
    simp only [surfaceGram, surfaceFirstForm, h1]
  have hB : surfaceSecondMatrix F N x = surfaceSecondMatrix G N x := by
    ext i j
    simp only [surfaceSecondMatrix, surfaceSecondForm, h2]
  simp only [surfaceShapeMatrix, hG, hB]

theorem markedCapCoordinates_fderiv_injective_top {R L : ℝ}
    (hR : 0 < R) (hL : 0 < L) {y : PolarPoint} (hy : cartesianRadius y ≤ 1)
    (htop : capDiskParameter R L y < L / 4) :
    Function.Injective (fderiv ℝ (markedCapCoordinates R L) y) := by
  have hd : fderiv ℝ (markedCapCoordinates R L) y = fderiv ℝ (capDiskBase R L) y :=
    (((markedCap_contDiff_base hR hL).differentiable (by simp) y).hasFDerivAt.sub_const _).fderiv
  rw [hd]
  exact markedCap_base_fderiv_injective_top hR hL 0 hy htop

theorem surfaceShapeMatrix_markedCap_top {R L : ℝ}
    (hR : 0 < R) (hL : 0 < L) (h k ρ : ℝ) {y : PolarPoint}
    (hy : cartesianRadius y ≤ 1) (htop : capDiskParameter R L y < L / 4) :
    surfaceShapeMatrix (markedCapMap R h L k ρ) (markedCapNormal R L k ρ y) y =
      (surfaceJacobian (markedCapCoordinates R L) y)⁻¹ *
        surfaceShapeMatrix (graphMap id (markerBump 1 2 k ρ))
          (graphUpwardNormal (markerBump 1 2 k ρ) (markedCapCoordinates R L y))
          (markedCapCoordinates R L y) * surfaceJacobian (markedCapCoordinates R L) y := by
  rw [markedCapNormal_eq_top hL k ρ htop.le,
    markedCap_shape_congr_germ (markedCapMap_top_germ hL h k ρ htop)]
  rw [surfaceShapeMatrix_comp
    ((contDiff_markedCapLocalGraph R h L k ρ).of_le (by simp : (2 : ℕ∞ω) ≤ ∞)).contDiffAt
    ((contDiff_markedCapCoordinates hR hL).of_le (by simp : (2 : ℕ∞ω) ≤ ∞)).contDiffAt
    (markedCapLocalGraph_normal R h L k ρ _)
    (markedCapLocalGraph_immersion R h L k ρ _)
    (markedCapCoordinates_fderiv_injective_top hR hL hy htop)]
  congr 2
  exact surfaceShapeMatrix_rigidSurfaceMap (LinearIsometryEquiv.refl ℝ E3) _
    (contDiff_graphMap contDiff_id (contDiff_markerBump 1 2 k ρ)) _ _

theorem surfaceGaussianCurvature_markedCap_top {R L ρ : ℝ}
    (hR : 0 < R) (hL : 0 < L) (hρ : ρ ≠ 0) (h k : ℝ) {y : PolarPoint}
    (hy : cartesianRadius y ≤ 1) (htop : capDiskParameter R L y < L / 4) :
    surfaceGaussianCurvature (markedCapMap R h L k ρ) (markedCapNormal R L k ρ y) y =
      markerCurvatureExpression 1 2 k ρ (markedCapCoordinates R L y) := by
  unfold surfaceGaussianCurvature
  rw [surfaceShapeMatrix_markedCap_top hR hL h k ρ hy htop,
    Matrix.det_conj' (surfaceJacobian_isUnit
      (markedCapCoordinates_fderiv_injective_top hR hL hy htop))]
  exact surfaceGaussianCurvature_markerBump 1 2 k hρ _

theorem surfaceShapeMatrix_markedCap_of_not_top {R L k ρ : ℝ}
    (hR : 0 < R) (hL : 0 < L) (hρ : 0 < ρ) (hsmall : ρ < L / 64) (h : ℝ)
    {y : PolarPoint} (hy : L / 4 ≤ capDiskParameter R L y) :
    surfaceShapeMatrix (markedCapMap R h L k ρ) (markedCapNormal R L k ρ y) y =
      surfaceShapeMatrix (capDiskMap R h L) (capDiskNormal R L y) y := by
  rw [markedCapNormal_eq_capDiskNormal hR hL hρ hsmall hy]
  exact markedCap_shape_congr_germ (markedCapMap_germ_of_not_top hR hL hρ hsmall h
    (not_top_mem_disk hR hL hy) hy) _

theorem surfaceGaussianCurvature_markedCap_of_not_top {R L k ρ : ℝ}
    (hR : 0 < R) (hL : 0 < L) (hρ : 0 < ρ) (hsmall : ρ < L / 64) (h : ℝ)
    {y : PolarPoint} (hy : L / 4 ≤ capDiskParameter R L y) :
    surfaceGaussianCurvature (markedCapMap R h L k ρ) (markedCapNormal R L k ρ y) y =
      surfaceGaussianCurvature (capDiskMap R h L) (capDiskNormal R L y) y := by
  simp only [surfaceGaussianCurvature, surfaceShapeMatrix_markedCap_of_not_top hR hL hρ hsmall h hy]

theorem surfaceMeanCurvature_markedCap_of_not_top {R L k ρ : ℝ}
    (hR : 0 < R) (hL : 0 < L) (hρ : 0 < ρ) (hsmall : ρ < L / 64) (h : ℝ)
    {y : PolarPoint} (hy : L / 4 ≤ capDiskParameter R L y) :
    surfaceMeanCurvature (markedCapMap R h L k ρ) (markedCapNormal R L k ρ y) y =
      surfaceMeanCurvature (capDiskMap R h L) (capDiskNormal R L y) y := by
  simp only [surfaceMeanCurvature, surfaceShapeMatrix_markedCap_of_not_top hR hL hρ hsmall h hy]

theorem markedCapCenterParameter_parameter {R L : ℝ} (hR : 0 < R) (hL : 0 < L) :
    capDiskParameter R L (markedCapCenterParameter R L) = L / 8 := by
  have hc0 : 0 < cartesianRadius (markedCapCenter R L) := by
    rw [markedCapCenter_radius hR hL]; linarith
  have hc4 : cartesianRadius (markedCapCenter R L) < R + L / 4 := by
    rw [markedCapCenter_radius hR hL]; linarith
  rw [markedCapCenterParameter, capDiskRimChart_parameter hR hL hc0 hc4,
    markedCapCenter_radius hR hL]
  ring

theorem markedCapCoordinates_center {R L : ℝ} (hR : 0 < R) (hL : 0 < L) :
    markedCapCoordinates R L (markedCapCenterParameter R L) = 0 := by
  have hc0 : 0 < cartesianRadius (markedCapCenter R L) := by
    rw [markedCapCenter_radius hR hL]; linarith
  have hc4 : cartesianRadius (markedCapCenter R L) < R + L / 4 := by
    rw [markedCapCenter_radius hR hL]; linarith
  simp [markedCapCoordinates, markedCapCenterParameter, capDiskBase_rimChart hR hL hc0 hc4]

theorem markedCapCoordinates_eq_zero_iff {R L : ℝ} (hR : 0 < R) (hL : 0 < L)
    {y : PolarPoint} (hy : cartesianRadius y ≤ 1)
    (htop : capDiskParameter R L y < L / 4) :
    markedCapCoordinates R L y = 0 ↔ y = markedCapCenterParameter R L := by
  constructor
  · intro hz
    have hb : capDiskBase R L y = markedCapCenter R L := sub_eq_zero.mp hz
    have hb0 : capDiskBase R L (markedCapCenterParameter R L) = markedCapCenter R L :=
      sub_eq_zero.mp (markedCapCoordinates_center hR hL)
    have hzy : capDiskHeight R 0 L y = 0 := capMeridianHeight_eq_left 0 hL htop.le
    have hzc : capDiskHeight R 0 L (markedCapCenterParameter R L) = 0 :=
      capMeridianHeight_eq_left 0 hL (by rw [markedCapCenterParameter_parameter hR hL]; linarith)
    apply capDiskMap_injOn hR hL 0 hy (markedCapCenterParameter_mem hR hL).le
    ext i
    fin_cases i <;> simp [capDiskMap, hb, hb0, hzy, hzc]
  · rintro rfl
    exact markedCapCoordinates_center hR hL

theorem markedCapNormal_center {R L : ℝ} (hR : 0 < R) (hL : 0 < L) (k ρ : ℝ) :
    markedCapNormal R L k ρ (markedCapCenterParameter R L) = e3Basis 2 := by
  rw [markedCapNormal_eq_top hL k ρ
    (by rw [markedCapCenterParameter_parameter hR hL]; linarith), markedCapCoordinates_center hR hL]
  simp [graphUpwardNormal, graphAreaDensity, graphAreaSq, radialPartial, angularPartial, graphMap]

/-- The original cap coordinates conjugate the two distinct physical marker
directions. The normal is upward here, independently of the coordinate orientation. -/
theorem surfaceShapeMatrix_markedCap_center {R L : ℝ}
    (hR : 0 < R) (hL : 0 < L) (h k ρ : ℝ) :
    surfaceShapeMatrix (markedCapMap R h L k ρ)
      (markedCapNormal R L k ρ (markedCapCenterParameter R L)) (markedCapCenterParameter R L) =
      (surfaceJacobian (markedCapCoordinates R L) (markedCapCenterParameter R L))⁻¹ *
        !![-k, 0; 0, -2 * k] *
        surfaceJacobian (markedCapCoordinates R L) (markedCapCenterParameter R L) := by
  rw [surfaceShapeMatrix_markedCap_top hR hL h k ρ (markedCapCenterParameter_mem hR hL).le
    (by rw [markedCapCenterParameter_parameter hR hL]; linarith),
    markedCapCoordinates_center hR hL, surfaceShapeMatrix_markerBump_zero]
  simp [mul_comm]

private theorem markedCap_conjugate_eigenvector
    (J D : Matrix (Fin 2) (Fin 2) ℝ) (hJ : IsUnit J.det)
    (a : ℝ) (v : Fin 2 → ℝ) (hv : v ≠ 0) (hDv : D.mulVec v = a • v) :
    (J⁻¹).mulVec v ≠ 0 ∧ (J⁻¹ * D * J).mulVec ((J⁻¹).mulVec v) = a • ((J⁻¹).mulVec v) := by
  have hc : J.mulVec ((J⁻¹).mulVec v) = v := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv J hJ, Matrix.one_mulVec]
  constructor
  · intro hz
    apply hv
    rw [← hc, hz, Matrix.mulVec_zero]
  · calc
      (J⁻¹ * D * J).mulVec ((J⁻¹).mulVec v) =
          (J⁻¹).mulVec (D.mulVec (J.mulVec ((J⁻¹).mulVec v))) := by
            rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      _ = (J⁻¹).mulVec (D.mulVec v) := by rw [hc]
      _ = a • ((J⁻¹).mulVec v) := by rw [hDv, Matrix.mulVec_smul]

/-- Nonzero eigenvectors for the actual cap shape matrix, with distinct
eigenvalues `-k` and `-2*k`. -/
theorem surfaceShapeMatrix_markedCap_center_eigenvectors {R L k : ℝ}
    (hR : 0 < R) (hL : 0 < L) (hk : k ≠ 0) (h ρ : ℝ) :
    let J := surfaceJacobian (markedCapCoordinates R L) (markedCapCenterParameter R L);
    let S := surfaceShapeMatrix (markedCapMap R h L k ρ)
      (markedCapNormal R L k ρ (markedCapCenterParameter R L)) (markedCapCenterParameter R L);
    -k ≠ -2 * k ∧
      (J⁻¹).mulVec ![1, 0] ≠ 0 ∧ (J⁻¹).mulVec ![0, 1] ≠ 0 ∧
      S.mulVec ((J⁻¹).mulVec ![1, 0]) = (-k) • ((J⁻¹).mulVec ![1, 0]) ∧
      S.mulVec ((J⁻¹).mulVec ![0, 1]) = (-2 * k) • ((J⁻¹).mulVec ![0, 1]) := by
  dsimp only
  rw [surfaceShapeMatrix_markedCap_center hR hL h k ρ]
  let J := surfaceJacobian (markedCapCoordinates R L) (markedCapCenterParameter R L)
  let D : Matrix (Fin 2) (Fin 2) ℝ := !![-k, 0; 0, -2 * k]
  have hJ : IsUnit J.det := isUnit_iff_ne_zero.mpr (surfaceJacobian_det_ne_zero
    (markedCapCoordinates_fderiv_injective_top hR hL (markedCapCenterParameter_mem hR hL).le
      (by rw [markedCapCenterParameter_parameter hR hL]; linarith)))
  have he0 : (![1, 0] : Fin 2 → ℝ) ≠ 0 := by
    intro hz
    have hh := congrFun hz 0
    norm_num at hh
  have he1 : (![0, 1] : Fin 2 → ℝ) ≠ 0 := by
    intro hz
    have hh := congrFun hz 1
    norm_num at hh
  have hd0 : D.mulVec ![1, 0] = (-k) • ![1, 0] := by
    ext i
    fin_cases i <;> simp [D, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hd1 : D.mulVec ![0, 1] = (-2 * k) • ![0, 1] := by
    ext i
    fin_cases i <;> simp [D, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hv0 := markedCap_conjugate_eigenvector J D hJ (-k) ![1, 0] he0 hd0
  have hv1 := markedCap_conjugate_eigenvector J D hJ (-2 * k) ![0, 1] he1 hd1
  refine ⟨?_, hv0.1, hv1.1, hv0.2, hv1.2⟩
  intro he
  apply hk
  linarith

theorem surfaceGaussianCurvature_markedCap_center {R L ρ : ℝ}
    (hR : 0 < R) (hL : 0 < L) (hρ : ρ ≠ 0) (h k : ℝ) :
    surfaceGaussianCurvature (markedCapMap R h L k ρ)
      (markedCapNormal R L k ρ (markedCapCenterParameter R L))
      (markedCapCenterParameter R L) = 2 * k ^ 2 := by
  rw [surfaceGaussianCurvature_markedCap_top hR hL hρ h k
    (markedCapCenterParameter_mem hR hL).le
    (by rw [markedCapCenterParameter_parameter hR hL]; linarith),
    markedCapCoordinates_center hR hL, markerCurvatureExpression_zero 1 2 k hρ]
  ring

private theorem markedCap_peak_parameters (L C B : ℝ) (hL : 0 < L) (hC : 0 < C) :
    ∃ k : ℝ, 0 < k ∧ B < 2 * k ^ 2 ∧ C < 2 * k ^ 2 ∧
      ∀ ε : ℝ, 0 < ε → ∃ ρ : ℝ, 0 < ρ ∧ ρ < L / 64 ∧ k * ρ ^ 2 / 2 < ε := by
  let k : ℝ := |B| + C + 1
  have hk1 : 1 < k := by dsimp [k]; linarith [abs_nonneg B]
  have hk : 0 < k := by linarith
  have hBk : B < k := by dsimp [k]; linarith [le_abs_self B]
  have hCk : C < k := by dsimp [k]; linarith [abs_nonneg B]
  have hkp : k < 2 * k ^ 2 := by nlinarith [sq_nonneg (k - 1)]
  refine ⟨k, hk, hBk.trans hkp, hCk.trans hkp, ?_⟩
  intro ε hε
  let ρ : ℝ := min (L / 128) (min 1 (ε / (k + 1)))
  have hpos : 0 < k + 1 := by linarith
  have hρ : 0 < ρ := by
    dsimp [ρ]
    exact lt_min (div_pos hL (by norm_num)) (lt_min zero_lt_one (div_pos hε hpos))
  have hρL : ρ ≤ L / 128 := min_le_left _ _
  have hρ1 : ρ ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hρε : ρ ≤ ε / (k + 1) := (min_le_right _ _).trans (min_le_right _ _)
  have hm : ρ * (k + 1) ≤ ε := (le_div_iff₀ hpos).mp hρε
  have hρsq : ρ ^ 2 ≤ ρ := by nlinarith [mul_nonneg hρ.le (sub_nonneg.mpr hρ1)]
  have hs := mul_le_mul_of_nonneg_left hρsq hk.le
  have hkr := mul_nonneg hk.le hρ.le
  refine ⟨ρ, hρ, by linarith, ?_⟩
  nlinarith

/-- The genuine unmarked-cap compact bound is used internally. The strength
is fixed before the support radius, which can meet any positive height budget.
The resulting unique peak is on the whole closed cap parameter disk. -/
theorem exists_markedCap_unique_peak {R L : ℝ} (hR : 0 < R) (hL : 0 < L) (h B : ℝ) :
    ∃ k : ℝ, 0 < k ∧ B < 2 * k ^ 2 ∧ ∀ ε : ℝ, 0 < ε → ∃ ρ : ℝ,
      0 < ρ ∧ ρ < L / 64 ∧ k * ρ ^ 2 / 2 < ε ∧
      surfaceGaussianCurvature (markedCapMap R h L k ρ)
        (markedCapNormal R L k ρ (markedCapCenterParameter R L))
        (markedCapCenterParameter R L) = 2 * k ^ 2 ∧
      ∀ y : PolarPoint, cartesianRadius y ≤ 1 → y ≠ markedCapCenterParameter R L →
        surfaceGaussianCurvature (markedCapMap R h L k ρ) (markedCapNormal R L k ρ y) y <
          2 * k ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := capDisk_curvature_uniform_bound hR hL h
  obtain ⟨k, hk, hBk, hCk, hradius⟩ := markedCap_peak_parameters L C B hL hC
  refine ⟨k, hk, hBk, ?_⟩
  intro ε hε
  obtain ⟨ρ, hρ, hsmall, hheight⟩ := hradius ε hε
  refine ⟨ρ, hρ, hsmall, hheight, surfaceGaussianCurvature_markedCap_center hR hL hρ.ne' h k, ?_⟩
  intro y hy hne
  by_cases ht : capDiskParameter R L y < L / 4
  · rw [surfaceGaussianCurvature_markedCap_top hR hL hρ.ne' h k hy ht]
    have hz : markedCapCoordinates R L y ≠ 0 := by
      intro hz
      exact hne ((markedCapCoordinates_eq_zero_iff hR hL hy ht).mp hz)
    simpa only [one_mul] using markerCurvatureExpression_lt_peak
      (A := (1 : ℝ)) (B := (2 : ℝ)) (by norm_num) (by norm_num) hk.ne' hρ.ne' hz
  · rw [surfaceGaussianCurvature_markedCap_of_not_top hR hL hρ hsmall h (le_of_not_gt ht)]
    exact (le_abs_self _).trans_lt (((hbound y hy).1).trans_lt hCk)

end ContinuousFlexibility
