module

public import ContinuousFlexibility.Geometry.SphereNormals
public import ContinuousFlexibility.Geometry.LocalSurfaceReparametrization
public import ContinuousFlexibility.Contracts.GraphCurvatureBounds

/-!
# Actual Gaussian curvature and the unique marker of the whole sphere

The global curvature is defined by the actual first and second derivatives in
the stereographic charts of the same constructed sphere, with its constructed
unit normal. Genuine chart germs and invertible differentials identify it with
the physical graph and cap curvatures. A compact bound for the graph and the
proved whole-cap strict peak then give a unique peak on the whole sphere.

This file does not assume a curvature field, a curvature comparison, or a
congruence-invariance law. Ambient image congruence and outward orientation are
separate subsequent obligations.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility

open Set Filter
open scoped ContDiff Manifold Topology

local notation "SpherePoint" => {v : E3 // v ∈ Metric.sphere (0 : E3) 1}

local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp [E3]⟩

set_option backward.isDefEq.respectTransparency false

def sphereNorthSurfaceChart (F : SpherePoint → E3) : PolarPoint → E3 :=
  F ∘ sphereNorthInverse

def sphereSouthSurfaceChart (F : SpherePoint → E3) : PolarPoint → E3 :=
  F ∘ sphereSouthInverse

/-- A global curvature defined from actual coordinate shape matrices. The two
hemispheres select genuine smooth local charts, including both polar points. -/
def sphereGaussianCurvature (F N : SpherePoint → E3) (x : SpherePoint) : ℝ :=
  if 0 ≤ (x : E3) 2 then
    surfaceGaussianCurvature (sphereNorthSurfaceChart F) (N x) (sphereNorthChart x)
  else
    surfaceGaussianCurvature (sphereSouthSurfaceChart F) (N x) (sphereSouthChart x)

def IsometricGraphDevelopment.markedSphereGaussianCurvature {A : FlatAnnularCore}
    (D : IsometricGraphDevelopment A) (R L k ρ t : ℝ) (x : SpherePoint) : ℝ :=
  sphereGaussianCurvature
    (fun y => sphereGraphCapFamily D (markedCapMap R A.cRight L k ρ) R L (y, t))
    (fun y => sphereMarkedNormal D R L k ρ (y, t)) x

theorem sphereGraphCapFamily_south_closed_germ {A : FlatAnnularCore}
    (D : IsometricGraphDevelopment A) {C : PolarPoint → E3} {R L : ℝ}
    (hR : A.b < R)
    (hcollar : ∀ y : PolarPoint, cartesianRadius y = 1 →
      (C ∘ capSphereRadialMap (capSphereRatio R L)) =ᶠ[𝓝 y]
        fun z => graphMap id (fun _ => A.cRight) ((R / cartesianRadius z ^ 2) • z))
    (q : SpherePoint × ℝ) (hq : (q.1 : E3) 2 ≤ 0) :
    sphereGraphCapFamily D C R L =ᶠ[𝓝 q]
      fun p : SpherePoint × ℝ => sphereSouthCap C R L p.1 := by
  by_cases hneg : (q.1 : E3) 2 < 0
  · exact sphereGraphCapFamily_south_germ D C R L q hneg
  · have hz : (q.1 : E3) 2 = 0 := le_antisymm hq (le_of_not_gt hneg)
    exact (sphereGraphCapFamily_north_germ D hR hcollar q hz.ge).trans
      (sphereGraphCap_equator_germ D hR hcollar q hz).symm

theorem markedSphereNorthSurfaceChart_germ {A : FlatAnnularCore}
    (D : IsometricGraphDevelopment A) {R L k ρ : ℝ}
    (hR : A.b < R) (hL : 0 < L) (hρ : 0 < ρ) (hsmall : ρ < L / 64)
    (t : ℝ) (x : SpherePoint) (hx : 0 ≤ (x : E3) 2) :
    sphereNorthSurfaceChart (fun y =>
      sphereGraphCapFamily D (markedCapMap R A.cRight L k ρ) R L (y, t))
      =ᶠ[𝓝 (sphereNorthChart x)] fun y => D.rotationFamily t (R • y) := by
  have hnx : x ∈ sphereNorthSource := by change (x : E3) 2 ≠ -1; linarith
  have hi : Tendsto (fun y : PolarPoint => (sphereNorthInverse y, t))
      (𝓝 (sphereNorthChart x)) (𝓝 (x, t)) := by
    have hc : ContinuousAt (fun y : PolarPoint => (sphereNorthInverse y, t))
        (sphereNorthChart x) :=
      contMDiff_sphereNorthInverse.continuous.continuousAt.prodMk continuousAt_const
    simpa only [sphereNorthInverse_chart x hnx] using hc.tendsto
  have hg := (sphereGraphCapFamily_north_germ D
    (C := markedCapMap R A.cRight L k ρ) hR
    (fun _ hy => markedCapMap_capSphereRadialMap_rim_germ (k := k)
      (A.b_pos.trans hR) hL hρ hsmall A.cRight hy) (x, t) hx).comp_tendsto hi
  simpa only [sphereNorthSurfaceChart, sphereNorthFamily, Function.comp_def,
    sphereNorthChart_inverse] using hg

theorem markedSphereSouthSurfaceChart_germ {A : FlatAnnularCore}
    (D : IsometricGraphDevelopment A) {R L k ρ : ℝ}
    (hR : A.b < R) (hL : 0 < L) (hρ : 0 < ρ) (hsmall : ρ < L / 64)
    (t : ℝ) (x : SpherePoint) (hx : (x : E3) 2 ≤ 0) :
    sphereSouthSurfaceChart (fun y =>
      sphereGraphCapFamily D (markedCapMap R A.cRight L k ρ) R L (y, t))
      =ᶠ[𝓝 (sphereSouthChart x)]
      markedCapMap R A.cRight L k ρ ∘ capSphereRadialMap (capSphereRatio R L) := by
  have hsx : x ∈ sphereSouthSource := by change (x : E3) 2 ≠ 1; linarith
  have hi : Tendsto (fun y : PolarPoint => (sphereSouthInverse y, t))
      (𝓝 (sphereSouthChart x)) (𝓝 (x, t)) := by
    have hc : ContinuousAt (fun y : PolarPoint => (sphereSouthInverse y, t))
        (sphereSouthChart x) :=
      contMDiff_sphereSouthInverse.continuous.continuousAt.prodMk continuousAt_const
    simpa only [sphereSouthInverse_chart x hsx] using hc.tendsto
  have hg := (sphereGraphCapFamily_south_closed_germ D
    (C := markedCapMap R A.cRight L k ρ) hR
    (fun _ hy => markedCapMap_capSphereRadialMap_rim_germ (k := k)
      (A.b_pos.trans hR) hL hρ hsmall A.cRight hy) (x, t) hx).comp_tendsto hi
  simpa only [sphereSouthSurfaceChart, sphereSouthCap, Function.comp_def,
    sphereSouthChart_inverse] using hg

private theorem sphereCurvature_scaling_injective {R : ℝ} (hR : 0 < R) (y : PolarPoint) :
    Function.Injective (fderiv ℝ (fun z : PolarPoint => R • z) y) := by
  let S : PolarPoint →L[ℝ] PolarPoint := R • ContinuousLinearMap.id ℝ PolarPoint
  have hS : (S : PolarPoint → PolarPoint) = fun z => R • z := by
    funext z
    simp only [S, smul_apply, ContinuousLinearMap.id_apply]
  rw [← hS, S.hasFDerivAt.fderiv]
  intro u v huv
  change R • u = R • v at huv
  have hh := congrArg (fun z : PolarPoint => R⁻¹ • z) huv
  simpa only [smul_smul, inv_mul_cancel₀ hR.ne', one_smul] using hh

/-- The actual north chart computes precisely the physical graph curvature. -/
theorem markedSphereNorthSurfaceChart_gaussian {A : FlatAnnularCore}
    (D : IsometricGraphDevelopment A) {R L k ρ : ℝ}
    (hR : A.b < R) (hL : 0 < L) (hρ : 0 < ρ) (hsmall : ρ < L / 64)
    (t : ℝ) (x : SpherePoint) (hx : 0 ≤ (x : E3) 2) :
    surfaceGaussianCurvature (sphereNorthSurfaceChart (fun y =>
      sphereGraphCapFamily D (markedCapMap R A.cRight L k ρ) R L (y, t)))
      (sphereMarkedNormal D R L k ρ (x, t)) (sphereNorthChart x) =
      surfaceGaussianCurvature (D.rotationFamily t)
        (D.rotationNormal t (R • sphereNorthChart x)) (R • sphereNorthChart x) := by
  have hscale : ContDiff ℝ ∞ (fun y : PolarPoint => R • y) := contDiff_const_smul R
  rw [sphereMarkedNormal_north D R L k ρ t x hx, sphereNorthPlanarMap,
    surfaceGaussianCurvature_congr_germ
      (markedSphereNorthSurfaceChart_germ D hR hL hρ hsmall t x hx)]
  exact surfaceGaussianCurvature_comp
    ((D.rotationFamily_smooth t).of_le (by simp : (2 : ℕ∞ω) ≤ ∞)).contDiffAt
    (hscale.of_le (by simp : (2 : ℕ∞ω) ≤ ∞)).contDiffAt
    (D.rotationNormal_isUnitSurfaceNormal t (R • sphereNorthChart x))
    (D.rotationFamily_immersion t (R • sphereNorthChart x))
    (sphereCurvature_scaling_injective (A.b_pos.trans hR) _)

/-- The actual south chart includes the constructed radial change of parameters. -/
theorem markedSphereSouthSurfaceChart_gaussian {A : FlatAnnularCore}
    (D : IsometricGraphDevelopment A) {R L k ρ : ℝ}
    (hR : A.b < R) (hL : 0 < L) (hk : 0 ≤ k) (hρ : 0 < ρ) (hsmall : ρ < L / 64)
    (t : ℝ) (x : SpherePoint) (hx : (x : E3) 2 ≤ 0) :
    surfaceGaussianCurvature (sphereSouthSurfaceChart (fun y =>
      sphereGraphCapFamily D (markedCapMap R A.cRight L k ρ) R L (y, t)))
      (sphereMarkedNormal D R L k ρ (x, t)) (sphereSouthChart x) =
      surfaceGaussianCurvature (markedCapMap R A.cRight L k ρ)
        (markedCapNormal R L k ρ
          (capSphereRadialMap (capSphereRatio R L) (sphereSouthChart x)))
        (capSphereRadialMap (capSphereRatio R L) (sphereSouthChart x)) := by
  have hRp := A.b_pos.trans hR
  have ha := capSphereRatio_mem hRp hL
  have hsx : x ∈ sphereSouthSource := by change (x : E3) 2 ≠ 1; linarith
  have hr := (sphereSouthChart_radius_le_one_iff x hsx).mpr hx
  have hφ := capSphereRadialMap_mapsTo_disk ha.1 ha.2 hr
  rw [sphereMarkedNormal_south D hR hL hρ hsmall t x hx,
    surfaceGaussianCurvature_congr_germ
      (markedSphereSouthSurfaceChart_germ D hR hL hρ hsmall t x hx)]
  exact surfaceGaussianCurvature_comp
    ((contDiff_markedCapMap hRp hL A.cRight k ρ).of_le
      (by simp : (2 : ℕ∞ω) ≤ ∞)).contDiffAt
    ((contDiff_capSphereRadialMap (capSphereRatio R L)).of_le
      (by simp : (2 : ℕ∞ω) ≤ ∞)).contDiffAt
    (isUnitSurfaceNormal_markedCap hRp hL hρ hsmall A.cRight _)
    (markedCapMap_fderiv_injective hRp hL hk hρ hsmall A.cRight hφ)
    (capSphereRadialMap_fderiv_injective ha.1 ha.2 _)

theorem IsometricGraphDevelopment.markedSphereGaussianCurvature_north
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) {R L k ρ : ℝ}
    (hR : A.b < R) (hL : 0 < L) (hρ : 0 < ρ) (hsmall : ρ < L / 64)
    (t : ℝ) (x : SpherePoint) (hx : 0 ≤ (x : E3) 2) :
    D.markedSphereGaussianCurvature R L k ρ t x =
      surfaceGaussianCurvature (D.rotationFamily t)
        (D.rotationNormal t (R • sphereNorthChart x)) (R • sphereNorthChart x) := by
  simp only [IsometricGraphDevelopment.markedSphereGaussianCurvature,
    sphereGaussianCurvature, hx, ↓reduceIte]
  exact markedSphereNorthSurfaceChart_gaussian D hR hL hρ hsmall t x hx

theorem IsometricGraphDevelopment.markedSphereGaussianCurvature_south
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) {R L k ρ : ℝ}
    (hR : A.b < R) (hL : 0 < L) (hk : 0 ≤ k) (hρ : 0 < ρ) (hsmall : ρ < L / 64)
    (t : ℝ) (x : SpherePoint) (hx : (x : E3) 2 < 0) :
    D.markedSphereGaussianCurvature R L k ρ t x =
      surfaceGaussianCurvature (markedCapMap R A.cRight L k ρ)
        (markedCapNormal R L k ρ
          (capSphereRadialMap (capSphereRatio R L) (sphereSouthChart x)))
        (capSphereRadialMap (capSphereRatio R L) (sphereSouthChart x)) := by
  simp only [IsometricGraphDevelopment.markedSphereGaussianCurvature,
    sphereGaussianCurvature, not_le.mpr hx, ↓reduceIte]
  exact markedSphereSouthSurfaceChart_gaussian D hR hL hk hρ hsmall t x hx.le

/-- The same actual coordinate calculation for the signed mean curvature will
also distinguish the two possible unit normals at the marker. -/
theorem markedSphereSouthSurfaceChart_mean {A : FlatAnnularCore}
    (D : IsometricGraphDevelopment A) {R L k ρ : ℝ}
    (hR : A.b < R) (hL : 0 < L) (hk : 0 ≤ k) (hρ : 0 < ρ) (hsmall : ρ < L / 64)
    (t : ℝ) (x : SpherePoint) (hx : (x : E3) 2 ≤ 0) :
    surfaceMeanCurvature (sphereSouthSurfaceChart (fun y =>
      sphereGraphCapFamily D (markedCapMap R A.cRight L k ρ) R L (y, t)))
      (sphereMarkedNormal D R L k ρ (x, t)) (sphereSouthChart x) =
      surfaceMeanCurvature (markedCapMap R A.cRight L k ρ)
        (markedCapNormal R L k ρ
          (capSphereRadialMap (capSphereRatio R L) (sphereSouthChart x)))
        (capSphereRadialMap (capSphereRatio R L) (sphereSouthChart x)) := by
  have hRp := A.b_pos.trans hR
  have ha := capSphereRatio_mem hRp hL
  have hsx : x ∈ sphereSouthSource := by change (x : E3) 2 ≠ 1; linarith
  have hr := (sphereSouthChart_radius_le_one_iff x hsx).mpr hx
  have hφ := capSphereRadialMap_mapsTo_disk ha.1 ha.2 hr
  rw [sphereMarkedNormal_south D hR hL hρ hsmall t x hx,
    surfaceMeanCurvature_congr_germ
      (markedSphereSouthSurfaceChart_germ D hR hL hρ hsmall t x hx)]
  exact surfaceMeanCurvature_comp
    ((contDiff_markedCapMap hRp hL A.cRight k ρ).of_le
      (by simp : (2 : ℕ∞ω) ≤ ∞)).contDiffAt
    ((contDiff_capSphereRadialMap (capSphereRatio R L)).of_le
      (by simp : (2 : ℕ∞ω) ≤ ∞)).contDiffAt
    (isUnitSurfaceNormal_markedCap hRp hL hρ hsmall A.cRight _)
    (markedCapMap_fderiv_injective hRp hL hk hρ hsmall A.cRight hφ)
    (capSphereRadialMap_fderiv_injective ha.1 ha.2 _)

theorem IsometricGraphDevelopment.markedSphereGaussianCurvature_periodic
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) (R L k ρ : ℝ)
    (x : SpherePoint) :
    Function.Periodic (fun t => D.markedSphereGaussianCurvature R L k ρ t x) 1 := by
  intro t
  have hF : (fun y : SpherePoint =>
      sphereGraphCapFamily D (markedCapMap R A.cRight L k ρ) R L (y, t + 1)) =
      fun y => sphereGraphCapFamily D (markedCapMap R A.cRight L k ρ) R L (y, t) :=
    funext (fun y => sphereGraphCapFamily_periodic D _ R L y t)
  have hN : (fun y : SpherePoint => sphereMarkedNormal D R L k ρ (y, t + 1)) =
      fun y => sphereMarkedNormal D R L k ρ (y, t) :=
    funext (fun y => sphereMarkedNormal_periodic D R L k ρ y t)
  unfold IsometricGraphDevelopment.markedSphereGaussianCurvature
  dsimp only
  rw [hF, hN]

private theorem sphereCurvature_horizontal_normal (h : ℝ) (x : PolarPoint) :
    graphUpwardNormal (fun _ : PolarPoint => h) x = e3Basis 2 := by
  simp [graphUpwardNormal, graphAreaDensity, graphAreaSq, radialPartial,
    angularPartial, graphMap, e3Basis]

theorem surfaceGaussianCurvature_horizontal (h : ℝ) (x : PolarPoint) :
    surfaceGaussianCurvature (graphMap id (fun _ => h)) (e3Basis 2) x = 0 := by
  rw [← sphereCurvature_horizontal_normal h x,
    surfaceGaussianCurvature_heightGraph (contDiff_const :
      ContDiff ℝ ∞ (fun _ : PolarPoint => h))]
  have hH : graphHessian (fun _ : PolarPoint => h) x = 0 := by
    ext i j
    simp [graphHessian]
  rw [hH]
  simp

theorem IsometricGraphDevelopment.rotationFamily_gaussianCurvature_outside
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) (t : ℝ)
    {x : PolarPoint} (hx : A.b < cartesianRadius x) :
    surfaceGaussianCurvature (D.rotationFamily t) (D.rotationNormal t x) x = 0 := by
  have hg : D.rotationFamily t =ᶠ[𝓝 x] graphMap id (fun _ => A.cRight) := by
    filter_upwards [(isOpen_lt continuous_const continuous_cartesianRadius).mem_nhds hx]
      with y hy
    exact D.phase_flat_outside t hy
  rw [D.rotationNormal_outside t hx, surfaceGaussianCurvature_congr_germ hg]
  exact surfaceGaussianCurvature_horizontal A.cRight x

theorem IsometricGraphDevelopment.markedSphereGaussianCurvature_equator
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) {R L k ρ : ℝ}
    (hR : A.b < R) (hL : 0 < L) (hρ : 0 < ρ) (hsmall : ρ < L / 64)
    (t : ℝ) (x : SpherePoint) (hx : (x : E3) 2 = 0) :
    D.markedSphereGaussianCurvature R L k ρ t x = 0 := by
  rw [D.markedSphereGaussianCurvature_north hR hL hρ hsmall t x hx.ge]
  apply D.rotationFamily_gaussianCurvature_outside t
  rw [capDisk_radius_smul, abs_of_pos (A.b_pos.trans hR),
    (sphere_equator_chart_radii hx).1, mul_one]
  exact hR

/-- A true sphere point above the already constructed cap-center parameter. -/
theorem exists_markedSphereCenterParameter {R L : ℝ} (hR : 0 < R) (hL : 0 < L) :
    ∃ x : SpherePoint, (x : E3) 2 < 0 ∧
      capSphereRadialMap (capSphereRatio R L) (sphereSouthChart x) =
        markedCapCenterParameter R L := by
  obtain ⟨u, hu, hmap⟩ := capSphereRadialMap_surjOn_disk (capSphereRatio R L)
    (markedCapCenterParameter_mem hR hL).le
  have hult : cartesianRadius u < 1 := by
    apply lt_of_le_of_ne hu
    intro he
    have hid := capSphereRadialMap_boundary (capSphereRatio R L) he
    have heq : u = markedCapCenterParameter R L := hid.symm.trans hmap
    have hh := markedCapCenterParameter_mem hR hL
    rw [← heq, he] at hh
    exact (lt_irrefl (1 : ℝ)) hh
  refine ⟨sphereSouthInverse u, ?_, ?_⟩
  · change (sphereSouthInvVector u) 2 < 0
    rw [sphereSouthInvVector, graphMap_two]
    apply div_neg_of_neg_of_pos _ (sphereStereoDenom_pos u)
    rw [spherePlaneEnergy_eq_radius_sq]
    have hn : 0 ≤ cartesianRadius u := norm_nonneg _
    have hp : 0 < (1 - cartesianRadius u) * (1 + cartesianRadius u) :=
      mul_pos (sub_pos.mpr hult) (by linarith)
    nlinarith [hp]
  · simpa only [sphereSouthChart_inverse] using hmap

def markedSphereCenterParameter {R L : ℝ} (hR : 0 < R) (hL : 0 < L) : SpherePoint :=
  (exists_markedSphereCenterParameter hR hL).choose

theorem markedSphereCenterParameter_south {R L : ℝ} (hR : 0 < R) (hL : 0 < L) :
    ((markedSphereCenterParameter hR hL : SpherePoint) : E3) 2 < 0 :=
  (exists_markedSphereCenterParameter hR hL).choose_spec.1

theorem markedSphereCenterParameter_coordinates {R L : ℝ} (hR : 0 < R) (hL : 0 < L) :
    capSphereRadialMap (capSphereRatio R L)
        (sphereSouthChart (markedSphereCenterParameter hR hL)) =
      markedCapCenterParameter R L :=
  (exists_markedSphereCenterParameter hR hL).choose_spec.2

theorem markedSphereCenterParameter_coordinates_eq_iff {R L : ℝ}
    (hR : 0 < R) (hL : 0 < L) {x : SpherePoint} (hx : x ∈ sphereSouthSource) :
    capSphereRadialMap (capSphereRatio R L) (sphereSouthChart x) =
        markedCapCenterParameter R L ↔ x = markedSphereCenterParameter hR hL := by
  constructor
  · intro he
    have ha := capSphereRatio_mem hR hL
    have hc := (capSphereRadialMap_injective ha.1 ha.2)
      (he.trans (markedSphereCenterParameter_coordinates hR hL).symm)
    apply sphereSouthChart_injectiveOn hx _ hc
    change ((markedSphereCenterParameter hR hL : SpherePoint) : E3) 2 ≠ 1
    linarith [markedSphereCenterParameter_south hR hL]
  · rintro rfl
    exact markedSphereCenterParameter_coordinates hR hL

theorem IsometricGraphDevelopment.markedSphereCenter_image {A : FlatAnnularCore}
    (D : IsometricGraphDevelopment A) {R L : ℝ} (hR : A.b < R) (hL : 0 < L)
    (k ρ t : ℝ) :
    sphereGraphCapFamily D (markedCapMap R A.cRight L k ρ) R L
        (markedSphereCenterParameter (A.b_pos.trans hR) hL, t) =
      markedCapMap R A.cRight L k ρ (markedCapCenterParameter R L) := by
  simp only [sphereGraphCapFamily, not_le.mpr
    (markedSphereCenterParameter_south (A.b_pos.trans hR) hL), ↓reduceIte,
    sphereSouthCap, markedSphereCenterParameter_coordinates]

theorem IsometricGraphDevelopment.markedSphereCenter_normal {A : FlatAnnularCore}
    (D : IsometricGraphDevelopment A) {R L k ρ : ℝ}
    (hR : A.b < R) (hL : 0 < L) (hρ : 0 < ρ) (hsmall : ρ < L / 64) (t : ℝ) :
    sphereMarkedNormal D R L k ρ
      (markedSphereCenterParameter (A.b_pos.trans hR) hL, t) = e3Basis 2 := by
  rw [sphereMarkedNormal_south D hR hL hρ hsmall t _
    (markedSphereCenterParameter_south (A.b_pos.trans hR) hL).le,
    markedSphereCenterParameter_coordinates]
  exact markedCapNormal_center (A.b_pos.trans hR) hL k ρ

theorem IsometricGraphDevelopment.markedSphereGaussianCurvature_center
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) {R L k ρ : ℝ}
    (hR : A.b < R) (hL : 0 < L) (hk : 0 ≤ k) (hρ : 0 < ρ) (hsmall : ρ < L / 64)
    (t : ℝ) :
    D.markedSphereGaussianCurvature R L k ρ t
      (markedSphereCenterParameter (A.b_pos.trans hR) hL) = 2 * k ^ 2 := by
  rw [D.markedSphereGaussianCurvature_south hR hL hk hρ hsmall t _
    (markedSphereCenterParameter_south (A.b_pos.trans hR) hL),
    markedSphereCenterParameter_coordinates]
  exact surfaceGaussianCurvature_markedCap_center (A.b_pos.trans hR) hL hρ.ne' A.cRight k

/-- The actual fixed marker has nonzero signed mean curvature for `k > 0`.
This does not assert outwardness of the supplied smooth unit normal. -/
theorem IsometricGraphDevelopment.markedSphereCenter_mean {A : FlatAnnularCore}
    (D : IsometricGraphDevelopment A) {R L k ρ : ℝ}
    (hR : A.b < R) (hL : 0 < L) (hk : 0 ≤ k) (hρ : 0 < ρ) (hsmall : ρ < L / 64)
    (t : ℝ) :
    surfaceMeanCurvature (sphereSouthSurfaceChart (fun y =>
      sphereGraphCapFamily D (markedCapMap R A.cRight L k ρ) R L (y, t)))
      (sphereMarkedNormal D R L k ρ
        (markedSphereCenterParameter (A.b_pos.trans hR) hL, t))
      (sphereSouthChart (markedSphereCenterParameter (A.b_pos.trans hR) hL)) =
      -3 * k / 2 := by
  rw [markedSphereSouthSurfaceChart_mean D hR hL hk hρ hsmall t _
    (markedSphereCenterParameter_south (A.b_pos.trans hR) hL).le,
    markedSphereCenterParameter_coordinates, surfaceMeanCurvature,
    surfaceShapeMatrix_markedCap_center (A.b_pos.trans hR) hL A.cRight k ρ]
  rw [Matrix.trace_conj' (surfaceJacobian_isUnit
    (markedCapCoordinates_fderiv_injective_top (A.b_pos.trans hR) hL
      (markedCapCenterParameter_mem (A.b_pos.trans hR) hL).le
      (by rw [markedCapCenterParameter_parameter (A.b_pos.trans hR) hL]; linarith)))]
  simp only [Matrix.trace_fin_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- The strength is chosen from actual whole-graph and whole-cap bounds before
the support radius. The maximum is strict at every other point of the sphere. -/
theorem IsometricGraphDevelopment.exists_markedSphere_unique_peak
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) {R L : ℝ}
    (hR : A.b < R) (hL : 0 < L) :
    ∃ k : ℝ, 0 < k ∧ ∀ ε : ℝ, 0 < ε → ∃ ρ : ℝ,
      0 < ρ ∧ ρ < L / 64 ∧ k * ρ ^ 2 / 2 < ε ∧
      ∀ t : ℝ,
        D.markedSphereGaussianCurvature R L k ρ t
          (markedSphereCenterParameter (A.b_pos.trans hR) hL) = 2 * k ^ 2 ∧
        ∀ x : SpherePoint, x ≠ markedSphereCenterParameter (A.b_pos.trans hR) hL →
          D.markedSphereGaussianCurvature R L k ρ t x < 2 * k ^ 2 := by
  obtain ⟨B, _, hB⟩ := D.exists_rotationFamily_curvature_bounds R
  obtain ⟨k, hk, hBk, hradius⟩ :=
    exists_markedCap_unique_peak (A.b_pos.trans hR) hL A.cRight B
  refine ⟨k, hk, fun ε hε => ?_⟩
  obtain ⟨ρ, hρ, hsmall, hheight, _, hcap⟩ := hradius ε hε
  refine ⟨ρ, hρ, hsmall, hheight, fun t =>
    ⟨D.markedSphereGaussianCurvature_center hR hL hk.le hρ hsmall t, ?_⟩⟩
  intro x hne
  by_cases hx : 0 ≤ (x : E3) 2
  · rw [D.markedSphereGaussianCurvature_north hR hL hρ hsmall t x hx]
    have hnx : x ∈ sphereNorthSource := by change (x : E3) 2 ≠ -1; linarith
    have hr := (sphereNorthChart_radius_le_one_iff x hnx).mpr hx
    have hrad : cartesianRadius (R • sphereNorthChart x) ≤ R := by
      rw [capDisk_radius_smul, abs_of_pos (A.b_pos.trans hR)]
      exact (mul_le_mul_of_nonneg_left hr (A.b_pos.trans hR).le).trans (by simp)
    exact (le_abs_self _).trans_lt (((hB t _ hrad).1).trans_lt hBk)
  · have hs : x ∈ sphereSouthSource := by change (x : E3) 2 ≠ 1; linarith
    have ha := capSphereRatio_mem (A.b_pos.trans hR) hL
    have hr := capSphereRadialMap_mapsTo_disk ha.1 ha.2
      ((sphereSouthChart_radius_le_one_iff x hs).mpr (lt_of_not_ge hx).le)
    rw [D.markedSphereGaussianCurvature_south hR hL hk.le hρ hsmall t x (lt_of_not_ge hx)]
    exact hcap _ hr (fun he => hne
      ((markedSphereCenterParameter_coordinates_eq_iff (A.b_pos.trans hR) hL hs).mp he))

/-- The whole-sphere peak, with the equality characterization needed to identify
its parameter from intrinsic curvature, for every real phase simultaneously. -/
theorem IsometricGraphDevelopment.exists_markedSphere_unique_peak_iff
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) {R L : ℝ}
    (hR : A.b < R) (hL : 0 < L) :
    ∃ k : ℝ, 0 < k ∧ ∀ ε : ℝ, 0 < ε → ∃ ρ : ℝ,
      0 < ρ ∧ ρ < L / 64 ∧ k * ρ ^ 2 / 2 < ε ∧
      ∀ t : ℝ, ∀ x : SpherePoint,
        D.markedSphereGaussianCurvature R L k ρ t x ≤ 2 * k ^ 2 ∧
        (D.markedSphereGaussianCurvature R L k ρ t x = 2 * k ^ 2 ↔
          x = markedSphereCenterParameter (A.b_pos.trans hR) hL) := by
  obtain ⟨k, hk, hradius⟩ := D.exists_markedSphere_unique_peak hR hL
  refine ⟨k, hk, fun ε hε => ?_⟩
  obtain ⟨ρ, hρ, hsmall, hheight, hpeak⟩ := hradius ε hε
  refine ⟨ρ, hρ, hsmall, hheight, fun t x => ?_⟩
  by_cases hx : x = markedSphereCenterParameter (A.b_pos.trans hR) hL
  · subst x
    exact ⟨(hpeak t).1.le, by simp only [(hpeak t).1]⟩
  · exact ⟨((hpeak t).2 x hx).le,
      ⟨fun he => ((hpeak t).2 x hx).ne he |>.elim, fun he => (hx he).elim⟩⟩

end ContinuousFlexibility
