module

public import ContinuousFlexibility.Geometry.SphereMetric
public import ContinuousFlexibility.Geometry.MarkedCapDiskCurvature
public import ContinuousFlexibility.Contracts.GraphFamilyCurvature

/-!
# The actual smooth unit normal of the marked sphere family

The graph normal and the constructed marked-cap normal agree with the upward
vertical vector on a whole open equatorial neighborhood. Their piecewise
formula is jointly smooth and orthogonal to the actual vector-valued manifold
derivative of the same sphere family. Outward orientation is a separate claim.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility

open Filter Set
open scoped ContDiff Manifold Topology

local notation "SpherePoint" => {v : E3 // v ∈ Metric.sphere (0 : E3) 1}
local notation "SphereTimeModel" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp [E3]⟩

set_option backward.isDefEq.respectTransparency false

private theorem sphereNormal_physicalHeight_outside {A : FlatAnnularCore}
    (D : IsometricGraphDevelopment A) {x : PolarPoint} (hx : A.b < cartesianRadius x) :
    D.physicalHeight x = A.cRight := by
  have hi : D.planar.symm x = x := by
    apply D.planar.injective
    simpa only [D.planar.apply_symm_apply] using (D.normalized_outside x hx).symm
  change A.cartesianHeight (D.planar.symm x) = A.cRight
  rw [hi]
  exact A.cartesianHeight_right hx.le

private theorem sphereNormal_graph_vertical {z : PolarPoint → ℝ} {x : PolarPoint}
    (hd : fderiv ℝ z x = 0) : graphUpwardNormal z x = e3Basis 2 := by
  simp [graphUpwardNormal, graphAreaDensity, graphAreaSq, radialPartial,
    angularPartial, hd, graphMap]

theorem IsometricGraphDevelopment.rotationNormal_outside {A : FlatAnnularCore}
    (D : IsometricGraphDevelopment A) (t : ℝ) {x : PolarPoint}
    (hx : A.b < cartesianRadius x) : D.rotationNormal t x = e3Basis 2 := by
  have hup {y : PolarPoint} (hy : A.b < cartesianRadius y) :
      D.upwardGraphNormal y = e3Basis 2 := by
    have hg : D.physicalHeight =ᶠ[𝓝 y] fun _ => A.cRight := by
      have hn : {z : PolarPoint | A.b < cartesianRadius z} ∈ 𝓝 y :=
        (isOpen_lt continuous_const continuous_cartesianRadius).mem_nhds hy
      filter_upwards [hn] with z hz
      exact sphereNormal_physicalHeight_outside D hz
    have hd : fderiv ℝ D.physicalHeight y = 0 := by
      rw [hg.fderiv_eq (𝕜 := ℝ)]
      exact fderiv_const_apply _
    rw [IsometricGraphDevelopment.upwardGraphNormal, D.normalized_outside y hy]
    exact sphereNormal_graph_vertical hd
  rw [IsometricGraphDevelopment.rotationNormal, hup (by simpa using hx)]
  ext i
  fin_cases i <;> simp [axialRotation_apply, axialRotationMap, graphBaseProjection,
    e3Basis, planarRotation, planeRotationLinearMap_apply]

private theorem sphereNormal_marker_zero_germ {R L k ρ : ℝ}
    (hR : 0 < R) (hL : 0 < L) (hρ : 0 < ρ) (hsmall : ρ < L / 64)
    {x : PolarPoint} (hx : cartesianRadius (x + markedCapCenter R L) < R + L / 16) :
    markerBump 1 2 k ρ =ᶠ[𝓝 x] fun _ => 0 := by
  have hc : Continuous (fun z : PolarPoint => cartesianRadius (z + markedCapCenter R L)) :=
    continuous_cartesianRadius.comp (continuous_id.add continuous_const)
  have hn : {z : PolarPoint | cartesianRadius (z + markedCapCenter R L) < R + L / 16} ∈ 𝓝 x :=
    (isOpen_lt hc continuous_const).mem_nhds hx
  filter_upwards [hn] with z hz
  by_contra hne
  have hh := markedCap_marker_support_lower (k := k) hR hL hρ hsmall
    (x := z + markedCapCenter R L) (by simpa only [add_sub_cancel_right] using hne)
  exact (not_lt_of_ge hz.le) hh

theorem markedCapNormal_eq_vertical_of_top_inner {R L k ρ : ℝ}
    (hR : 0 < R) (hL : 0 < L) (hρ : 0 < ρ) (hsmall : ρ < L / 64)
    {y : PolarPoint} (htop : capDiskParameter R L y ≤ L / 4)
    (hinner : cartesianRadius (capDiskBase R L y) < R + L / 16) :
    markedCapNormal R L k ρ y = e3Basis 2 := by
  rw [markedCapNormal_eq_top hL k ρ htop]
  apply sphereNormal_graph_vertical
  have hg := sphereNormal_marker_zero_germ (k := k) hR hL hρ hsmall
    (x := markedCapCoordinates R L y)
    (by simpa only [markedCapCoordinates, sub_add_cancel] using hinner)
  rw [hg.fderiv_eq (𝕜 := ℝ)]
  exact fderiv_const_apply _

theorem markedCapNormal_rim_germ {R L k ρ : ℝ}
    (hR : 0 < R) (hL : 0 < L) (hρ : 0 < ρ) (hsmall : ρ < L / 64)
    {y : PolarPoint} (hy : cartesianRadius y = 1) :
    markedCapNormal R L k ρ =ᶠ[𝓝 y] fun _ => e3Basis 2 := by
  have hs : capDiskParameter R L y = 0 := by simp [capDiskParameter, hy]
  have hb : cartesianRadius (capDiskBase R L y) = R := by
    rw [capDiskBase_radius hR hL hy.le, hs]
    simp [capMeridianRadius]
  have hcs : Continuous (capDiskParameter R L) :=
    continuous_const.mul (continuous_const.sub continuous_cartesianRadius)
  have hcb : Continuous (fun z => cartesianRadius (capDiskBase R L z)) :=
    continuous_cartesianRadius.comp (markedCap_contDiff_base hR hL).continuous
  have hns : ∀ᶠ z in 𝓝 y, capDiskParameter R L z < L / 4 :=
    hcs.continuousAt.eventually_lt continuousAt_const (by rw [hs]; linarith)
  have hnb : ∀ᶠ z in 𝓝 y, cartesianRadius (capDiskBase R L z) < R + L / 16 :=
    hcb.continuousAt.eventually_lt continuousAt_const (by rw [hb]; linarith)
  filter_upwards [hns, hnb] with z hzs hzb
  exact markedCapNormal_eq_vertical_of_top_inner hR hL hρ hsmall hzs.le hzb

theorem markedCapNormal_capSphereRadialMap_rim_germ {R L k ρ : ℝ}
    (hR : 0 < R) (hL : 0 < L) (hρ : 0 < ρ) (hsmall : ρ < L / 64)
    {y : PolarPoint} (hy : cartesianRadius y = 1) :
    (markedCapNormal R L k ρ ∘ capSphereRadialMap (capSphereRatio R L)) =ᶠ[𝓝 y]
      fun _ => e3Basis 2 := by
  have ht : Tendsto (capSphereRadialMap (capSphereRatio R L)) (𝓝 y) (𝓝 y) := by
    have hc : ContinuousAt (capSphereRadialMap (capSphereRatio R L)) y :=
      (contDiff_capSphereRadialMap (capSphereRatio R L)).continuous.continuousAt
    simpa only [capSphereRadialMap_boundary _ hy] using
      hc.tendsto
  exact (markedCapNormal_rim_germ hR hL hρ hsmall hy).comp_tendsto ht

def sphereNorthNormal {A : FlatAnnularCore} (D : IsometricGraphDevelopment A)
    (R : ℝ) (q : SpherePoint × ℝ) : E3 :=
  D.rotationNormal q.2 (sphereNorthPlanarMap R q.1)

def sphereMarkedNormal {A : FlatAnnularCore} (D : IsometricGraphDevelopment A)
    (R L k ρ : ℝ) (q : SpherePoint × ℝ) : E3 :=
  if 0 ≤ (q.1 : E3) 2 then sphereNorthNormal D R q
  else sphereSouthCap (markedCapNormal R L k ρ) R L q.1

theorem contMDiffAt_sphereNorthNormal {A : FlatAnnularCore}
    (D : IsometricGraphDevelopment A) (R : ℝ) (q : SpherePoint × ℝ)
    (hq : q.1 ∈ sphereNorthSource) :
    ContMDiffAt SphereTimeModel 𝓘(ℝ, E3) ∞ (sphereNorthNormal D R) q := by
  change ContMDiffAt SphereTimeModel 𝓘(ℝ, E3) ∞
    (fun p : SpherePoint × ℝ => D.rotationNormal p.2 (R • sphereNorthChart p.1)) q
  have hfst : ContMDiffAt SphereTimeModel (𝓡 2) ∞ Prod.fst q := contMDiffAt_fst
  have hc : ContMDiffAt SphereTimeModel 𝓘(ℝ, PolarPoint) ∞
      (fun p : SpherePoint × ℝ => sphereNorthChart p.1) q :=
    (contMDiffAt_sphereNorthChart q.1 hq).comp q hfst
  have ht : ContMDiffAt SphereTimeModel 𝓘(ℝ, ℝ) ∞ Prod.snd q := contMDiffAt_snd
  have hpair : ContMDiffAt SphereTimeModel 𝓘(ℝ, PolarPoint × ℝ) ∞
      (fun p : SpherePoint × ℝ => (sphereNorthChart p.1, p.2)) q := hc.prodMk_space ht
  have hRconst : ContDiff ℝ ∞ (fun _ : PolarPoint × ℝ => R) := contDiff_const
  have hspace : ContDiff ℝ ∞ (fun p : PolarPoint × ℝ => p.1) := contDiff_fst
  have hs : ContDiff ℝ ∞ (fun p : PolarPoint × ℝ => R • p.1) := hRconst.smul hspace
  have ht' : ContDiff ℝ ∞ (fun p : PolarPoint × ℝ => p.2) := contDiff_snd
  have hinput : ContDiff ℝ ∞ (fun p : PolarPoint × ℝ => (p.2, R • p.1)) := ht'.prodMk hs
  have hf : ContDiff ℝ ∞ (fun p : PolarPoint × ℝ => D.rotationNormal p.2 (R • p.1)) :=
    by simpa only [Function.comp_def] using D.rotationNormal_joint_smooth.comp hinput
  have hFat : ContMDiffAt 𝓘(ℝ, PolarPoint × ℝ) 𝓘(ℝ, E3) ∞
      (fun p : PolarPoint × ℝ => D.rotationNormal p.2 (R • p.1))
      (sphereNorthChart q.1, q.2) := hf.contDiffAt.contMDiffAt
  simpa only [Function.comp_def] using hFat.comp q hpair

theorem sphereNorthNormal_equator_germ {A : FlatAnnularCore}
    (D : IsometricGraphDevelopment A) {R : ℝ} (hR : A.b < R)
    (q : SpherePoint × ℝ) (hq : (q.1 : E3) 2 = 0) :
    sphereNorthNormal D R =ᶠ[𝓝 q] fun _ => e3Basis 2 := by
  have hsrc := (sphere_equator_sources hq).1
  have hc : ContinuousAt (fun p : SpherePoint × ℝ =>
      cartesianRadius (sphereNorthPlanarMap R p.1)) q :=
    continuous_cartesianRadius.continuousAt.comp
      ((contMDiffAt_sphereNorthPlanarMap R q.1 hsrc).continuousAt.comp continuousAt_fst)
  have hr : A.b < cartesianRadius (sphereNorthPlanarMap R q.1) := by
    rw [sphereNorthPlanarMap, capDisk_radius_smul,
      abs_of_pos (A.b_pos.trans hR), (sphere_equator_chart_radii hq).1, mul_one]
    exact hR
  filter_upwards [continuousAt_const.eventually_lt hc hr] with p hp
  exact D.rotationNormal_outside p.2 hp

theorem sphereSouthNormal_equator_germ {A : FlatAnnularCore}
    {R L k ρ : ℝ}
    (hR : A.b < R) (hL : 0 < L) (hρ : 0 < ρ) (hsmall : ρ < L / 64)
    (q : SpherePoint × ℝ) (hq : (q.1 : E3) 2 = 0) :
    (fun p : SpherePoint × ℝ => sphereSouthCap (markedCapNormal R L k ρ) R L p.1)
      =ᶠ[𝓝 q] fun _ => e3Basis 2 := by
  have hs := (sphere_equator_sources hq).2
  have hc := (contMDiffAt_sphereSouthChart q.1 hs).continuousAt.comp continuousAt_fst
  exact (markedCapNormal_capSphereRadialMap_rim_germ (k := k)
    (A.b_pos.trans hR) hL hρ hsmall (sphere_equator_chart_radii hq).2).comp_tendsto hc.tendsto

/-- Both branches agree on a joint open neighborhood, not just on the equator. -/
theorem sphereMarkedNormal_equator_germ {A : FlatAnnularCore}
    (D : IsometricGraphDevelopment A) {R L k ρ : ℝ}
    (hR : A.b < R) (hL : 0 < L) (hρ : 0 < ρ) (hsmall : ρ < L / 64)
    (q : SpherePoint × ℝ) (hq : (q.1 : E3) 2 = 0) :
    sphereMarkedNormal D R L k ρ =ᶠ[𝓝 q] fun _ => e3Basis 2 := by
  filter_upwards [sphereNorthNormal_equator_germ D hR q hq,
    sphereSouthNormal_equator_germ (k := k) hR hL hρ hsmall q hq] with p hn hs
  change (if 0 ≤ (p.1 : E3) 2 then _ else _) = _
  split_ifs
  · exact hn
  · exact hs

theorem contMDiff_sphereMarkedNormal {A : FlatAnnularCore}
    (D : IsometricGraphDevelopment A) {R L k ρ : ℝ}
    (hR : A.b < R) (hL : 0 < L) (hρ : 0 < ρ) (hsmall : ρ < L / 64) :
    ContMDiff SphereTimeModel 𝓘(ℝ, E3) ∞ (sphereMarkedNormal D R L k ρ) := by
  intro q
  have hcoord : Continuous (fun p : SpherePoint × ℝ => (p.1 : E3) 2) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).continuous.comp
      (continuous_subtype_val.comp continuous_fst)
  by_cases hp : 0 < (q.1 : E3) 2
  · have hn : q.1 ∈ sphereNorthSource := by change (q.1 : E3) 2 ≠ -1; linarith
    apply (contMDiffAt_sphereNorthNormal D R q hn).congr_of_eventuallyEq
    filter_upwards [continuousAt_const.eventually_lt hcoord.continuousAt hp] with p hpp
    exact ite_eq_left hpp.le
  by_cases hm : (q.1 : E3) 2 < 0
  · have hs : q.1 ∈ sphereSouthSource := by change (q.1 : E3) 2 ≠ 1; linarith
    have hfst : ContMDiffAt SphereTimeModel (𝓡 2) ∞ Prod.fst q := contMDiffAt_fst
    have hsm := (contMDiffAt_sphereSouthCap
      (contDiff_markedCapNormal (A.b_pos.trans hR) hL k ρ) R L q.1 hs).comp q hfst
    apply hsm.congr_of_eventuallyEq
    filter_upwards [hcoord.continuousAt.eventually_lt continuousAt_const hm] with p hpm
    exact ite_eq_right (not_le.mpr hpm)
  · have hz : (q.1 : E3) 2 = 0 := le_antisymm (le_of_not_gt hp) (le_of_not_gt hm)
    exact contMDiffAt_const.congr_of_eventuallyEq
      (sphereMarkedNormal_equator_germ D hR hL hρ hsmall q hz)

theorem sphereMarkedNormal_norm {A : FlatAnnularCore}
    (D : IsometricGraphDevelopment A) {R L k ρ : ℝ}
    (hR : A.b < R) (hL : 0 < L) (hρ : 0 < ρ) (hsmall : ρ < L / 64)
    (q : SpherePoint × ℝ) : ‖sphereMarkedNormal D R L k ρ q‖ = 1 := by
  unfold sphereMarkedNormal
  split_ifs
  · exact (D.rotationNormal_isUnitSurfaceNormal q.2 (sphereNorthPlanarMap R q.1)).1
  · exact markedCapNormal_norm (A.b_pos.trans hR) hL hρ hsmall _

/-- Orthogonality uses the actual vector-valued manifold derivative. -/
theorem sphereMarkedNormal_orthogonal {A : FlatAnnularCore}
    (D : IsometricGraphDevelopment A) {R L k ρ : ℝ}
    (hR : A.b < R) (hL : 0 < L) (hρ : 0 < ρ) (hsmall : ρ < L / 64)
    (t : ℝ) (x : SpherePoint) (v : TangentSpace (𝓡 2) x) :
    inner ℝ (mvfderiv (𝓡 2) (fun y : SpherePoint =>
      sphereGraphCapFamily D (markedCapMap R A.cRight L k ρ) R L (y, t)) x v)
      (sphereMarkedNormal D R L k ρ (x, t)) = 0 := by
  have hRp := A.b_pos.trans hR
  have hslice : Tendsto (fun y : SpherePoint => (y, t)) (𝓝 x) (𝓝 (x, t)) :=
    (continuousAt_id.prodMk continuousAt_const).tendsto
  by_cases hx : 0 ≤ (x : E3) 2
  · have hnx : x ∈ sphereNorthSource := by change (x : E3) 2 ≠ -1; linarith
    have hφ := (contMDiffAt_sphereNorthPlanarMap R x hnx).mdifferentiableAt (by simp)
    have he : (fun y : SpherePoint =>
        sphereGraphCapFamily D (markedCapMap R A.cRight L k ρ) R L (y, t)) =ᶠ[𝓝 x]
        (D.rotationFamily t ∘ sphereNorthPlanarMap R) := by
      simpa only [Function.comp_def, sphereNorthFamily, sphereNorthPlanarMap] using
        (sphereGraphCapFamily_north_germ D hR
          (fun _ hy => markedCapMap_capSphereRadialMap_rim_germ (k := k)
            hRp hL hρ hsmall A.cRight hy)
          (x, t) hx).comp_tendsto hslice
    rw [sphere_mvfderiv_congr he,
      sphere_mvfderiv_comp x ((D.rotationFamily_smooth t).differentiable (by simp) _) hφ]
    simp only [sphereMarkedNormal, hx, ↓reduceIte, sphereNorthNormal,
      ContinuousLinearMap.comp_apply]
    exact (D.rotationNormal_isUnitSurfaceNormal t (sphereNorthPlanarMap R x)).2 _
  · have hsx : x ∈ sphereSouthSource := by change (x : E3) 2 ≠ 1; linarith
    let ψ : SpherePoint → PolarPoint :=
      capSphereRadialMap (capSphereRatio R L) ∘ sphereSouthChart
    have hψ : MDifferentiableAt (𝓡 2) 𝓘(ℝ, PolarPoint) ψ x :=
      ((contDiff_capSphereRadialMap _).contDiffAt.contMDiffAt.comp x
        (contMDiffAt_sphereSouthChart x hsx)).mdifferentiableAt (by simp)
    have he : (fun y : SpherePoint =>
        sphereGraphCapFamily D (markedCapMap R A.cRight L k ρ) R L (y, t)) =ᶠ[𝓝 x]
        (markedCapMap R A.cRight L k ρ ∘ ψ) := by
      simpa only [Function.comp_def, sphereSouthCap, ψ] using
        (sphereGraphCapFamily_south_germ D (markedCapMap R A.cRight L k ρ)
          R L (x, t) (lt_of_not_ge hx)).comp_tendsto hslice
    rw [sphere_mvfderiv_congr he,
      sphere_mvfderiv_comp x ((contDiff_markedCapMap hRp hL A.cRight k ρ).differentiable
        (by simp) _) hψ]
    simp only [sphereMarkedNormal, hx, ↓reduceIte, sphereSouthCap,
      ContinuousLinearMap.comp_apply]
    exact markedCapNormal_orthogonal hRp hL hρ hsmall A.cRight (ψ x) _

theorem sphereMarkedNormal_periodic {A : FlatAnnularCore}
    (D : IsometricGraphDevelopment A) (R L k ρ : ℝ) (x : SpherePoint) :
    Function.Periodic (fun t => sphereMarkedNormal D R L k ρ (x, t)) 1 := by
  intro t
  simp only [sphereMarkedNormal, sphereNorthNormal]
  split_ifs
  · exact congrFun (D.rotationNormal_periodic t) _
  · rfl

theorem sphereMarkedNormal_fixed_south {A : FlatAnnularCore}
    (D : IsometricGraphDevelopment A) (R L k ρ t : ℝ) (x : SpherePoint)
    (hx : (x : E3) 2 < 0) :
    sphereMarkedNormal D R L k ρ (x, t) = sphereMarkedNormal D R L k ρ (x, 0) := by
  simp only [sphereMarkedNormal, not_le.mpr hx, ↓reduceIte]

theorem sphereMarkedNormal_north {A : FlatAnnularCore}
    (D : IsometricGraphDevelopment A) (R L k ρ t : ℝ) (x : SpherePoint)
    (hx : 0 ≤ (x : E3) 2) :
    sphereMarkedNormal D R L k ρ (x, t) =
      D.rotationNormal t (sphereNorthPlanarMap R x) := by
  simp only [sphereMarkedNormal, hx, ↓reduceIte, sphereNorthNormal]

/-- On the closed cap, including its attaching circle, the normal is the
actual marked-cap normal in the actual radial coordinates. -/
theorem sphereMarkedNormal_south {A : FlatAnnularCore}
    (D : IsometricGraphDevelopment A) {R L k ρ : ℝ}
    (hR : A.b < R) (hL : 0 < L) (hρ : 0 < ρ) (hsmall : ρ < L / 64)
    (t : ℝ) (x : SpherePoint) (hx : (x : E3) 2 ≤ 0) :
    sphereMarkedNormal D R L k ρ (x, t) =
      markedCapNormal R L k ρ
        (capSphereRadialMap (capSphereRatio R L) (sphereSouthChart x)) := by
  by_cases hn : (x : E3) 2 < 0
  · simp only [sphereMarkedNormal, not_le.mpr hn, ↓reduceIte, sphereSouthCap]
  · have hz : (x : E3) 2 = 0 := le_antisymm hx (le_of_not_gt hn)
    exact (sphereMarkedNormal_equator_germ D hR hL hρ hsmall (x, t) hz).eq_of_nhds.trans
      (sphereSouthNormal_equator_germ (k := k) hR hL hρ hsmall (x, t) hz).eq_of_nhds.symm

theorem sphereMarkedNormal_fixed_closed_south {A : FlatAnnularCore}
    (D : IsometricGraphDevelopment A) {R L k ρ : ℝ}
    (hR : A.b < R) (hL : 0 < L) (hρ : 0 < ρ) (hsmall : ρ < L / 64)
    (t : ℝ) (x : SpherePoint) (hx : (x : E3) 2 ≤ 0) :
    sphereMarkedNormal D R L k ρ (x, t) = sphereMarkedNormal D R L k ρ (x, 0) := by
  rw [sphereMarkedNormal_south D hR hL hρ hsmall t x hx,
    sphereMarkedNormal_south D hR hL hρ hsmall 0 x hx]

/-- A single actual normal for the same marked sphere family. -/
theorem sphereMarkedNormal_smooth_unit {A : FlatAnnularCore}
    (D : IsometricGraphDevelopment A) {R L k ρ : ℝ}
    (hR : A.b < R) (hL : 0 < L) (hρ : 0 < ρ) (hsmall : ρ < L / 64) :
    ContMDiff SphereTimeModel 𝓘(ℝ, E3) ∞ (sphereMarkedNormal D R L k ρ) ∧
      ∀ t : ℝ, ∀ x : SpherePoint, ‖sphereMarkedNormal D R L k ρ (x, t)‖ = 1 ∧
        ∀ v : TangentSpace (𝓡 2) x,
          inner ℝ (mvfderiv (𝓡 2) (fun y : SpherePoint =>
            sphereGraphCapFamily D (markedCapMap R A.cRight L k ρ) R L (y, t)) x v)
            (sphereMarkedNormal D R L k ρ (x, t)) = 0 :=
  ⟨contMDiff_sphereMarkedNormal D hR hL hρ hsmall,
    fun t x => ⟨sphereMarkedNormal_norm D hR hL hρ hsmall (x, t),
      sphereMarkedNormal_orthogonal D hR hL hρ hsmall t x⟩⟩

end ContinuousFlexibility
