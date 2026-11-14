module

public import ContinuousFlexibility.Geometry.SphereShapeCurvature
public import ContinuousFlexibility.Geometry.SphereArea

/-!
# The actual signed mean-curvature integral of the constructed sphere

The scalar field is half the trace of the genuine tangent shape operator.
Its ambient representative agrees on the embedded image, whose normalized
Hausdorff measure is used for integration. The graph moves by a true ambient
rotation and the cap is fixed. Identification of the constructed normal as
outward belongs to the enclosed-region construction.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility

open Set Filter MeasureTheory
open scoped ContDiff Manifold Topology

local notation "SpherePoint" => {v : E3 // v ∈ Metric.sphere (0 : E3) 1}

local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp [E3]⟩

set_option backward.isDefEq.respectTransparency false

/-- A scalar on a sphere is represented on its actual image. Off the image
the value is zero; only its restriction to the image is integrated. -/
def sphereImageScalar (F : SpherePoint → E3) (m : SpherePoint → ℝ) : E3 → ℝ :=
  Function.extend F m (fun _ => 0)

theorem sphereImageScalar_apply {F : SpherePoint → E3} (hi : Function.Injective F)
    (m : SpherePoint → ℝ) (x : SpherePoint) : sphereImageScalar F m (F x) = m x :=
  hi.extend_apply m (fun _ => 0) x

theorem integrable_sphereImageScalar {F : SpherePoint → E3} {m : SpherePoint → ℝ}
    (he : Topology.IsEmbedding F) (hm : Continuous m)
    (hfinite : (Measure.euclideanHausdorffMeasure 2 : Measure E3) (Set.range F) < ⊤) :
    Integrable (sphereImageScalar F m)
      ((Measure.euclideanHausdorffMeasure 2 : Measure E3).restrict (Set.range F)) := by
  have hpull : sphereImageScalar F m ∘ F = m :=
    Function.extend_comp he.injective m (fun _ => 0)
  apply integrable_surfaceArea_of_continuous_comp he _ hfinite
  rw [hpull]
  exact hm

/-- Any actual ambient representative of the same sphere scalar has the
same image integral; its behavior away from the image is immaterial. -/
theorem integrable_and_integral_eq_sphereImageScalar
    {F : SpherePoint → E3} {m : SpherePoint → ℝ} {h : E3 → ℝ}
    (he : Topology.IsEmbedding F) (hm : Continuous m)
    (hfinite : (Measure.euclideanHausdorffMeasure 2 : Measure E3) (Set.range F) < ⊤)
    (hh : ∀ x : SpherePoint, h (F x) = m x) :
    Integrable h ((Measure.euclideanHausdorffMeasure 2 : Measure E3).restrict (Set.range F)) ∧
      (∫ z, h z ∂(Measure.euclideanHausdorffMeasure 2 : Measure E3).restrict (Set.range F)) =
        ∫ z, sphereImageScalar F m z
          ∂(Measure.euclideanHausdorffMeasure 2 : Measure E3).restrict (Set.range F) := by
  have heq : h =ᵐ[(Measure.euclideanHausdorffMeasure 2 : Measure E3).restrict (Set.range F)]
      sphereImageScalar F m := by
    apply ae_restrict_of_forall_mem (isCompact_range he.continuous).measurableSet
    rintro z ⟨x, rfl⟩
    rw [sphereImageScalar_apply he.injective m x]
    exact hh x
  exact ⟨(integrable_sphereImageScalar he hm hfinite).congr heq.symm, integral_congr_ae heq⟩

/-- Injectivity of the genuine immersion differential makes the actual
Weingarten endomorphism unique. This identifies an independently constructed
shape field once its full normal function has been identified. -/
theorem sphereShapeOperator_unique {F N : SpherePoint → E3}
    (hN : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ N)
    (hi : ∀ x, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, E3) F x))
    (hu : ∀ x, ‖N x‖ = 1)
    (ho : ∀ x v, inner ℝ (mvfderiv (𝓡 2) F x v) (N x) = 0)
    (x : SpherePoint) (S : TangentSpace (𝓡 2) x →L[ℝ] TangentSpace (𝓡 2) x)
    (hS : ∀ v, mvfderiv (𝓡 2) F x (S v) = -mvfderiv (𝓡 2) N x v) :
    S = sphereShapeOperator F N x := by
  apply ContinuousLinearMap.ext
  intro v
  apply (NormedSpace.fromTangentSpace (𝕜 := ℝ) (F x)).injective.comp (hi x)
  exact (hS v).trans (sphereShapeOperator_weingarten hN hi hu ho x v).symm

theorem sphereMeanCurvature_eq_trace_of_weingarten {F N : SpherePoint → E3}
    (hN : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ N)
    (hi : ∀ x, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, E3) F x))
    (hu : ∀ x, ‖N x‖ = 1)
    (ho : ∀ x v, inner ℝ (mvfderiv (𝓡 2) F x v) (N x) = 0)
    (x : SpherePoint) (S : TangentSpace (𝓡 2) x →L[ℝ] TangentSpace (𝓡 2) x)
    (hS : ∀ v, mvfderiv (𝓡 2) F x (S v) = -mvfderiv (𝓡 2) N x v) :
    sphereMeanCurvature F N x = LinearMap.trace ℝ (TangentSpace (𝓡 2) x) S.toLinearMap / 2 := by
  change LinearMap.trace ℝ (TangentSpace (𝓡 2) x)
      (sphereShapeOperator F N x).toLinearMap / 2 = _
  rw [sphereShapeOperator_unique hN hi hu ho x S hS]

def IsometricGraphDevelopment.markedSpherePhaseMap {A : FlatAnnularCore}
    (D : IsometricGraphDevelopment A) (R L k ρ t : ℝ) (x : SpherePoint) : E3 :=
  sphereGraphCapFamily D (markedCapMap R A.cRight L k ρ) R L (x, t)

def IsometricGraphDevelopment.markedSpherePhaseNormal {A : FlatAnnularCore}
    (D : IsometricGraphDevelopment A) (R L k ρ t : ℝ) (x : SpherePoint) : E3 :=
  sphereMarkedNormal D R L k ρ (x, t)

def IsometricGraphDevelopment.markedSphereMeanCurvature {A : FlatAnnularCore}
    (D : IsometricGraphDevelopment A) (R L k ρ t : ℝ) : SpherePoint → ℝ :=
  sphereMeanCurvature (D.markedSpherePhaseMap R L k ρ t)
    (D.markedSpherePhaseNormal R L k ρ t)

def IsometricGraphDevelopment.markedSphereAmbientMean {A : FlatAnnularCore}
    (D : IsometricGraphDevelopment A) (R L k ρ t : ℝ) : E3 → ℝ :=
  sphereImageScalar (D.markedSpherePhaseMap R L k ρ t)
    (D.markedSphereMeanCurvature R L k ρ t)

theorem IsometricGraphDevelopment.contMDiff_markedSpherePhaseMap {A : FlatAnnularCore}
    (D : IsometricGraphDevelopment A) {R L k ρ : ℝ}
    (hR : A.b < R) (hL : 0 < L) (hρ : 0 < ρ) (hsmall : ρ < L / 64) (t : ℝ) :
    ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ (D.markedSpherePhaseMap R L k ρ t) :=
  D.markedSphereFamily_slice_contMDiff hR hL hρ hsmall t

theorem IsometricGraphDevelopment.contMDiff_markedSpherePhaseNormal {A : FlatAnnularCore}
    (D : IsometricGraphDevelopment A) {R L k ρ : ℝ}
    (hR : A.b < R) (hL : 0 < L) (hρ : 0 < ρ) (hsmall : ρ < L / 64) (t : ℝ) :
    ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ (D.markedSpherePhaseNormal R L k ρ t) := by
  have hs : ContMDiff (𝓡 2) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞
      (fun x : SpherePoint => (x, t)) := contMDiff_id.prodMk contMDiff_const
  exact (contMDiff_sphereMarkedNormal D hR hL hρ hsmall).comp hs

theorem IsometricGraphDevelopment.markedSpherePhaseMap_isEmbedding {A : FlatAnnularCore}
    (D : IsometricGraphDevelopment A) {R L k ρ t : ℝ}
    (hR : A.b < R) (hL : 0 < L) (hk : 0 ≤ k) (hρ : 0 < ρ) (hsmall : ρ < L / 64)
    (hmeet : graphPhaseDiskImage D R t ∩ capDiskImage R A.cRight L =
      capAttachingRim R A.cRight) :
    Topology.IsEmbedding (D.markedSpherePhaseMap R L k ρ t) := by
  exact isEmbedding_sphereGraphCapFamily D
    (C := markedCapMap R A.cRight L k ρ) (t := t) hR hL
    (contDiff_markedCapMap (A.b_pos.trans hR) hL A.cRight k ρ)
    (fun _ hy => markedCapMap_capSphereRadialMap_rim_germ (k := k)
      (A.b_pos.trans hR) hL hρ hsmall A.cRight hy)
    (markedCapMap_injOn (A.b_pos.trans hR) hL hk hρ hsmall A.cRight)
    (fun _ hy => markedCap_boundary (A.b_pos.trans hR) hL hρ hsmall A.cRight hy)
    (D.marked_cap_meeting_subset hR hL hρ hsmall hmeet)

theorem IsometricGraphDevelopment.contMDiff_markedSphereMeanCurvature
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) {R L k ρ : ℝ}
    (hR : A.b < R) (hL : 0 < L) (hk : 0 ≤ k) (hρ : 0 < ρ) (hsmall : ρ < L / 64) (t : ℝ) :
    ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (D.markedSphereMeanCurvature R L k ρ t) :=
  contMDiff_sphereMeanCurvature
    (D.contMDiff_markedSpherePhaseMap hR hL hρ hsmall t)
    (D.contMDiff_markedSpherePhaseNormal hR hL hρ hsmall t)
    (D.markedSphereFamily_mfderiv_injective hR hL hk hρ hsmall t)
    (fun x => sphereMarkedNormal_norm D hR hL hρ hsmall (x, t))
    (sphereMarkedNormal_orthogonal D hR hL hρ hsmall t)

private theorem meanIntegral_scaling_injective {R : ℝ} (hR : 0 < R) (y : PolarPoint) :
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

/-- The northern sphere chart computes the physical moving graph's signed mean. -/
theorem IsometricGraphDevelopment.markedSphereMeanCurvature_north
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) {R L k ρ : ℝ}
    (hR : A.b < R) (hL : 0 < L) (hk : 0 ≤ k) (hρ : 0 < ρ) (hsmall : ρ < L / 64)
    (t : ℝ) (x : SpherePoint) (hx : 0 ≤ (x : E3) 2) :
    D.markedSphereMeanCurvature R L k ρ t x =
      surfaceMeanCurvature (D.rotationFamily t)
        (D.rotationNormal t (R • sphereNorthChart x)) (R • sphereNorthChart x) := by
  have hn : x ∈ sphereNorthSource := by change (x : E3) 2 ≠ -1; linarith
  change sphereMeanCurvature (D.markedSpherePhaseMap R L k ρ t)
    (D.markedSpherePhaseNormal R L k ρ t) x = _
  rw [sphereMeanCurvature_north
    (D.contMDiff_markedSpherePhaseMap hR hL hρ hsmall t)
    (D.contMDiff_markedSpherePhaseNormal hR hL hρ hsmall t)
    (D.markedSphereFamily_mfderiv_injective hR hL hk hρ hsmall t)
    (fun y => sphereMarkedNormal_norm D hR hL hρ hsmall (y, t))
    (sphereMarkedNormal_orthogonal D hR hL hρ hsmall t) x hn]
  change surfaceMeanCurvature (sphereNorthSurfaceChart (fun y =>
    sphereGraphCapFamily D (markedCapMap R A.cRight L k ρ) R L (y, t)))
      (sphereMarkedNormal D R L k ρ (x, t)) (sphereNorthChart x) = _
  rw [sphereMarkedNormal_north D R L k ρ t x hx, sphereNorthPlanarMap,
    surfaceMeanCurvature_congr_germ
      (markedSphereNorthSurfaceChart_germ D hR hL hρ hsmall t x hx)]
  have hscale : ContDiff ℝ ∞ (fun y : PolarPoint => R • y) := contDiff_const_smul R
  exact surfaceMeanCurvature_comp
    ((D.rotationFamily_smooth t).of_le (by simp : (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω))).contDiffAt
    (hscale.of_le (by simp : (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω))).contDiffAt
    (D.rotationNormal_isUnitSurfaceNormal t (R • sphereNorthChart x))
    (D.rotationFamily_immersion t (R • sphereNorthChart x))
    (meanIntegral_scaling_injective (A.b_pos.trans hR) _)

/-- The complementary cap has the same actual signed mean at every phase,
including its attaching circle. -/
theorem IsometricGraphDevelopment.markedSphereMeanCurvature_south
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) {R L k ρ : ℝ}
    (hR : A.b < R) (hL : 0 < L) (hk : 0 ≤ k) (hρ : 0 < ρ) (hsmall : ρ < L / 64)
    (t : ℝ) (x : SpherePoint) (hx : (x : E3) 2 ≤ 0) :
    D.markedSphereMeanCurvature R L k ρ t x =
      surfaceMeanCurvature (markedCapMap R A.cRight L k ρ)
        (markedCapNormal R L k ρ
          (capSphereRadialMap (capSphereRatio R L) (sphereSouthChart x)))
        (capSphereRadialMap (capSphereRatio R L) (sphereSouthChart x)) := by
  have hs : x ∈ sphereSouthSource := by change (x : E3) 2 ≠ 1; linarith
  change sphereMeanCurvature (D.markedSpherePhaseMap R L k ρ t)
    (D.markedSpherePhaseNormal R L k ρ t) x = _
  rw [sphereMeanCurvature_south
    (D.contMDiff_markedSpherePhaseMap hR hL hρ hsmall t)
    (D.contMDiff_markedSpherePhaseNormal hR hL hρ hsmall t)
    (D.markedSphereFamily_mfderiv_injective hR hL hk hρ hsmall t)
    (fun y => sphereMarkedNormal_norm D hR hL hρ hsmall (y, t))
    (sphereMarkedNormal_orthogonal D hR hL hρ hsmall t) x hs]
  exact markedSphereSouthSurfaceChart_mean D hR hL hk hρ hsmall t x hx

theorem IsometricGraphDevelopment.markedSphereAmbientMean_on_image
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) {R L k ρ t : ℝ}
    (hR : A.b < R) (hL : 0 < L) (hk : 0 ≤ k) (hρ : 0 < ρ) (hsmall : ρ < L / 64)
    (hmeet : graphPhaseDiskImage D R t ∩ capDiskImage R A.cRight L =
      capAttachingRim R A.cRight) (x : SpherePoint) :
    D.markedSphereAmbientMean R L k ρ t (D.markedSpherePhaseMap R L k ρ t x) =
      D.markedSphereMeanCurvature R L k ρ t x :=
  sphereImageScalar_apply
    (D.markedSpherePhaseMap_isEmbedding hR hL hk hρ hsmall hmeet).injective _ x

theorem IsometricGraphDevelopment.integrable_markedSphereAmbientMean
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) {R L k ρ : ℝ}
    (hR : A.b < R) (hL : 0 < L) (hk : 0 ≤ k) (hρ : 0 < ρ) (hsmall : ρ < L / 64)
    (t : ℝ)
    (hmeet : graphPhaseDiskImage D R t ∩ capDiskImage R A.cRight L =
      capAttachingRim R A.cRight) :
    Integrable (D.markedSphereAmbientMean R L k ρ t)
      ((Measure.euclideanHausdorffMeasure 2 : Measure E3).restrict
        (Set.range (D.markedSpherePhaseMap R L k ρ t))) :=
  integrable_sphereImageScalar
    (D.markedSpherePhaseMap_isEmbedding hR hL hk hρ hsmall hmeet)
    (D.contMDiff_markedSphereMeanCurvature hR hL hk hρ hsmall t).continuous
    (D.markedSphereFamily_area_lt_top hR hL hρ hsmall t)

/-- The ambient representative at every point of the actual graph image is
the mean curvature computed from that physical graph and its transported normal. -/
theorem IsometricGraphDevelopment.markedSphereAmbientMean_on_graph
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) {R L k ρ t : ℝ}
    (hR : A.b < R) (hL : 0 < L) (hk : 0 ≤ k) (hρ : 0 < ρ) (hsmall : ρ < L / 64)
    (hmeet : graphPhaseDiskImage D R t ∩ capDiskImage R A.cRight L =
      capAttachingRim R A.cRight) (p : PolarPoint) (hp : cartesianRadius p ≤ R) :
    D.markedSphereAmbientMean R L k ρ t (D.rotationFamily t p) =
      surfaceMeanCurvature (D.rotationFamily t) (D.rotationNormal t p) p := by
  have hRp := A.b_pos.trans hR
  let u : PolarPoint := R⁻¹ • p
  let x : SpherePoint := sphereNorthInverse u
  have hu : cartesianRadius u ≤ 1 := by
    dsimp only [u]
    rw [capDisk_radius_smul, abs_of_pos (inv_pos.mpr hRp)]
    exact (inv_mul_le_iff₀ hRp).mpr (by simpa using hp)
  have hx : 0 ≤ (x : E3) 2 := by
    have hr := sphereNorthChart_radius_le_one_iff
      (sphereNorthInverse u) (sphereNorthInverse_source u)
    rw [sphereNorthChart_inverse] at hr
    exact hr.mp hu
  have hpos : R • sphereNorthChart x = p := by
    change R • sphereNorthChart (sphereNorthInverse u) = p
    rw [sphereNorthChart_inverse]
    dsimp only [u]
    rw [smul_smul, mul_inv_cancel₀ hRp.ne', one_smul]
  have hvalue : D.markedSpherePhaseMap R L k ρ t x = D.rotationFamily t p := by
    change sphereGraphCapFamily D (markedCapMap R A.cRight L k ρ) R L (x, t) = _
    rw [sphereGraphCapFamily_north D (markedCapMap R A.cRight L k ρ) R L t x hx, hpos]
  calc
    D.markedSphereAmbientMean R L k ρ t (D.rotationFamily t p) =
        D.markedSphereAmbientMean R L k ρ t (D.markedSpherePhaseMap R L k ρ t x) :=
      congrArg (D.markedSphereAmbientMean R L k ρ t) hvalue.symm
    _ = D.markedSphereMeanCurvature R L k ρ t x :=
      D.markedSphereAmbientMean_on_image hR hL hk hρ hsmall hmeet x
    _ = surfaceMeanCurvature (D.rotationFamily t) (D.rotationNormal t p) p := by
      rw [D.markedSphereMeanCurvature_north hR hL hk hρ hsmall t x hx, hpos]

/-- The fixed cap has one fixed actual ambient mean-curvature integrand.
The radial chart's actual disk surjectivity also covers its attaching circle. -/
theorem IsometricGraphDevelopment.markedSphereAmbientMean_on_cap
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) {R L k ρ t : ℝ}
    (hR : A.b < R) (hL : 0 < L) (hk : 0 ≤ k) (hρ : 0 < ρ) (hsmall : ρ < L / 64)
    (hmeet : graphPhaseDiskImage D R t ∩ capDiskImage R A.cRight L =
      capAttachingRim R A.cRight) (y : PolarPoint) (hy : cartesianRadius y ≤ 1) :
    D.markedSphereAmbientMean R L k ρ t (markedCapMap R A.cRight L k ρ y) =
      surfaceMeanCurvature (markedCapMap R A.cRight L k ρ) (markedCapNormal R L k ρ y) y := by
  obtain ⟨u, hu, heu⟩ := capSphereRadialMap_surjOn_disk (capSphereRatio R L) hy
  let x : SpherePoint := sphereSouthInverse u
  have hx : (x : E3) 2 ≤ 0 := by
    have hr := sphereSouthChart_radius_le_one_iff
      (sphereSouthInverse u) (sphereSouthInverse_source u)
    rw [sphereSouthChart_inverse] at hr
    exact hr.mp hu
  have hpos : capSphereRadialMap (capSphereRatio R L) (sphereSouthChart x) = y := by
    change capSphereRadialMap (capSphereRatio R L) (sphereSouthChart (sphereSouthInverse u)) = y
    rw [sphereSouthChart_inverse]
    exact heu
  have hvalue : D.markedSpherePhaseMap R L k ρ t x = markedCapMap R A.cRight L k ρ y := by
    change sphereGraphCapFamily D (markedCapMap R A.cRight L k ρ) R L (x, t) = _
    rw [sphereGraphCapFamily_south D (C := markedCapMap R A.cRight L k ρ) hR
      (fun _ hz => markedCapMap_capSphereRadialMap_rim_germ (k := k)
        (A.b_pos.trans hR) hL hρ hsmall A.cRight hz) x hx t]
    change markedCapMap R A.cRight L k ρ
      (capSphereRadialMap (capSphereRatio R L) (sphereSouthChart x)) = _
    rw [hpos]
  calc
    D.markedSphereAmbientMean R L k ρ t (markedCapMap R A.cRight L k ρ y) =
        D.markedSphereAmbientMean R L k ρ t (D.markedSpherePhaseMap R L k ρ t x) :=
      congrArg (D.markedSphereAmbientMean R L k ρ t) hvalue.symm
    _ = D.markedSphereMeanCurvature R L k ρ t x :=
      D.markedSphereAmbientMean_on_image hR hL hk hρ hsmall hmeet x
    _ = surfaceMeanCurvature (markedCapMap R A.cRight L k ρ) (markedCapNormal R L k ρ y) y := by
      rw [D.markedSphereMeanCurvature_south hR hL hk hρ hsmall t x hx, hpos]

/-- The actual image integral of half the trace of the actual shape operator. -/
def IsometricGraphDevelopment.markedSphereTotalMean {A : FlatAnnularCore}
    (D : IsometricGraphDevelopment A) (R L k ρ t : ℝ) : ℝ :=
  ∫ z, D.markedSphereAmbientMean R L k ρ t z
    ∂(Measure.euclideanHausdorffMeasure 2 : Measure E3).restrict
      (Set.range (D.markedSpherePhaseMap R L k ρ t))

/-- The signed total mean is phase independent for the same constructed
normal, length, marker, and sphere family. -/
theorem IsometricGraphDevelopment.markedSphereTotalMean_invariant
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) {R L k ρ : ℝ}
    (hR : A.b < R) (hL : 0 < L) (hk : 0 ≤ k) (hρ : 0 < ρ) (hsmall : ρ < L / 64)
    (hmeet : ∀ s : ℝ, graphPhaseDiskImage D R s ∩ capDiskImage R A.cRight L =
      capAttachingRim R A.cRight) (t : ℝ) :
    D.markedSphereTotalMean R L k ρ t = D.markedSphereTotalMean R L k ρ 0 := by
  unfold IsometricGraphDevelopment.markedSphereTotalMean
  apply D.markedSphereFamily_integral_invariant hR hL hρ hsmall hmeet t
    (D.integrable_markedSphereAmbientMean hR hL hk hρ hsmall 0 (hmeet 0))
    (D.integrable_markedSphereAmbientMean hR hL hk hρ hsmall t (hmeet t))
  · rintro z ⟨p, hp, rfl⟩
    change cartesianRadius p ≤ R at hp
    let u : PolarPoint := planarRotation (-t) p
    have hu : cartesianRadius u ≤ R := by
      simpa only [u, cartesianRadius_planarRotation] using hp
    have hrot : planarRotation t u = p := planarRotation_neg_cancel t p
    have hv : axialRotation (-t) (D.map p) = D.rotationFamily t u := by
      rw [D.rotationFamily_eq_axialRotation t u, hrot]
    rw [hv, D.markedSphereAmbientMean_on_graph hR hL hk hρ hsmall (hmeet t) u hu,
      D.rotationFamily_meanCurvature, hrot]
    have hzero := D.markedSphereAmbientMean_on_graph hR hL hk hρ hsmall (hmeet 0) p hp
    have hf0 : D.rotationFamily 0 = D.map := funext D.rotationFamily_zero
    simpa only [hf0, D.rotationNormal_zero] using hzero.symm
  · rintro z ⟨y, hy, rfl⟩
    change cartesianRadius y ≤ 1 at hy
    rw [D.markedSphereAmbientMean_on_cap hR hL hk hρ hsmall (hmeet t) y hy,
      D.markedSphereAmbientMean_on_cap hR hL hk hρ hsmall (hmeet 0) y hy]

/-- A representative supplied by another geometric construction is
integrable and has the actual constructed total mean whenever its values
on this same embedded image are the same actual signed mean. -/
theorem IsometricGraphDevelopment.markedSphereMean_integral_eq_of_identification
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) {R L k ρ : ℝ}
    (hR : A.b < R) (hL : 0 < L) (hk : 0 ≤ k) (hρ : 0 < ρ) (hsmall : ρ < L / 64)
    (t : ℝ)
    (hmeet : graphPhaseDiskImage D R t ∩ capDiskImage R A.cRight L =
      capAttachingRim R A.cRight) {h : E3 → ℝ}
    (hh : ∀ x : SpherePoint, h (D.markedSpherePhaseMap R L k ρ t x) =
      D.markedSphereMeanCurvature R L k ρ t x) :
    Integrable h ((Measure.euclideanHausdorffMeasure 2 : Measure E3).restrict
      (Set.range (D.markedSpherePhaseMap R L k ρ t))) ∧
      (∫ z, h z ∂(Measure.euclideanHausdorffMeasure 2 : Measure E3).restrict
        (Set.range (D.markedSpherePhaseMap R L k ρ t))) = D.markedSphereTotalMean R L k ρ t :=
  integrable_and_integral_eq_sphereImageScalar
    (D.markedSpherePhaseMap_isEmbedding hR hL hk hρ hsmall hmeet)
    (D.contMDiff_markedSphereMeanCurvature hR hL hk hρ hsmall t).continuous
    (D.markedSphereFamily_area_lt_top hR hL hρ hsmall t) hh

/-- Integral invariance is independent of the chosen ambient representative.
Identifying another normal or another enclosed region remains a separate step. -/
theorem IsometricGraphDevelopment.markedSphereMean_integral_invariant_of_identification
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) {R L k ρ : ℝ}
    (hR : A.b < R) (hL : 0 < L) (hk : 0 ≤ k) (hρ : 0 < ρ) (hsmall : ρ < L / 64)
    (hmeet : ∀ t : ℝ, graphPhaseDiskImage D R t ∩ capDiskImage R A.cRight L =
      capAttachingRim R A.cRight) (H : ℝ → E3 → ℝ)
    (hH : ∀ t : ℝ, ∀ x : SpherePoint, H t (D.markedSpherePhaseMap R L k ρ t x) =
      D.markedSphereMeanCurvature R L k ρ t x) :
    (∀ t : ℝ, Integrable (H t) ((Measure.euclideanHausdorffMeasure 2 : Measure E3).restrict
      (Set.range (D.markedSpherePhaseMap R L k ρ t)))) ∧
      ∀ t : ℝ,
        (∫ z, H t z ∂(Measure.euclideanHausdorffMeasure 2 : Measure E3).restrict
          (Set.range (D.markedSpherePhaseMap R L k ρ t))) =
        ∫ z, H 0 z ∂(Measure.euclideanHausdorffMeasure 2 : Measure E3).restrict
          (Set.range (D.markedSpherePhaseMap R L k ρ 0)) := by
  have hrep (t : ℝ) := D.markedSphereMean_integral_eq_of_identification
    (h := H t) hR hL hk hρ hsmall t (hmeet t) (hH t)
  refine ⟨fun t => (hrep t).1, ?_⟩
  intro t
  exact (hrep t).2.trans
    ((D.markedSphereTotalMean_invariant hR hL hk hρ hsmall hmeet t).trans (hrep 0).2.symm)

/-- The actual cap attachment supplies one length for all these signed
integrals; the all-phase intersection witness is retained for later assembly. -/
theorem IsometricGraphDevelopment.exists_markedSphereTotalMean
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) {R : ℝ} (hR : A.b < R) :
    ∃ L : ℝ, 0 < L ∧
      (∀ t : ℝ, graphPhaseDiskImage D R t ∩ capDiskImage R A.cRight L =
        capAttachingRim R A.cRight) ∧
      ∀ k ρ : ℝ, 0 ≤ k → 0 < ρ → ρ < L / 64 →
        (∀ t : ℝ, Integrable (D.markedSphereAmbientMean R L k ρ t)
          ((Measure.euclideanHausdorffMeasure 2 : Measure E3).restrict
            (Set.range (D.markedSpherePhaseMap R L k ρ t)))) ∧
        (∀ t : ℝ, D.markedSphereTotalMean R L k ρ t = D.markedSphereTotalMean R L k ρ 0) := by
  obtain ⟨L, hL, hmeet, _⟩ := D.exists_fixed_cap_attachment hR
  refine ⟨L, hL, hmeet, ?_⟩
  intro k ρ hk hρ hsmall
  exact ⟨fun t => D.integrable_markedSphereAmbientMean hR hL hk hρ hsmall t (hmeet t),
    D.markedSphereTotalMean_invariant hR hL hk hρ hsmall hmeet⟩

end ContinuousFlexibility
