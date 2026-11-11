import ContinuousFlexibility.Geometry.SphereCongruenceCurvature
import ContinuousFlexibility.Geometry.MarkerStabilizer
import ContinuousFlexibility.Geometry.MarkerFrame

/-!
# Actual marker constraints on closed sphere congruences

The marker is the constructed whole-sphere curvature maximum. Its fixed point
and normal constraints are conclusions of genuine image congruence, rather than
new preservation hypotheses. The nonzero signed mean curvature distinguishes
the two actual unit normals at that fixed point.
-/

noncomputable section

namespace ContinuousFlexibility

open Set Filter Function
open scoped ContDiff Manifold Topology

local notation "SpherePoint" => {v : E3 // v ∈ Metric.sphere (0 : E3) 1}
local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp [E3]⟩

set_option backward.isDefEq.respectTransparency false

def IsometricGraphDevelopment.markedSphereSlice {B : FlatAnnularCore}
    (D : IsometricGraphDevelopment B) (R L k ρ t : ℝ) : SpherePoint → E3 :=
  fun x => sphereGraphCapFamily D (markedCapMap R B.cRight L k ρ) R L (x, t)

def IsometricGraphDevelopment.markedSphereMarker {B : FlatAnnularCore}
    (_D : IsometricGraphDevelopment B) (R L k ρ : ℝ) : E3 :=
  markedCapMap R B.cRight L k ρ (markedCapCenterParameter R L)

/-- The actual unique peak identifies the physical marker under every ambient
image congruence, including reflections. -/
theorem IsometricGraphDevelopment.markedSphere_congruence_fixes_marker_of_peak
    {B : FlatAnnularCore} (D : IsometricGraphDevelopment B) {R L k ρ : ℝ}
    (hR : B.b < R) (hL : 0 < L) (hk : 0 ≤ k) (hρ : 0 < ρ) (hsmall : ρ < L / 64)
    (hpeak : ∀ t : ℝ, ∀ x : SpherePoint,
      D.markedSphereGaussianCurvature R L k ρ t x ≤ 2 * k ^ 2 ∧
      (D.markedSphereGaussianCurvature R L k ρ t x = 2 * k ^ 2 ↔
        x = markedSphereCenterParameter (B.b_pos.trans hR) hL))
    (A : E3 ≃ᵃⁱ[ℝ] E3) {s t : ℝ}
    (hGE : Topology.IsEmbedding (D.markedSphereSlice R L k ρ t))
    (himage : A '' range (D.markedSphereSlice R L k ρ s) =
      range (D.markedSphereSlice R L k ρ t)) :
    A (D.markedSphereMarker R L k ρ) = D.markedSphereMarker R L k ρ := by
  let m := markedSphereCenterParameter (B.b_pos.trans hR) hL
  have hfs : D.markedSphereSlice R L k ρ s m = D.markedSphereMarker R L k ρ :=
    D.markedSphereCenter_image hR hL k ρ s
  have hft : D.markedSphereSlice R L k ρ t m = D.markedSphereMarker R L k ρ :=
    D.markedSphereCenter_image hR hL k ρ t
  have hmem : A (D.markedSphereSlice R L k ρ s m) ∈
      range (D.markedSphereSlice R L k ρ t) := by
    rw [← himage]
    exact ⟨D.markedSphereSlice R L k ρ s m, ⟨m, rfl⟩, rfl⟩
  obtain ⟨y, hy⟩ := hmem
  have hK := D.markedSphereGaussianCurvature_congruence hR hL hk hρ hsmall
    A hGE himage hy.symm
  have hKm : D.markedSphereGaussianCurvature R L k ρ s m = 2 * k ^ 2 :=
    (hpeak s m).2.mpr rfl
  have hym : y = m := (hpeak t y).2.mp (hK.symm.trans hKm)
  calc
    A (D.markedSphereMarker R L k ρ) = A (D.markedSphereSlice R L k ρ s m) :=
      congrArg A hfs.symm
    _ = D.markedSphereSlice R L k ρ t y := hy.symm
    _ = D.markedSphereMarker R L k ρ := by rw [hym]; exact hft

/-- Signed mean curvature transports with the actually transported unit normal. -/
theorem meanCurvature_of_affine_surface_germ
    (A : E3 ≃ᵃⁱ[ℝ] E3) {f g : PolarPoint → E3} {H : PolarPoint → PolarPoint}
    {a : PolarPoint} {N : E3}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hH : ContDiffAt ℝ ∞ H a)
    (heq : (fun q => A (f q)) =ᶠ[𝓝 a] g ∘ H)
    (hbij : Bijective (fderiv ℝ H a))
    (hgi : Injective (fderiv ℝ g (H a))) (hN : IsUnitSurfaceNormal f a N) :
    surfaceMeanCurvature f N a =
      surfaceMeanCurvature g (A.linearIsometryEquiv N) (H a) := by
  have htrans := hN.of_affine_reparametrization A
    (hf.differentiable (by simp) a) (hg.differentiable (by simp) (H a))
    (hH.differentiableAt (by simp)) heq hbij.surjective
  rw [← surfaceMeanCurvature_affineIsometry A hf N a, surfaceMeanCurvature_congr_germ heq]
  exact surfaceMeanCurvature_comp
    (hg.of_le (by simp : (2 : ℕ∞ω) ≤ ∞)).contDiffAt
    (hH.of_le (by simp : (2 : ℕ∞ω) ≤ ∞)) htrans hgi hbij.injective

/-- A nonzero common signed mean curvature excludes the negative normal sign.
The sign alternative itself is derived from the actual tangent planes. -/
theorem normal_fixed_of_affine_surface_germ
    (A : E3 ≃ᵃⁱ[ℝ] E3) {f g : PolarPoint → E3} {H : PolarPoint → PolarPoint}
    {a : PolarPoint} {N : E3}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hH : ContDiffAt ℝ ∞ H a)
    (heq : (fun q => A (f q)) =ᶠ[𝓝 a] g ∘ H)
    (hbij : Bijective (fderiv ℝ H a))
    (hgi : Injective (fderiv ℝ g (H a)))
    (hN : IsUnitSurfaceNormal f a N) (hM : IsUnitSurfaceNormal g (H a) N)
    (hmean : surfaceMeanCurvature f N a = surfaceMeanCurvature g N (H a))
    (hnonzero : surfaceMeanCurvature g N (H a) ≠ 0) : A.linearIsometryEquiv N = N := by
  rcases normal_sign_of_affine_surface_germ A hf hg hH heq hbij hgi hN hM with h | h
  · exact h
  · have hm := meanCurvature_of_affine_surface_germ A hf hg hH heq hbij hgi hN
    rw [h, surfaceMeanCurvature_neg_normal] at hm
    have hz : surfaceMeanCurvature g N (H a) = 0 := by linarith
    exact (hnonzero hz).elim

theorem IsometricGraphDevelopment.markedSphereCanonicalCenter_mean
    {B : FlatAnnularCore} (D : IsometricGraphDevelopment B) {R L k ρ : ℝ}
    (hR : B.b < R) (hL : 0 < L) (hk : 0 ≤ k) (hρ : 0 < ρ) (hsmall : ρ < L / 64)
    (t : ℝ) :
    surfaceMeanCurvature
      (sphereCanonicalSurfaceChart (D.markedSphereSlice R L k ρ t)
        (markedSphereCenterParameter (B.b_pos.trans hR) hL)) (e3Basis 2)
      (sphereCanonicalCoordinates (markedSphereCenterParameter (B.b_pos.trans hR) hL)
        (markedSphereCenterParameter (B.b_pos.trans hR) hL)) = -3 * k / 2 := by
  have hs := markedSphereCenterParameter_south (B.b_pos.trans hR) hL
  have h := D.markedSphereCenter_mean hR hL hk hρ hsmall t
  rw [D.markedSphereCenter_normal hR hL hρ hsmall t] at h
  unfold sphereCanonicalSurfaceChart sphereCanonicalCoordinates
  rw [ite_eq_right (not_le.mpr hs)]
  change surfaceMeanCurvature
    (sphereSouthSurfaceChart (D.markedSphereSlice R L k ρ t)) (e3Basis 2)
    (sphereSouthChart (markedSphereCenterParameter (B.b_pos.trans hR) hL)) = -3 * k / 2
  rw [show D.markedSphereSlice R L k ρ t = (fun y : SpherePoint =>
    sphereGraphCapFamily D (markedCapMap R B.cRight L k ρ) R L (y, t)) from rfl]
  exact h

/-- No normal-preservation premise: the actual marker curvature forces it. -/
theorem IsometricGraphDevelopment.markedSphere_congruence_fixes_normal_of_peak
    {B : FlatAnnularCore} (D : IsometricGraphDevelopment B) {R L k ρ : ℝ}
    (hR : B.b < R) (hL : 0 < L) (hk : 0 < k) (hρ : 0 < ρ) (hsmall : ρ < L / 64)
    (hpeak : ∀ t : ℝ, ∀ x : SpherePoint,
      D.markedSphereGaussianCurvature R L k ρ t x ≤ 2 * k ^ 2 ∧
      (D.markedSphereGaussianCurvature R L k ρ t x = 2 * k ^ 2 ↔
        x = markedSphereCenterParameter (B.b_pos.trans hR) hL))
    (A : E3 ≃ᵃⁱ[ℝ] E3) {s t : ℝ}
    (hGE : Topology.IsEmbedding (D.markedSphereSlice R L k ρ t))
    (himage : A '' range (D.markedSphereSlice R L k ρ s) =
      range (D.markedSphereSlice R L k ρ t)) :
    A.linearIsometryEquiv (e3Basis 2) = e3Basis 2 := by
  let m := markedSphereCenterParameter (B.b_pos.trans hR) hL
  let a := sphereCanonicalCoordinates m m
  have hfix := D.markedSphere_congruence_fixes_marker_of_peak
    hR hL hk.le hρ hsmall hpeak A hGE himage
  have hbase : A (D.markedSphereSlice R L k ρ s m) = D.markedSphereSlice R L k ρ t m := by
    have hfs : D.markedSphereSlice R L k ρ s m = D.markedSphereMarker R L k ρ :=
      D.markedSphereCenter_image hR hL k ρ s
    have hft : D.markedSphereSlice R L k ρ t m = D.markedSphereMarker R L k ρ :=
      D.markedSphereCenter_image hR hL k ρ t
    rw [hfs, hft]
    exact hfix
  have hsm (v : ℝ) : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ (D.markedSphereSlice R L k ρ v) :=
    D.markedSphereFamily_slice_contMDiff hR hL hρ hsmall v
  have himm (v : ℝ) := D.markedSphereFamily_mfderiv_injective hR hL hk.le hρ hsmall v
  obtain ⟨H, hHa, hH, heq, hbij⟩ := exists_sphere_congruence_reparametrization A
    (hsm s) (hsm t) (himm s) (himm t) hGE himage hbase
  change H a = a at hHa
  have hunit (v : ℝ) : IsUnitSurfaceNormal
      (sphereCanonicalSurfaceChart (D.markedSphereSlice R L k ρ v) m) a (e3Basis 2) := by
    have hu := isUnitSurfaceNormal_sphereCanonicalSurfaceChart
      (F := D.markedSphereSlice R L k ρ v)
      (N := fun z => sphereMarkedNormal D R L k ρ (z, v)) (hsm v)
      (fun z => ⟨sphereMarkedNormal_norm D hR hL hρ hsmall (z, v),
        sphereMarkedNormal_orthogonal D hR hL hρ hsmall v z⟩) m a
    rw [show a = sphereCanonicalCoordinates m m from rfl,
      sphereCanonicalCoordinates_left_inv] at hu
    rw [D.markedSphereCenter_normal hR hL hρ hsmall v] at hu
    exact hu
  have hmt := D.markedSphereCanonicalCenter_mean hR hL hk.le hρ hsmall t
  have hms := D.markedSphereCanonicalCenter_mean hR hL hk.le hρ hsmall s
  apply normal_fixed_of_affine_surface_germ A
    (contDiff_sphereCanonicalSurfaceChart (hsm s) m)
    (contDiff_sphereCanonicalSurfaceChart (hsm t) m) hH heq hbij
    (by rw [hHa]; exact sphereCanonicalSurfaceChart_fderiv_injective (hsm t) (himm t) m a)
    (hunit s) (by rw [hHa]; exact hunit t)
  · rw [hHa, hms, hmt]
  · rw [hHa, hmt]
    nlinarith

/-- The embedding length, peak strength, and support radius are all chosen by
the already proved actual construction. No peak or marker constraint is assumed. -/
theorem IsometricGraphDevelopment.exists_markedSphere_fixed_marker_normal
    {B : FlatAnnularCore} (D : IsometricGraphDevelopment B) {R : ℝ} (hR : B.b < R) :
    ∃ L : ℝ, ∃ hL : 0 < L, ∃ k : ℝ, 0 < k ∧ ∀ ε : ℝ, 0 < ε → ∃ ρ : ℝ,
      0 < ρ ∧ ρ < L / 64 ∧ k * ρ ^ 2 / 2 < ε ∧
      (∀ t : ℝ, Topology.IsEmbedding (D.markedSphereSlice R L k ρ t)) ∧
      (∀ t : ℝ, ∀ x : SpherePoint,
        D.markedSphereGaussianCurvature R L k ρ t x ≤ 2 * k ^ 2 ∧
        (D.markedSphereGaussianCurvature R L k ρ t x = 2 * k ^ 2 ↔
          x = markedSphereCenterParameter (B.b_pos.trans hR) hL)) ∧
      ∀ s t : ℝ, ∀ A : E3 ≃ᵃⁱ[ℝ] E3,
        A '' range (D.markedSphereSlice R L k ρ s) =
          range (D.markedSphereSlice R L k ρ t) →
        A (D.markedSphereMarker R L k ρ) = D.markedSphereMarker R L k ρ ∧
        A.linearIsometryEquiv (e3Basis 2) = e3Basis 2 := by
  obtain ⟨L, hL, hfamily⟩ := D.exists_markedSphereFamily_regular hR
  obtain ⟨k, hk, hradius⟩ := D.exists_markedSphere_unique_peak_iff hR hL
  refine ⟨L, hL, k, hk, fun ε hε => ?_⟩
  obtain ⟨ρ, hρ, hsmall, hheight, hpeak⟩ := hradius ε hε
  have hE (t : ℝ) : Topology.IsEmbedding (D.markedSphereSlice R L k ρ t) :=
    ((hfamily k ρ hk.le hρ hsmall).2 t).1
  refine ⟨ρ, hρ, hsmall, hheight, hE, hpeak, fun s t A himage => ?_⟩
  exact ⟨D.markedSphere_congruence_fixes_marker_of_peak
    hR hL hk.le hρ hsmall hpeak A (hE t) himage,
    D.markedSphere_congruence_fixes_normal_of_peak
      hR hL hk hρ hsmall hpeak A (hE t) himage⟩

/-- The fixed local cap chart used to build the actual principal frame. -/
def IsometricGraphDevelopment.markerCapComposite {B : FlatAnnularCore}
    (_D : IsometricGraphDevelopment B) (R L k ρ : ℝ) : PolarPoint → E3 :=
  markedCapMap R B.cRight L k ρ ∘ capSphereRadialMap (capSphereRatio R L)

def markerChartPoint {R L : ℝ} (hR : 0 < R) (hL : 0 < L) : PolarPoint :=
  sphereCanonicalCoordinates (markedSphereCenterParameter hR hL)
    (markedSphereCenterParameter hR hL)

theorem markerChartPoint_eq_south {R L : ℝ} (hR : 0 < R) (hL : 0 < L) :
    markerChartPoint hR hL = sphereSouthChart (markedSphereCenterParameter hR hL) := by
  unfold markerChartPoint sphereCanonicalCoordinates
  rw [ite_eq_right (not_le.mpr (markedSphereCenterParameter_south hR hL))]
  rfl

theorem markerChartPoint_cap_coordinates {R L : ℝ} (hR : 0 < R) (hL : 0 < L) :
    capSphereRadialMap (capSphereRatio R L) (markerChartPoint hR hL) =
      markedCapCenterParameter R L := by
  rw [markerChartPoint_eq_south, markedSphereCenterParameter_coordinates]

theorem IsometricGraphDevelopment.contDiff_markerCapComposite {B : FlatAnnularCore}
    (D : IsometricGraphDevelopment B) {R L : ℝ} (hR : 0 < R) (hL : 0 < L) (k ρ : ℝ) :
    ContDiff ℝ ∞ (D.markerCapComposite R L k ρ) :=
  (contDiff_markedCapMap hR hL B.cRight k ρ).comp (contDiff_capSphereRadialMap _)

theorem IsometricGraphDevelopment.markerCapComposite_immersion {B : FlatAnnularCore}
    (D : IsometricGraphDevelopment B) {R L k ρ : ℝ}
    (hR : 0 < R) (hL : 0 < L) (hk : 0 ≤ k) (hρ : 0 < ρ) (hsmall : ρ < L / 64) :
    Injective (fderiv ℝ (D.markerCapComposite R L k ρ) (markerChartPoint hR hL)) := by
  have ha := capSphereRatio_mem hR hL
  rw [IsometricGraphDevelopment.markerCapComposite, fderiv_comp _
    ((contDiff_markedCapMap hR hL B.cRight k ρ).differentiable (by simp) _)
    ((contDiff_capSphereRadialMap _).differentiable (by simp) _),
    markerChartPoint_cap_coordinates]
  exact (markedCapMap_fderiv_injective hR hL hk hρ hsmall B.cRight
    (markedCapCenterParameter_mem hR hL).le).comp
    (capSphereRadialMap_fderiv_injective ha.1 ha.2 _)

theorem IsometricGraphDevelopment.markerCapComposite_normal {B : FlatAnnularCore}
    (D : IsometricGraphDevelopment B) {R L k ρ : ℝ}
    (hR : 0 < R) (hL : 0 < L) (hρ : 0 < ρ) (hsmall : ρ < L / 64) :
    IsUnitSurfaceNormal (D.markerCapComposite R L k ρ)
      (markerChartPoint hR hL) (e3Basis 2) := by
  have hn := (isUnitSurfaceNormal_markedCap hR hL hρ hsmall B.cRight
    (capSphereRadialMap (capSphereRatio R L) (markerChartPoint hR hL))).comp
    ((contDiff_markedCapMap hR hL B.cRight k ρ).differentiable (by simp) _)
    ((contDiff_capSphereRadialMap _).differentiable (by simp) _)
  rw [markerChartPoint_cap_coordinates, markedCapNormal_center hR hL k ρ] at hn
  exact hn

theorem IsometricGraphDevelopment.markedSphereCanonicalCenter_germ
    {B : FlatAnnularCore} (D : IsometricGraphDevelopment B) {R L k ρ : ℝ}
    (hR : B.b < R) (hL : 0 < L) (hρ : 0 < ρ) (hsmall : ρ < L / 64) (t : ℝ) :
    sphereCanonicalSurfaceChart (D.markedSphereSlice R L k ρ t)
      (markedSphereCenterParameter (B.b_pos.trans hR) hL)
      =ᶠ[𝓝 (markerChartPoint (B.b_pos.trans hR) hL)] D.markerCapComposite R L k ρ := by
  have hs := markedSphereCenterParameter_south (B.b_pos.trans hR) hL
  unfold sphereCanonicalSurfaceChart sphereCanonicalCoordinates
  rw [ite_eq_right (not_le.mpr hs), markerChartPoint_eq_south]
  change sphereSouthSurfaceChart (D.markedSphereSlice R L k ρ t)
    =ᶠ[𝓝 (sphereSouthChart (markedSphereCenterParameter (B.b_pos.trans hR) hL))]
    D.markerCapComposite R L k ρ
  exact markedSphereSouthSurfaceChart_germ D hR hL hρ hsmall t _ hs.le

private theorem marker_matrix_conjugate_eigenpair
    (J S : Matrix (Fin 2) (Fin 2) ℝ) (hJ : IsUnit J.det)
    {eigenvalue : ℝ} {v : MarkerPlane} (hv : v ≠ 0) (he : S.mulVec v = eigenvalue • v) :
    (J⁻¹).mulVec v ≠ 0 ∧ (J⁻¹ * S * J).mulVec ((J⁻¹).mulVec v) = eigenvalue • (J⁻¹).mulVec v := by
  have hid : J.mulVec ((J⁻¹).mulVec v) = v := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv J hJ, Matrix.one_mulVec]
  refine ⟨?_, ?_⟩
  · intro hz
    exact hv (by simpa only [hz, Matrix.mulVec_zero] using hid.symm)
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hid, he, Matrix.mulVec_smul]

/-- The two eigenlines come from the computed cap shape and the genuine
invertible radial chart, with no spectral or principal-line assumption. -/
theorem IsometricGraphDevelopment.exists_markerCapComposite_eigenbasis
    {B : FlatAnnularCore} (D : IsometricGraphDevelopment B) {R L k ρ : ℝ}
    (hR : 0 < R) (hL : 0 < L) (hk : 0 < k) (hρ : 0 < ρ) (hsmall : ρ < L / 64) :
    ∃ b : Module.Basis (Fin 2) ℝ MarkerPlane, ∀ i : Fin 2,
      (surfaceShapeMatrix (D.markerCapComposite R L k ρ) (e3Basis 2)
        (markerChartPoint hR hL)).toLin' (b i) = (![-k, -2 * k] : Fin 2 → ℝ) i • b i := by
  let a := markerChartPoint hR hL
  let φ := capSphereRadialMap (capSphereRatio R L)
  let J := surfaceJacobian φ a
  let S := surfaceShapeMatrix (markedCapMap R B.cRight L k ρ)
    (markedCapNormal R L k ρ (markedCapCenterParameter R L)) (markedCapCenterParameter R L)
  let S₀ := surfaceShapeMatrix (D.markerCapComposite R L k ρ) (e3Basis 2) a
  have ha := capSphereRatio_mem hR hL
  have hJi := capSphereRadialMap_fderiv_injective ha.1 ha.2 a
  have hJ : IsUnit J.det := isUnit_iff_ne_zero.mpr (surfaceJacobian_det_ne_zero hJi)
  have hshape : S₀ = J⁻¹ * S * J := by
    have hpoint : capSphereRadialMap (capSphereRatio R L) a = markedCapCenterParameter R L :=
      markerChartPoint_cap_coordinates hR hL
    have hc := surfaceShapeMatrix_comp
      ((contDiff_markedCapMap hR hL B.cRight k ρ).of_le
        (by simp : (2 : ℕ∞ω) ≤ ∞)).contDiffAt
      ((contDiff_capSphereRadialMap (capSphereRatio R L)).of_le
        (by simp : (2 : ℕ∞ω) ≤ ∞)).contDiffAt
      (isUnitSurfaceNormal_markedCap hR hL hρ hsmall B.cRight (φ a))
      (by rw [hpoint]
          exact markedCapMap_fderiv_injective hR hL hk.le hρ hsmall B.cRight
            (markedCapCenterParameter_mem hR hL).le) hJi
    dsimp only [φ] at hc
    rw [hpoint, markedCapNormal_center hR hL k ρ] at hc
    change surfaceShapeMatrix (markedCapMap R B.cRight L k ρ ∘
      capSphereRadialMap (capSphereRatio R L)) (e3Basis 2) a =
      (surfaceJacobian (capSphereRadialMap (capSphereRatio R L)) a)⁻¹ *
        surfaceShapeMatrix (markedCapMap R B.cRight L k ρ)
          (markedCapNormal R L k ρ (markedCapCenterParameter R L)) (markedCapCenterParameter R L) *
        surfaceJacobian (capSphereRadialMap (capSphereRatio R L)) a
    rw [markedCapNormal_center hR hL k ρ]
    exact hc
  have he := surfaceShapeMatrix_markedCap_center_eigenvectors hR hL hk.ne' B.cRight ρ
  dsimp only at he
  obtain ⟨hneq, hv0, hv1, he0, he1⟩ := he
  let K := surfaceJacobian (markedCapCoordinates R L) (markedCapCenterParameter R L)
  have h0 := marker_matrix_conjugate_eigenpair J S hJ hv0 he0
  have h1 := marker_matrix_conjugate_eigenpair J S hJ hv1 he1
  let v : Fin 2 → MarkerPlane := ![(J⁻¹).mulVec ((K⁻¹).mulVec ![1, 0]),
    (J⁻¹).mulVec ((K⁻¹).mulVec ![0, 1])]
  let μ : Fin 2 → ℝ := ![-k, -2 * k]
  have hv : ∀ i, v i ≠ 0 := by intro i; fin_cases i; exact h0.1; exact h1.1
  have hμ : μ 0 ≠ μ 1 := hneq
  have heigen : ∀ i, S₀.toLin' (v i) = μ i • v i := by
    intro i
    rw [Matrix.toLin'_apply, hshape]
    fin_cases i
    · exact h0.2
    · exact h1.2
  refine ⟨markerPlaneEigenbasis S₀.toLin' v μ hv hμ heigen, fun i => ?_⟩
  simpa only [markerPlaneEigenbasis_apply] using heigen i

private theorem marker_shape_commutes_of_affine_germ
    (A : E3 ≃ᵃⁱ[ℝ] E3) {C : PolarPoint → E3} {H : PolarPoint → PolarPoint}
    {a : PolarPoint} {N : E3} (hC : ContDiff ℝ ∞ C)
    (hi : Injective (fderiv ℝ C a)) (hN : IsUnitSurfaceNormal C a N)
    (hH : ContDiffAt ℝ ∞ H a) (hHa : H a = a)
    (hbij : Bijective (fderiv ℝ H a)) (hfix : A.linearIsometryEquiv N = N)
    (heq : (fun q => A (C q)) =ᶠ[𝓝 a] C ∘ H) :
    surfaceShapeMatrix C N a * surfaceJacobian H a =
      surfaceJacobian H a * surfaceShapeMatrix C N a := by
  let S := surfaceShapeMatrix C N a
  let J := surfaceJacobian H a
  have htrans := hN.of_affine_reparametrization A
    (hC.differentiable (by simp) a) (hC.differentiable (by simp) (H a))
    (hH.differentiableAt (by simp)) heq hbij.surjective
  have hs : S = J⁻¹ * S * J := by
    calc
      S = surfaceShapeMatrix (fun q => A (C q)) (A.linearIsometryEquiv N) a :=
        (surfaceShapeMatrix_affineIsometry A hC N a).symm
      _ = surfaceShapeMatrix (C ∘ H) (A.linearIsometryEquiv N) a :=
        surfaceShapeMatrix_congr_germ heq _
      _ = J⁻¹ * surfaceShapeMatrix C (A.linearIsometryEquiv N) (H a) * J :=
        surfaceShapeMatrix_comp (hC.of_le (by simp : (2 : ℕ∞ω) ≤ ∞)).contDiffAt
          (hH.of_le (by simp : (2 : ℕ∞ω) ≤ ∞)) htrans (hHa.symm ▸ hi) hbij.injective
      _ = J⁻¹ * S * J := by rw [hfix, hHa]
  have hJ : IsUnit J.det := isUnit_iff_ne_zero.mpr (surfaceJacobian_det_ne_zero hbij.injective)
  have hm : J * S = S * J := by
    calc
      J * S = J * (J⁻¹ * S * J) := congrArg (J * ·) hs
      _ = S * J := by simp only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv J hJ, Matrix.one_mul]
  exact hm.symm

/-- One actual principal frame works for every phase and every ambient image
congruence. Its tangent lines are derived from the actual cap shape. -/
theorem IsometricGraphDevelopment.markedSphere_congruences_in_stabilizers_of_peak
    {B : FlatAnnularCore} (D : IsometricGraphDevelopment B) {R L k ρ : ℝ}
    (hR : B.b < R) (hL : 0 < L) (hk : 0 < k) (hρ : 0 < ρ) (hsmall : ρ < L / 64)
    (hE : ∀ t, Topology.IsEmbedding (D.markedSphereSlice R L k ρ t))
    (hpeak : ∀ t : ℝ, ∀ x : SpherePoint,
      D.markedSphereGaussianCurvature R L k ρ t x ≤ 2 * k ^ 2 ∧
      (D.markedSphereGaussianCurvature R L k ρ t x = 2 * k ^ 2 ↔
        x = markedSphereCenterParameter (B.b_pos.trans hR) hL)) :
    ∃ b : Module.Basis (Fin 3) ℝ E3, ∀ s t : ℝ, ∀ A : E3 ≃ᵃⁱ[ℝ] E3,
      A '' range (D.markedSphereSlice R L k ρ s) = range (D.markedSphereSlice R L k ρ t) →
      A ∈ markerStabilizers (D.markedSphereMarker R L k ρ) b := by
  let hRp := B.b_pos.trans hR
  let m := markedSphereCenterParameter hRp hL
  let a := markerChartPoint hRp hL
  let C := D.markerCapComposite R L k ρ
  let Q : MarkerPlane ≃L[ℝ] PolarPoint := (LinearEquiv.finTwoArrow ℝ ℝ).toContinuousLinearEquiv
  let T : MarkerPlane →L[ℝ] E3 := (fderiv ℝ C a).comp (Q : MarkerPlane →L[ℝ] PolarPoint)
  let S := (surfaceShapeMatrix C (e3Basis 2) a).toLin'
  let μ : Fin 2 → ℝ := ![-k, -2 * k]
  have hCs := D.contDiff_markerCapComposite hRp hL k ρ
  have hCi := D.markerCapComposite_immersion hRp hL hk.le hρ hsmall
  have hCN := D.markerCapComposite_normal (k := k) hRp hL hρ hsmall
  have hTi : Injective T := hCi.comp Q.injective
  have hTN : ∀ v, inner ℝ (T v) (e3Basis 2) = 0 := fun v => hCN.2 (Q v)
  obtain ⟨b, hdiag⟩ := D.exists_markerCapComposite_eigenbasis hRp hL hk hρ hsmall
  have hμ : Injective μ := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · change -k = -2 * k at hij
      exfalso
      nlinarith
    · change -2 * k = -k at hij
      exfalso
      nlinarith
    · rfl
  refine ⟨principalFrame T b (e3Basis 2) hTi hCN.1 hTN, fun s t A himage => ?_⟩
  have hp := D.markedSphere_congruence_fixes_marker_of_peak hR hL hk.le hρ hsmall hpeak A (hE t) himage
  have hn := D.markedSphere_congruence_fixes_normal_of_peak hR hL hk hρ hsmall hpeak A (hE t) himage
  have hbase : A (D.markedSphereSlice R L k ρ s m) = D.markedSphereSlice R L k ρ t m := by
    have hfs : D.markedSphereSlice R L k ρ s m = D.markedSphereMarker R L k ρ :=
      D.markedSphereCenter_image hR hL k ρ s
    have hft : D.markedSphereSlice R L k ρ t m = D.markedSphereMarker R L k ρ :=
      D.markedSphereCenter_image hR hL k ρ t
    rw [hfs, hft]
    exact hp
  have hsm (v : ℝ) : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞
      (D.markedSphereSlice R L k ρ v) :=
    D.markedSphereFamily_slice_contMDiff (k := k) hR hL hρ hsmall v
  have himm (v : ℝ) :=
    D.markedSphereFamily_mfderiv_injective (k := k) hR hL hk.le hρ hsmall v
  obtain ⟨H, hHa, hH, heq, hbij⟩ := exists_sphere_congruence_reparametrization A
    (hsm s) (hsm t) (himm s) (himm t) (hE t) himage hbase
  change H a = a at hHa
  change ContDiffAt ℝ ∞ H a at hH
  have hfs := D.markedSphereCanonicalCenter_germ (k := k) hR hL hρ hsmall s
  have hgt := D.markedSphereCanonicalCenter_germ (k := k) hR hL hρ hsmall t
  have hHt : Tendsto H (𝓝 a) (𝓝 a) := by simpa only [hHa] using hH.continuousAt.tendsto
  have hc : (fun q => A (C q)) =ᶠ[𝓝 a] C ∘ H := by
    have hl : (fun q => A (C q)) =ᶠ[𝓝 a]
        fun q => A (sphereCanonicalSurfaceChart (D.markedSphereSlice R L k ρ s) m q) := by
      filter_upwards [hfs] with q hq
      exact congrArg A hq.symm
    exact hl.trans (heq.trans (hgt.comp_tendsto hHt))
  let J := surfaceJacobian H a
  have hcommM := marker_shape_commutes_of_affine_germ A hCs hCi hCN hH hHa hbij hn hc
  have hcomm : ∀ v, S (J.toLin' v) = J.toLin' (S v) := by
    intro v
    rw [← Matrix.toLin'_mul_apply, ← Matrix.toLin'_mul_apply, hcommM]
  have hd := fderiv_surface_reparametrization A
    (hCs.differentiable (by simp) a) (hCs.differentiable (by simp) (H a))
    (hH.differentiableAt (by simp)) hc
  rw [hHa] at hd
  have hQ : ∀ v, Q (J.toLin' v) = fderiv ℝ H a (Q v) := by
    intro v
    change ((Matrix.mulVec (surfaceLinearMatrix (fderiv ℝ H a)) v) 0,
      (Matrix.mulVec (surfaceLinearMatrix (fderiv ℝ H a)) v) 1) =
        fderiv ℝ H a (v 0, v 1)
    rw [surfaceLinearMatrix_mulVec]
    rfl
  have hchain : ∀ v, A.linearIsometryEquiv (T v) = T (J.toLin' v) := by
    intro v
    calc
      A.linearIsometryEquiv (T v) = fderiv ℝ C a (fderiv ℝ H a (Q v)) :=
        (DFunLike.congr_fun hd (Q v)).symm
      _ = T (J.toLin' v) := congrArg (fderiv ℝ C a) (hQ v).symm
  exact mem_markerStabilizers_of_shape_commute T b (e3Basis 2) hTi hCN.1 hTN
    S J.toLin' μ hμ hdiag (D.markedSphereMarker R L k ρ) A hp hn hchain hcomm

/-- The cap length is supplied by the same actual region construction. Strength
and support radius are genuinely chosen for this very length, rather than
selecting a second, potentially incompatible, cap. -/
theorem IsometricGraphDevelopment.exists_markedSphere_finite_congruences_given_length
    {B : FlatAnnularCore} (D : IsometricGraphDevelopment B) {R L : ℝ}
    (hR : B.b < R) (hL : 0 < L)
    (hRegular : ∀ k ρ : ℝ, 0 ≤ k → 0 < ρ → ρ < L / 64 →
      ∀ t, Topology.IsEmbedding (D.markedSphereSlice R L k ρ t)) :
    ∃ k : ℝ, 0 < k ∧ ∀ ε : ℝ, 0 < ε → ∃ ρ : ℝ,
      0 < ρ ∧ ρ < L / 64 ∧ k * ρ ^ 2 / 2 < ε ∧
      ∃ b : Module.Basis (Fin 3) ℝ E3,
        {A : E3 ≃ᵃⁱ[ℝ] E3 | ∃ s t : ℝ,
          A '' range (D.markedSphereSlice R L k ρ s) =
            range (D.markedSphereSlice R L k ρ t)} ⊆
          markerStabilizers (D.markedSphereMarker R L k ρ) b ∧
        {A : E3 ≃ᵃⁱ[ℝ] E3 | ∃ s t : ℝ,
          A '' range (D.markedSphereSlice R L k ρ s) =
            range (D.markedSphereSlice R L k ρ t)}.encard ≤ 4 := by
  obtain ⟨k, hk, hradius⟩ := D.exists_markedSphere_unique_peak_iff hR hL
  refine ⟨k, hk, fun ε hε => ?_⟩
  obtain ⟨ρ, hρ, hsmall, hheight, hpeak⟩ := hradius ε hε
  obtain ⟨b, hb⟩ := D.markedSphere_congruences_in_stabilizers_of_peak
    hR hL hk hρ hsmall (hRegular k ρ hk.le hρ hsmall) hpeak
  have hsub : {A : E3 ≃ᵃⁱ[ℝ] E3 | ∃ s t : ℝ,
      A '' range (D.markedSphereSlice R L k ρ s) = range (D.markedSphereSlice R L k ρ t)} ⊆
      markerStabilizers (D.markedSphereMarker R L k ρ) b := by
    rintro A ⟨s, t, he⟩
    exact hb s t A he
  exact ⟨ρ, hρ, hsmall, hheight, b, hsub,
    (Set.encard_le_encard hsub).trans (markerStabilizers_encard_le_four _ b)⟩

/-- An actual construction instance as well as the supplied-length interface:
the regular-sphere engine supplies its own admissible length when no region
length has already been fixed. -/
theorem IsometricGraphDevelopment.exists_markedSphere_finite_congruences
    {B : FlatAnnularCore} (D : IsometricGraphDevelopment B) {R : ℝ} (hR : B.b < R) :
    ∃ L : ℝ, 0 < L ∧ ∃ k : ℝ, 0 < k ∧ ∀ ε : ℝ, 0 < ε → ∃ ρ : ℝ,
      0 < ρ ∧ ρ < L / 64 ∧ k * ρ ^ 2 / 2 < ε ∧
      {A : E3 ≃ᵃⁱ[ℝ] E3 | ∃ s t : ℝ,
        A '' range (D.markedSphereSlice R L k ρ s) =
          range (D.markedSphereSlice R L k ρ t)}.encard ≤ 4 := by
  obtain ⟨L, hL, hfamily⟩ := D.exists_markedSphereFamily_regular hR
  obtain ⟨k, hk, hradius⟩ := D.exists_markedSphere_finite_congruences_given_length hR hL
    (fun k ρ hk hρ hsmall t => ((hfamily k ρ hk hρ hsmall).2 t).1)
  refine ⟨L, hL, k, hk, fun ε hε => ?_⟩
  obtain ⟨ρ, hρ, hsmall, hheight, b, _, hfinite⟩ := hradius ε hε
  exact ⟨ρ, hρ, hsmall, hheight, hfinite⟩

end ContinuousFlexibility
