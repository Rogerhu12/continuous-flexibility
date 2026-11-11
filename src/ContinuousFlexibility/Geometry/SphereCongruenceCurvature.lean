import ContinuousFlexibility.Geometry.SphereCurvature
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Curvature transport from actual sphere image congruence

The target canonical stereographic chart is an embedded open branch of the
actual full sphere image. Image congruence and continuity produce its image germ.
The previously constructed projected inverse produces a genuinely smooth local
reparameterization. The two actual unit normals differ by a sign, as proved from
the dimension of the orthogonal complement of the actual surface differential.
Gaussian curvature therefore transports without an outward-orientation premise.
-/

noncomputable section

namespace ContinuousFlexibility

open Set Filter Function
open scoped ContDiff Manifold Topology

local notation "SpherePoint" => {v : E3 // v ∈ Metric.sphere (0 : E3) 1}
local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp [E3]⟩

set_option backward.isDefEq.respectTransparency false

/-- The actual normal space of an immersed plane in E3 has dimension one. -/
theorem IsUnitSurfaceNormal.eq_or_eq_neg
    {F : PolarPoint → E3} {x : PolarPoint} {N M : E3}
    (hN : IsUnitSurfaceNormal F x N) (hM : IsUnitSurfaceNormal F x M)
    (hi : Injective (fderiv ℝ F x)) : M = N ∨ M = -N := by
  let T : Submodule ℝ E3 := (fderiv ℝ F x).range
  have hTrank : Module.finrank ℝ T = 2 := by
    have h := LinearMap.finrank_range_of_inj
      (f := (fderiv ℝ F x).toLinearMap) hi
    simpa [T, PolarPoint] using h
  have hOrank : Module.finrank ℝ Tᗮ = 1 := by
    have h := T.finrank_add_finrank_orthogonal
    rw [hTrank] at h
    have hE : Module.finrank ℝ E3 = 3 := by simp [E3]
    rw [hE] at h
    omega
  have hNmem : N ∈ Tᗮ := by
    intro v hv
    obtain ⟨u, rfl⟩ := hv
    exact hN.2 u
  have hMmem : M ∈ Tᗮ := by
    intro v hv
    obtain ⟨u, rfl⟩ := hv
    exact hM.2 u
  have hNne : N ≠ 0 := by
    intro he
    have h := hN.1
    simp only [he, norm_zero] at h
    exact zero_ne_one h
  have hspan : Submodule.span ℝ {N} = Tᗮ :=
    Submodule.eq_of_le_of_finrank_eq
      (Submodule.span_le.mpr (by intro v hv; rcases Set.mem_singleton_iff.mp hv with rfl; exact hNmem))
      ((finrank_span_singleton hNne).trans hOrank.symm)
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (hspan.symm ▸ hMmem)
  have habs : |a| = 1 := by
    have hn := congrArg norm ha
    simpa only [norm_smul, Real.norm_eq_abs, hN.1, hM.1, mul_one] using hn
  rcases abs_eq_abs.mp (show |a| = |(1 : ℝ)| by simpa using habs) with h | h
  · left
    simpa only [h, one_smul] using ha.symm
  · right
    simpa only [h, neg_one_smul] using ha.symm

/-- A canonical full-plane chart: its range omits the opposite polar point. -/
def sphereCanonicalCoordinates (x : SpherePoint) :
    OpenPartialHomeomorph SpherePoint PolarPoint :=
  if 0 ≤ (x : E3) 2 then sphereNorthCoordinates else sphereSouthCoordinates

theorem sphereCanonicalCoordinates_mem_source (x : SpherePoint) :
    x ∈ (sphereCanonicalCoordinates x).source := by
  unfold sphereCanonicalCoordinates
  split_ifs with hx
  ·
    change (x : E3) 2 ≠ -1
    linarith
  ·
    change (x : E3) 2 ≠ 1
    linarith

@[simp] theorem sphereCanonicalCoordinates_target (x : SpherePoint) :
    (sphereCanonicalCoordinates x).target = univ := by
  unfold sphereCanonicalCoordinates
  split_ifs <;> rfl

theorem sphereCanonicalCoordinates_left_inv (x : SpherePoint) :
    (sphereCanonicalCoordinates x).symm (sphereCanonicalCoordinates x x) = x :=
  (sphereCanonicalCoordinates x).left_inv (sphereCanonicalCoordinates_mem_source x)

theorem sphereCanonicalCoordinates_mdiff (x : SpherePoint) :
    (sphereCanonicalCoordinates x).MDifferentiable (𝓡 2) 𝓘(ℝ, PolarPoint) := by
  unfold sphereCanonicalCoordinates
  split_ifs
  · exact mdifferentiable_sphereNorthCoordinates
  · exact mdifferentiable_sphereSouthCoordinates

theorem contMDiff_sphereCanonicalInverse (x : SpherePoint) :
    ContMDiff 𝓘(ℝ, PolarPoint) (𝓡 2) ∞ (sphereCanonicalCoordinates x).symm := by
  unfold sphereCanonicalCoordinates
  split_ifs
  · exact contMDiff_sphereNorthInverse
  · exact contMDiff_sphereSouthInverse

theorem isOpenEmbedding_sphereCanonicalInverse (x : SpherePoint) :
    Topology.IsOpenEmbedding (sphereCanonicalCoordinates x).symm :=
  (sphereCanonicalCoordinates x).symm.isOpenEmbedding (sphereCanonicalCoordinates_target x)

theorem sphereCanonicalInverse_range (x : SpherePoint) :
    range (sphereCanonicalCoordinates x).symm = (sphereCanonicalCoordinates x).source := by
  rw [← image_univ, ← sphereCanonicalCoordinates_target x]
  exact (sphereCanonicalCoordinates x).symm.image_source_eq_target

def sphereCanonicalSurfaceChart (F : SpherePoint → E3) (x : SpherePoint) :
    PolarPoint → E3 := F ∘ (sphereCanonicalCoordinates x).symm

theorem contDiff_sphereCanonicalSurfaceChart {F : SpherePoint → E3}
    (hF : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ F) (x : SpherePoint) :
    ContDiff ℝ ∞ (sphereCanonicalSurfaceChart F x) :=
  (hF.comp (contMDiff_sphereCanonicalInverse x)).contDiff

theorem sphereCanonicalSurfaceChart_fderiv_injective {F : SpherePoint → E3}
    (hF : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ F)
    (hi : ∀ x, Injective (mfderiv (𝓡 2) 𝓘(ℝ, E3) F x))
    (x : SpherePoint) (q : PolarPoint) :
    Injective (fderiv ℝ (sphereCanonicalSurfaceChart F x) q) := by
  let e := sphereCanonicalCoordinates x
  have he := sphereCanonicalCoordinates_mdiff x
  have hq : q ∈ e.target := by rw [sphereCanonicalCoordinates_target]; trivial
  have hcomp : Injective (mfderiv 𝓘(ℝ, PolarPoint) 𝓘(ℝ, E3)
      (F ∘ e.symm) q) := by
    rw [mfderiv_comp q (hF.mdifferentiable (by simp) _)
      (he.mdifferentiableAt_symm hq)]
    exact (hi _).comp (he.symm.mfderiv_injective hq)
  rw [mfderiv_eq_fderiv] at hcomp
  let B := NormedSpace.fromTangentSpace (𝕜 := ℝ) q
  intro u v huv
  apply B.symm.injective
  apply hcomp
  change (NormedSpace.fromTangentSpace (𝕜 := ℝ) (F (e.symm q))).symm
      (fderiv ℝ (F ∘ e.symm) q (B (B.symm u))) =
    (NormedSpace.fromTangentSpace (𝕜 := ℝ) (F (e.symm q))).symm
      (fderiv ℝ (F ∘ e.symm) q (B (B.symm v)))
  rw [B.apply_symm_apply, B.apply_symm_apply]
  exact congrArg (NormedSpace.fromTangentSpace (𝕜 := ℝ) (F (e.symm q))).symm huv

theorem isUnitSurfaceNormal_sphereCanonicalSurfaceChart {F N : SpherePoint → E3}
    (hF : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ F)
    (hN : ∀ x, ‖N x‖ = 1 ∧ ∀ v : TangentSpace (𝓡 2) x,
      inner ℝ (mvfderiv (𝓡 2) F x v) (N x) = 0)
    (x : SpherePoint) (q : PolarPoint) :
    IsUnitSurfaceNormal (sphereCanonicalSurfaceChart F x) q
      (N ((sphereCanonicalCoordinates x).symm q)) := by
  let e := sphereCanonicalCoordinates x
  have he := sphereCanonicalCoordinates_mdiff x
  have hq : q ∈ e.target := by rw [sphereCanonicalCoordinates_target]; trivial
  have hd := mvfderiv_comp q (hF.mdifferentiable (by simp) _)
    (he.mdifferentiableAt_symm hq)
  rw [mvfderiv_eq_fderiv] at hd
  refine ⟨(hN _).1, fun v => ?_⟩
  let B := NormedSpace.fromTangentSpace (𝕜 := ℝ) q
  have hv := DFunLike.congr_fun hd (B.symm v)
  change fderiv ℝ (F ∘ e.symm) q (B (B.symm v)) =
    mvfderiv (𝓡 2) F (e.symm q)
      (mfderiv 𝓘(ℝ, PolarPoint) (𝓡 2) e.symm q (B.symm v)) at hv
  rw [B.apply_symm_apply] at hv
  change inner ℝ (fderiv ℝ (F ∘ e.symm) q v) (N (e.symm q)) = 0
  rw [hv]
  exact (hN _).2 _

theorem sphereGaussianCurvature_eq_canonical (F N : SpherePoint → E3) (x : SpherePoint) :
    sphereGaussianCurvature F N x =
      surfaceGaussianCurvature (sphereCanonicalSurfaceChart F x) (N x)
        (sphereCanonicalCoordinates x x) := by
  unfold sphereCanonicalSurfaceChart sphereCanonicalCoordinates sphereGaussianCurvature
  split_ifs <;> rfl

/-- Actual image inclusion localizes to a target embedded open chart. -/
theorem eventually_mem_open_chart_image
    {M : Type*} [TopologicalSpace M] {G : M → E3}
    (hG : Topology.IsEmbedding G) {ψ : PolarPoint → M}
    (hψ : Topology.IsOpenEmbedding ψ) {f : PolarPoint → E3} {a b : PolarPoint}
    (hf : ContinuousAt f a) (hbase : f a = G (ψ b))
    (himage : ∀ z, f z ∈ range G) :
    ∀ᶠ z in 𝓝 a, f z ∈ (G ∘ ψ) '' univ := by
  obtain ⟨O, hO, hGO⟩ := hG.isInducing.image_eq_isOpen_inter_range hψ.isOpen_range
  have hb : G (ψ b) ∈ O := by
    have hm : G (ψ b) ∈ G '' range ψ := ⟨ψ b, ⟨b, rfl⟩, rfl⟩
    rw [hGO] at hm
    exact hm.1
  have hnear := hf.eventually (hO.mem_nhds (hbase.symm ▸ hb))
  filter_upwards [hnear] with z hz
  have hm : f z ∈ G '' range ψ := by rw [hGO]; exact ⟨hz, himage z⟩
  obtain ⟨y, ⟨w, rfl⟩, hwy⟩ := hm
  exact ⟨w, mem_univ _, hwy⟩

/-- A smooth reparameterization is constructed from the actual full-image
congruence; it is not an input to the theorem. -/
theorem exists_sphere_congruence_reparametrization
    (A : E3 ≃ᵃⁱ[ℝ] E3) {F G : SpherePoint → E3}
    (hF : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ F)
    (hG : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ G)
    (hFi : ∀ x, Injective (mfderiv (𝓡 2) 𝓘(ℝ, E3) F x))
    (hGi : ∀ y, Injective (mfderiv (𝓡 2) 𝓘(ℝ, E3) G y))
    (hGE : Topology.IsEmbedding G)
    (himage : A '' range F = range G) {x y : SpherePoint} (hbase : A (F x) = G y) :
    ∃ H : PolarPoint → PolarPoint,
      H (sphereCanonicalCoordinates x x) = sphereCanonicalCoordinates y y ∧
      ContDiffAt ℝ ∞ H (sphereCanonicalCoordinates x x) ∧
      (fun q => A (sphereCanonicalSurfaceChart F x q)) =ᶠ[𝓝 (sphereCanonicalCoordinates x x)]
        sphereCanonicalSurfaceChart G y ∘ H ∧
      Bijective (fderiv ℝ H (sphereCanonicalCoordinates x x)) := by
  let f := sphereCanonicalSurfaceChart F x
  let g := sphereCanonicalSurfaceChart G y
  have hf := contDiff_sphereCanonicalSurfaceChart hF x
  have hg := contDiff_sphereCanonicalSurfaceChart hG y
  have hge : Topology.IsEmbedding g :=
    hGE.comp (isOpenEmbedding_sphereCanonicalInverse y).isEmbedding
  have hbase' : A (f (sphereCanonicalCoordinates x x)) = g (sphereCanonicalCoordinates y y) := by
    simpa only [f, g, sphereCanonicalSurfaceChart, Function.comp_apply,
      sphereCanonicalCoordinates_left_inv] using hbase
  have hinc : ∀ q, A (f q) ∈ range G := by
    intro q
    rw [← himage]
    exact ⟨f q, ⟨(sphereCanonicalCoordinates x).symm q, rfl⟩, rfl⟩
  have himage' : ∀ᶠ q in 𝓝 (sphereCanonicalCoordinates x x), A (f q) ∈ g '' univ :=
    eventually_mem_open_chart_image hGE (isOpenEmbedding_sphereCanonicalInverse y)
      (contDiffAt_affineSurfaceMap A hf.contDiffAt).continuousAt hbase' hinc
  apply exists_smooth_local_reparametrization_germ A isOpen_univ (mem_univ _)
    (fun q _ => hf.contDiffAt) (fun q _ => hg.contDiffAt)
    (fun q _ => sphereCanonicalSurfaceChart_fderiv_injective hF hFi x q)
    (sphereCanonicalSurfaceChart_fderiv_injective hG hGi y _)
    (hge.comp Topology.IsEmbedding.subtypeVal) isOpen_univ (mem_univ _) hbase' himage'

/-- Normal transport and the codimension-one theorem give an actual sign,
including orientation-reversing ambient isometries. -/
theorem normal_sign_of_affine_surface_germ
    (A : E3 ≃ᵃⁱ[ℝ] E3) {f g : PolarPoint → E3} {H : PolarPoint → PolarPoint}
    {a : PolarPoint} {N M : E3}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hH : ContDiffAt ℝ ∞ H a)
    (heq : (fun q => A (f q)) =ᶠ[𝓝 a] g ∘ H)
    (hbij : Bijective (fderiv ℝ H a))
    (hgi : Injective (fderiv ℝ g (H a)))
    (hN : IsUnitSurfaceNormal f a N) (hM : IsUnitSurfaceNormal g (H a) M) :
    A.linearIsometryEquiv N = M ∨ A.linearIsometryEquiv N = -M := by
  have htrans := hN.of_affine_reparametrization A
    (hf.differentiable (by simp) a) (hg.differentiable (by simp) (H a))
    (hH.differentiableAt (by simp)) heq hbij.surjective
  exact hM.eq_or_eq_neg htrans hgi

/-- Actual Gaussian curvature transport follows from the constructed local
change of parameters and the proved sign alternative for normals. -/
theorem gaussianCurvature_of_affine_surface_germ
    (A : E3 ≃ᵃⁱ[ℝ] E3) {f g : PolarPoint → E3} {H : PolarPoint → PolarPoint}
    {a : PolarPoint} {N M : E3}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hH : ContDiffAt ℝ ∞ H a)
    (heq : (fun q => A (f q)) =ᶠ[𝓝 a] g ∘ H)
    (hbij : Bijective (fderiv ℝ H a))
    (hgi : Injective (fderiv ℝ g (H a)))
    (hN : IsUnitSurfaceNormal f a N) (hM : IsUnitSurfaceNormal g (H a) M) :
    surfaceGaussianCurvature f N a = surfaceGaussianCurvature g M (H a) := by
  have htrans := hN.of_affine_reparametrization A
    (hf.differentiable (by simp) a) (hg.differentiable (by simp) (H a))
    (hH.differentiableAt (by simp)) heq hbij.surjective
  have hc : surfaceGaussianCurvature f N a =
      surfaceGaussianCurvature g (A.linearIsometryEquiv N) (H a) := by
    rw [← surfaceGaussianCurvature_affineIsometry A hf N a,
      surfaceGaussianCurvature_congr_germ heq]
    exact surfaceGaussianCurvature_comp
      (hg.of_le (by simp : (2 : ℕ∞ω) ≤ ∞)).contDiffAt
      (hH.of_le (by simp : (2 : ℕ∞ω) ≤ ∞)) htrans hgi hbij.injective
  rcases hM.eq_or_eq_neg htrans hgi with h | h
  · simpa only [h] using hc
  · simpa only [h, surfaceGaussianCurvature_neg_normal] using hc

/-- Curvature of the actual coordinate shape, not of an arbitrary scalar field,
is preserved by every ambient congruence between embedded regular spheres. -/
theorem sphereGaussianCurvature_congruence
    (A : E3 ≃ᵃⁱ[ℝ] E3) {F G N M : SpherePoint → E3}
    (hF : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ F)
    (hG : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ G)
    (hFi : ∀ x, Injective (mfderiv (𝓡 2) 𝓘(ℝ, E3) F x))
    (hGi : ∀ y, Injective (mfderiv (𝓡 2) 𝓘(ℝ, E3) G y))
    (hGE : Topology.IsEmbedding G)
    (hN : ∀ x, ‖N x‖ = 1 ∧ ∀ v : TangentSpace (𝓡 2) x,
      inner ℝ (mvfderiv (𝓡 2) F x v) (N x) = 0)
    (hM : ∀ y, ‖M y‖ = 1 ∧ ∀ v : TangentSpace (𝓡 2) y,
      inner ℝ (mvfderiv (𝓡 2) G y v) (M y) = 0)
    (himage : A '' range F = range G) {x y : SpherePoint} (hbase : A (F x) = G y) :
    sphereGaussianCurvature F N x = sphereGaussianCurvature G M y := by
  obtain ⟨H, hHa, hH, heq, hbij⟩ :=
    exists_sphere_congruence_reparametrization A hF hG hFi hGi hGE himage hbase
  have hn := isUnitSurfaceNormal_sphereCanonicalSurfaceChart hF hN x
    (sphereCanonicalCoordinates x x)
  have hm := isUnitSurfaceNormal_sphereCanonicalSurfaceChart hG hM y
    (sphereCanonicalCoordinates y y)
  rw [sphereCanonicalCoordinates_left_inv] at hn hm
  rw [sphereGaussianCurvature_eq_canonical, sphereGaussianCurvature_eq_canonical]
  have hc := gaussianCurvature_of_affine_surface_germ A
    (contDiff_sphereCanonicalSurfaceChart hF x) (contDiff_sphereCanonicalSurfaceChart hG y)
    hH heq hbij
    (by rw [hHa]; exact sphereCanonicalSurfaceChart_fderiv_injective hG hGi y _)
    hn (by rw [hHa]; exact hm)
  simpa only [hHa] using hc

theorem IsometricGraphDevelopment.markedSphereGaussianCurvature_congruence
    {B : FlatAnnularCore} (D : IsometricGraphDevelopment B) {R L k ρ : ℝ}
    (hR : B.b < R) (hL : 0 < L) (hk : 0 ≤ k) (hρ : 0 < ρ) (hsmall : ρ < L / 64)
    (A : E3 ≃ᵃⁱ[ℝ] E3) {s t : ℝ}
    (hGE : Topology.IsEmbedding (fun x : SpherePoint =>
      sphereGraphCapFamily D (markedCapMap R B.cRight L k ρ) R L (x, t)))
    (himage : A '' range (fun x : SpherePoint =>
        sphereGraphCapFamily D (markedCapMap R B.cRight L k ρ) R L (x, s)) =
      range (fun x : SpherePoint =>
        sphereGraphCapFamily D (markedCapMap R B.cRight L k ρ) R L (x, t)))
    {x y : SpherePoint}
    (hbase : A (sphereGraphCapFamily D (markedCapMap R B.cRight L k ρ) R L (x, s)) =
      sphereGraphCapFamily D (markedCapMap R B.cRight L k ρ) R L (y, t)) :
    D.markedSphereGaussianCurvature R L k ρ s x =
      D.markedSphereGaussianCurvature R L k ρ t y := by
  apply sphereGaussianCurvature_congruence A
    (D.markedSphereFamily_slice_contMDiff hR hL hρ hsmall s)
    (D.markedSphereFamily_slice_contMDiff hR hL hρ hsmall t)
    (D.markedSphereFamily_mfderiv_injective hR hL hk hρ hsmall s)
    (D.markedSphereFamily_mfderiv_injective hR hL hk hρ hsmall t) hGE
    (fun x => ⟨sphereMarkedNormal_norm D hR hL hρ hsmall (x, s),
      sphereMarkedNormal_orthogonal D hR hL hρ hsmall s x⟩)
    (fun y => ⟨sphereMarkedNormal_norm D hR hL hρ hsmall (y, t),
      sphereMarkedNormal_orthogonal D hR hL hρ hsmall t y⟩) himage hbase

end ContinuousFlexibility
