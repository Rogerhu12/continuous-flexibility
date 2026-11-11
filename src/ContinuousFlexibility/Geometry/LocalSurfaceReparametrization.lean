import ContinuousFlexibility.Geometry.LocalInverse
import ContinuousFlexibility.Geometry.SurfaceReparametrization
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Smooth local reparameterizations from actual surface images

An injective surface differential has an ambient continuous linear left inverse.
The inverse function theorem applies to the resulting planar projection of the
target chart. An embedded target chart and an actual image germ select its correct
local branch; no smoothness of an already chosen reparameterization is assumed.

Both surface differentials are required for the local diffeomorphism conclusion.
In particular, image equality alone does not exclude a singular parameterization
such as `(x, y) ↦ (x³, y, 0)`. Closed sphere image congruences must still be localized
to these chart hypotheses in a separate theorem.
-/

noncomputable section

namespace ContinuousFlexibility

open Set Filter Topology
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-- A genuine ambient projection, rather than an inverse defined only on `L.range`. -/
theorem exists_continuousLinearMap_leftInverse
    (L : PolarPoint →L[ℝ] E3) (hi : Function.Injective L) :
    ∃ π : E3 →L[ℝ] PolarPoint, π.comp L = ContinuousLinearMap.id ℝ PolarPoint := by
  obtain ⟨π, hπ⟩ := L.toLinearMap.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hi)
  refine ⟨LinearMap.toContinuousLinearMap π, ?_⟩
  apply ContinuousLinearMap.ext
  intro v
  exact DFunLike.congr_fun hπ v

/-- An embedded branch converts actual image membership near its base point into
membership in any smaller open chart neighborhood. -/
theorem eventually_mem_image_of_embedded_chart
    {X : Type*} [TopologicalSpace X] {f : X → E3} {a : X}
    {G : PolarPoint → E3} {V W : Set PolarPoint} {b : PolarPoint}
    (hEmb : Topology.IsEmbedding (fun y : V => G y))
    (hbV : b ∈ V) (hW : IsOpen W) (hbW : b ∈ W)
    (hf : ContinuousAt f a) (hbase : f a = G b)
    (himage : ∀ᶠ x in 𝓝 a, f x ∈ G '' V) :
    ∀ᶠ x in 𝓝 a, f x ∈ G '' (V ∩ W) := by
  have hopen : IsOpen {y : V | (y : PolarPoint) ∈ W} :=
    hW.preimage continuous_subtype_val
  obtain ⟨O, hO, hpre⟩ := hEmb.isInducing.isOpen_iff.mp hopen
  have hbO : G b ∈ O := by
    have hb' : (⟨b, hbV⟩ : V) ∈ {y : V | (y : PolarPoint) ∈ W} := hbW
    rw [← hpre] at hb'
    exact hb'
  have hnear : ∀ᶠ x in 𝓝 a, f x ∈ O :=
    hf.eventually (hO.mem_nhds (hbase.symm ▸ hbO))
  filter_upwards [himage, hnear] with x hx hxo
  obtain ⟨y, hyV, hgy⟩ := hx
  refine ⟨y, ⟨hyV, ?_⟩, hgy⟩
  have hy : (⟨y, hyV⟩ : V) ∈ (fun z : V => G z) ⁻¹' O := by
    change G y ∈ O
    simpa only [hgy] using hxo
  rw [hpre] at hy
  exact hy

/-- Smoothness and differential invertibility for a genuine projected inverse,
at every point where its original differential is invertible. -/
theorem contDiffAt_projected_inverse
    {Q : PolarPoint → PolarPoint}
    (e : OpenPartialHomeomorph PolarPoint PolarPoint)
    (he : (e : PolarPoint → PolarPoint) = Q)
    {y : PolarPoint} (hy : y ∈ e.source)
    (hQ : ContDiffAt ℝ ∞ Q y)
    (hi : (fderiv ℝ Q y).IsInvertible) :
    ContDiffAt ℝ ∞ e.symm (Q y) := by
  obtain ⟨L, hL⟩ := hi
  have hy' : e.symm (Q y) = y := by
    rw [← he]
    exact e.left_inv hy
  apply e.contDiffAt_symm
    (by rw [← he]; exact e.map_source hy)
  · rw [hy', he, hL]
    exact (hQ.differentiableAt (by simp)).hasFDerivAt
  · rw [hy', he]
    exact hQ

/-- A derivative identity between actual local surface maps forces the planar
reparameterization derivative to be bijective whenever the source is immersed. -/
theorem fderiv_bijective_of_surface_identity
    {F G : PolarPoint → E3} {H : PolarPoint → PolarPoint} {x : PolarPoint}
    (_hF : DifferentiableAt ℝ F x)
    (hG : DifferentiableAt ℝ G (H x))
    (hH : DifferentiableAt ℝ H x)
    (hidentity : F =ᶠ[𝓝 x] G ∘ H)
    (hi : Function.Injective (fderiv ℝ F x)) :
    Function.Bijective (fderiv ℝ H x) := by
  have hchain : fderiv ℝ F x = (fderiv ℝ G (H x)).comp (fderiv ℝ H x) := by
    rw [hidentity.fderiv_eq, fderiv_comp x hG hH]
  have hinj : Function.Injective (fderiv ℝ H x) := by
    intro u v huv
    apply hi
    rw [hchain]
    simp only [ContinuousLinearMap.comp_apply, huv]
  exact ⟨hinj, (LinearMap.injective_iff_surjective
    (f := (fderiv ℝ H x).toLinearMap)).mp hinj⟩

/-- The genuine local smooth reparameterization theorem. All image and chart
conditions are topological input; the reparameterization and its smoothness are
constructed by a continuous linear projection and the inverse function theorem. -/
theorem exists_smooth_local_reparametrization_of_image_germ
    {F G : PolarPoint → E3} {U V : Set PolarPoint} {a b : PolarPoint}
    (hU : IsOpen U) (ha : a ∈ U)
    (hF : ∀ x ∈ U, ContDiffAt ℝ ∞ F x)
    (hG : ∀ y ∈ V, ContDiffAt ℝ ∞ G y)
    (hFi : ∀ x ∈ U, Function.Injective (fderiv ℝ F x))
    (hGi : Function.Injective (fderiv ℝ G b))
    (hEmb : Topology.IsEmbedding (fun y : V => G y))
    (hV : IsOpen V) (hb : b ∈ V)
    (hbase : F a = G b)
    (himage : ∀ᶠ x in 𝓝 a, F x ∈ G '' V) :
    ∃ (W : Set PolarPoint) (H : PolarPoint → PolarPoint),
      IsOpen W ∧ a ∈ W ∧ W ⊆ U ∧ H a = b ∧ MapsTo H W V ∧
      (∀ x ∈ W, ContDiffAt ℝ ∞ H x) ∧
      (∀ x ∈ W, F x = G (H x)) ∧
      (∀ x ∈ W, Function.Bijective (fderiv ℝ H x)) := by
  obtain ⟨π, hπ⟩ := exists_continuousLinearMap_leftInverse (fderiv ℝ G b) hGi
  let Q : PolarPoint → PolarPoint := π ∘ G
  have hQ : ∀ y ∈ V, ContDiffAt ℝ ∞ Q y := fun y hy =>
    π.contDiff.contDiffAt.comp y (hG y hy)
  have hDQ : fderiv ℝ Q b = ContinuousLinearMap.id ℝ PolarPoint := by
    rw [show Q = π ∘ G from rfl, fderiv_comp b π.differentiableAt
      ((hG b hb).differentiableAt (by simp)), π.fderiv]
    exact hπ
  have hbij : Function.Bijective (fderiv ℝ Q b) := by
    rw [hDQ]
    exact Function.bijective_id
  obtain ⟨e, he, hbs, _, _⟩ :=
    exists_localInverse_of_fderiv_bijective (hQ b hb) (by simp) hbij
  have hDQinv : (fderiv ℝ Q b).IsInvertible := by
    refine ⟨ContinuousLinearEquiv.refl ℝ PolarPoint, ?_⟩
    exact hDQ.symm
  have hevent : ∀ᶠ y in 𝓝 b, (fderiv ℝ Q y).IsInvertible :=
    ((hQ b hb).continuousAt_fderiv (by simp)).eventually hDQinv.eventually_nhds
  obtain ⟨B, hBinv, hBo, hbB⟩ := eventually_nhds_iff.mp hevent
  let T : Set PolarPoint := V ∩ (e.source ∩ B)
  have hTo : IsOpen T := hV.inter (e.open_source.inter hBo)
  have hbT : b ∈ T := ⟨hb, hbs, hbB⟩
  have himageT : ∀ᶠ x in 𝓝 a, F x ∈ G '' T := by
    have ht := eventually_mem_image_of_embedded_chart hEmb hb hTo hbT
      (hF a ha).continuousAt hbase himage
    have hVT : V ∩ T = T := by
      ext y
      exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩
    simpa only [hVT] using ht
  let H : PolarPoint → PolarPoint := fun x => e.symm (π (F x))
  have hHof : ∀ x, F x ∈ G '' T →
      H x ∈ T ∧ F x = G (H x) := by
    intro x hx
    obtain ⟨y, hy, hgy⟩ := hx
    have hHy : H x = y := by
      change e.symm (π (F x)) = y
      rw [← hgy]
      change e.symm (Q y) = y
      rw [← he]
      exact e.left_inv hy.2.1
    exact ⟨hHy.symm ▸ hy, hHy.symm ▸ hgy.symm⟩
  have hHa : H a = b := by
    change e.symm (π (F a)) = b
    rw [hbase]
    change e.symm (Q b) = b
    rw [← he]
    exact e.left_inv hbs
  obtain ⟨W, hWsub, hWo, haW⟩ := mem_nhds_iff.mp
    (inter_mem (hU.mem_nhds ha) himageT)
  have hWU : W ⊆ U := fun x hx => (hWsub hx).1
  have hWT : ∀ x ∈ W, H x ∈ T ∧ F x = G (H x) :=
    fun x hx => hHof x (hWsub hx).2
  have hHs : ∀ x ∈ W, ContDiffAt ℝ ∞ H x := by
    intro x hx
    have hHx := (hWT x hx).1
    have hinverse := contDiffAt_projected_inverse e he hHx.2.1
      (hQ (H x) hHx.1) (hBinv (H x) hHx.2.2)
    have harg : Q (H x) = π (F x) := by
      change π (G (H x)) = π (F x)
      rw [← (hWT x hx).2]
    rw [harg] at hinverse
    exact hinverse.comp x (π.contDiff.contDiffAt.comp x (hF x (hWU hx)))
  refine ⟨W, H, hWo, haW, hWU, hHa, fun x hx => (hWT x hx).1.1,
    hHs, fun x hx => (hWT x hx).2, ?_⟩
  intro x hx
  apply fderiv_bijective_of_surface_identity
    ((hF x (hWU hx)).differentiableAt (by simp))
    ((hG (H x) (hWT x hx).1.1).differentiableAt (by simp))
    ((hHs x hx).differentiableAt (by simp))
    (Filter.eventuallyEq_iff_exists_mem.mpr ⟨W, hWo.mem_nhds hx,
      fun y hy => (hWT y hy).2⟩)
    (hFi x (hWU hx))

/-- Actual local smoothness under an ambient affine isometry. -/
theorem contDiffAt_affineSurfaceMap (A : E3 ≃ᵃⁱ[ℝ] E3)
    {F : PolarPoint → E3} {x : PolarPoint}
    (hF : ContDiffAt ℝ ∞ F x) :
    ContDiffAt ℝ ∞ (fun y => A (F y)) x := by
  rw [affineSurfaceMap_eq_rigidSurfaceMap]
  change ContDiffAt ℝ ∞ (fun y => A.linearIsometryEquiv (F y) + A 0) x
  have hL : ContDiff ℝ ∞ (A.linearIsometryEquiv : E3 → E3) :=
    A.linearIsometryEquiv.contDiff
  exact (hL.contDiffAt.comp x hF).add contDiffAt_const

theorem fderiv_affineSurfaceMap (A : E3 ≃ᵃⁱ[ℝ] E3)
    {F : PolarPoint → E3} {x : PolarPoint}
    (hF : DifferentiableAt ℝ F x) :
    fderiv ℝ (fun y => A (F y)) x =
      (A.linearIsometryEquiv : E3 →L[ℝ] E3).comp (fderiv ℝ F x) := by
  rw [affineSurfaceMap_eq_rigidSurfaceMap]
  exact fderiv_rigidSurfaceMap _ _ hF

/-- Ambient image congruence is used only through genuine local image membership.
The target chart embedding selects a branch and the inverse function theorem
constructs the smooth reparameterization. -/
theorem exists_smooth_local_reparametrization
    (A : E3 ≃ᵃⁱ[ℝ] E3)
    {F G : PolarPoint → E3} {U V : Set PolarPoint} {a b : PolarPoint}
    (hU : IsOpen U) (ha : a ∈ U)
    (hF : ∀ x ∈ U, ContDiffAt ℝ ∞ F x)
    (hG : ∀ y ∈ V, ContDiffAt ℝ ∞ G y)
    (hFi : ∀ x ∈ U, Function.Injective (fderiv ℝ F x))
    (hGi : Function.Injective (fderiv ℝ G b))
    (hEmb : Topology.IsEmbedding (fun y : V => G y))
    (hV : IsOpen V) (hb : b ∈ V)
    (hbase : A (F a) = G b)
    (himage : ∀ᶠ x in 𝓝 a, A (F x) ∈ G '' V) :
    ∃ (W : Set PolarPoint) (H : PolarPoint → PolarPoint),
      IsOpen W ∧ a ∈ W ∧ W ⊆ U ∧ H a = b ∧ MapsTo H W V ∧
      (∀ x ∈ W, ContDiffAt ℝ ∞ H x) ∧
      (∀ x ∈ W, A (F x) = G (H x)) ∧
      (∀ x ∈ W, Function.Bijective (fderiv ℝ H x)) := by
  apply exists_smooth_local_reparametrization_of_image_germ hU ha
    (fun x hx => contDiffAt_affineSurfaceMap A (hF x hx)) hG
    (fun x hx => ?_) hGi hEmb hV hb hbase himage
  rw [fderiv_affineSurfaceMap A ((hF x hx).differentiableAt (by simp))]
  exact A.linearIsometryEquiv.injective.comp (hFi x hx)

/-- Pointwise germ version, convenient for the actual first and second derivative
chain rules in the surface geometry interface. -/
theorem exists_smooth_local_reparametrization_germ
    (A : E3 ≃ᵃⁱ[ℝ] E3)
    {F G : PolarPoint → E3} {U V : Set PolarPoint} {a b : PolarPoint}
    (hU : IsOpen U) (ha : a ∈ U)
    (hF : ∀ x ∈ U, ContDiffAt ℝ ∞ F x)
    (hG : ∀ y ∈ V, ContDiffAt ℝ ∞ G y)
    (hFi : ∀ x ∈ U, Function.Injective (fderiv ℝ F x))
    (hGi : Function.Injective (fderiv ℝ G b))
    (hEmb : Topology.IsEmbedding (fun y : V => G y))
    (hV : IsOpen V) (hb : b ∈ V)
    (hbase : A (F a) = G b)
    (himage : ∀ᶠ x in 𝓝 a, A (F x) ∈ G '' V) :
    ∃ H : PolarPoint → PolarPoint, H a = b ∧ ContDiffAt ℝ ∞ H a ∧
      (fun x => A (F x)) =ᶠ[𝓝 a] G ∘ H ∧
      Function.Bijective (fderiv ℝ H a) := by
  obtain ⟨W, H, hWo, haW, _, hHa, _, hHs, heq, hHi⟩ :=
    exists_smooth_local_reparametrization A hU ha hF hG hFi hGi hEmb hV hb hbase himage
  refine ⟨H, hHa, hHs a haW, ?_, hHi a haW⟩
  filter_upwards [hWo.mem_nhds haW] with x hx
  exact heq x hx

/-- The actual first derivative identity of an ambient image reparameterization. -/
theorem fderiv_surface_reparametrization
    (A : E3 ≃ᵃⁱ[ℝ] E3)
    {F G : PolarPoint → E3} {H : PolarPoint → PolarPoint} {x : PolarPoint}
    (hF : DifferentiableAt ℝ F x)
    (hG : DifferentiableAt ℝ G (H x))
    (hH : DifferentiableAt ℝ H x)
    (heq : (fun y => A (F y)) =ᶠ[𝓝 x] G ∘ H) :
    (fderiv ℝ G (H x)).comp (fderiv ℝ H x) =
      (A.linearIsometryEquiv : E3 →L[ℝ] E3).comp (fderiv ℝ F x) := by
  rw [← fderiv_affineSurfaceMap A hF, heq.fderiv_eq, fderiv_comp x hG hH]

/-- Normal transport is a conclusion of the actual differential identity and
surjectivity of the reparameterization differential, rather than a hypothesis. -/
theorem IsUnitSurfaceNormal.of_affine_reparametrization
    (A : E3 ≃ᵃⁱ[ℝ] E3)
    {F G : PolarPoint → E3} {H : PolarPoint → PolarPoint}
    {x : PolarPoint} {N : E3}
    (hN : IsUnitSurfaceNormal F x N)
    (hF : DifferentiableAt ℝ F x)
    (hG : DifferentiableAt ℝ G (H x))
    (hH : DifferentiableAt ℝ H x)
    (heq : (fun y => A (F y)) =ᶠ[𝓝 x] G ∘ H)
    (hsurj : Function.Surjective (fderiv ℝ H x)) :
    IsUnitSurfaceNormal G (H x) (A.linearIsometryEquiv N) := by
  refine ⟨by simpa only [LinearIsometryEquiv.norm_map] using hN.1, ?_⟩
  intro v
  obtain ⟨u, rfl⟩ := hsurj v
  have hd := DFunLike.congr_fun (fderiv_surface_reparametrization A hF hG hH heq) u
  change fderiv ℝ G (H x) (fderiv ℝ H x u) =
    A.linearIsometryEquiv (fderiv ℝ F x u) at hd
  rw [hd, A.linearIsometryEquiv.inner_map_map]
  exact hN.2 u

/-- Curvature definitions depend only on a genuine second-order surface germ. -/
theorem surfaceShapeMatrix_congr_germ
    {F G : PolarPoint → E3} {x : PolarPoint} (heq : F =ᶠ[𝓝 x] G) (N : E3) :
    surfaceShapeMatrix F N x = surfaceShapeMatrix G N x := by
  have hfirst : fderiv ℝ F x = fderiv ℝ G x := heq.fderiv_eq
  have hsecond : fderiv ℝ (fderiv ℝ F) x = fderiv ℝ (fderiv ℝ G) x :=
    heq.fderiv.fderiv_eq
  have hI : surfaceGram F x = surfaceGram G x := by
    ext i j
    simp only [surfaceGram, surfaceFirstForm, hfirst]
  have hII : surfaceSecondMatrix F N x = surfaceSecondMatrix G N x := by
    ext i j
    simp only [surfaceSecondMatrix, surfaceSecondForm, hsecond]
  simp only [surfaceShapeMatrix, hI, hII]

theorem surfaceGaussianCurvature_congr_germ
    {F G : PolarPoint → E3} {x : PolarPoint} (heq : F =ᶠ[𝓝 x] G) (N : E3) :
    surfaceGaussianCurvature F N x = surfaceGaussianCurvature G N x := by
  rw [surfaceGaussianCurvature, surfaceGaussianCurvature, surfaceShapeMatrix_congr_germ heq]

theorem surfaceMeanCurvature_congr_germ
    {F G : PolarPoint → E3} {x : PolarPoint} (heq : F =ᶠ[𝓝 x] G) (N : E3) :
    surfaceMeanCurvature F N x = surfaceMeanCurvature G N x := by
  rw [surfaceMeanCurvature, surfaceMeanCurvature, surfaceShapeMatrix_congr_germ heq]

end ContinuousFlexibility
