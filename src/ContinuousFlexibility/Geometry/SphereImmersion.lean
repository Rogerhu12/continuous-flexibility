module

public import ContinuousFlexibility.Geometry.SphereCapGluing
public import Mathlib.Geometry.Manifold.SmoothEmbedding
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-!
# Genuine immersion normal forms for the constructed standard spheres

The inverse function theorem supplies actual ambient coordinate charts in which
the map is the linear inclusion of a plane.  This proves mathlib's normal-form
`Manifold.IsImmersion`, in addition to the previously proved injectivity of the
manifold differential.  The complement is the same real line at every point.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility

open Set Function ChartedSpace
open scoped ContDiff Manifold Topology

local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "SpherePoint" => {v : E3 // v ∈ Metric.sphere (0 : E3) 1}

local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp [E3]⟩

set_option backward.isDefEq.respectTransparency false

/-- Complete an injective plane differential by one actual complementary line. -/
private theorem exists_plane_complement (D : E2 →L[ℝ] E3) (hD : Injective D) :
    ∃ e : (E2 × ℝ) ≃L[ℝ] E3, ∀ u : E2, e (u, 0) = D u := by
  obtain ⟨Q, hQ⟩ := D.range.exists_isCompl
  let r : E2 ≃ₗ[ℝ] D.range := LinearEquiv.ofInjective D.toLinearMap hD
  have hdim : Module.finrank ℝ Q = 1 := by
    have hr : Module.finrank ℝ D.range = 2 := by
      rw [← r.finrank_eq]
      simp
    have hs : 2 + Module.finrank ℝ Q = 3 := by
      rw [← hr, Submodule.finrank_add_eq_of_isCompl hQ]
      simp [E3]
    omega
  let q : ℝ ≃ₗ[ℝ] Q := LinearEquiv.ofFinrankEq ℝ Q (by simpa using hdim.symm)
  let e : (E2 × ℝ) ≃L[ℝ] E3 :=
    ((r.prodCongr q).trans (D.range.prodEquivOfIsCompl Q hQ)).toContinuousLinearEquiv
  refine ⟨e, ?_⟩
  intro u
  change (r u : E3) + (q 0 : E3) = D u
  simp [r]

/-- A globally smooth map with invertible derivative has a genuinely smooth
local inverse on an open neighborhood, at smooth order `∞`. -/
private theorem smooth_local_coordinates
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} (hf : ContDiff ℝ ∞ f) (a : E) (e : E ≃L[ℝ] F)
    (hder : HasFDerivAt f (e : E →L[ℝ] F) a) :
    ∃ c : OpenPartialHomeomorph E F,
      (c : E → F) = f ∧ a ∈ c.source ∧
      ContDiffOn ℝ ∞ c c.source ∧ ContDiffOn ℝ ∞ c.symm c.target := by
  have hn : {z : E | ∃ v : E ≃L[ℝ] F, (v : E →L[ℝ] F) = fderiv ℝ f z} ∈ 𝓝 a := by
    have he := e.nhds
    rw [← hder.fderiv] at he
    exact (hf.continuous_fderiv (by simp)).continuousAt.preimage_mem_nhds he
  obtain ⟨U, hU, hUopen, haU⟩ := mem_nhds_iff.mp hn
  let c₀ := hf.contDiffAt.toOpenPartialHomeomorph f hder (by simp)
  let c := c₀.restr U
  have hc : (c : E → F) = f := rfl
  have ha : a ∈ c.source := by
    rw [OpenPartialHomeomorph.restr_source' _ _ hUopen]
    exact ⟨hf.contDiffAt.mem_toOpenPartialHomeomorph_source hder (by simp), haU⟩
  refine ⟨c, hc, ha, hc ▸ hf.contDiffOn, ?_⟩
  intro y hy
  have hyU : c.symm y ∈ U := by
    have hm := c.map_target hy
    rw [OpenPartialHomeomorph.restr_source' _ _ hUopen] at hm
    exact hm.2
  obtain ⟨v, hv⟩ := hU hyU
  have hd : HasFDerivAt c (v : E →L[ℝ] F) (c.symm y) := by
    rw [hc, hv]
    exact (hf.differentiable (by simp) _).hasFDerivAt
  exact (c.contDiffAt_symm hy hd (hc ▸ hf.contDiffAt)).contDiffWithinAt

/-- The normal-form construction in any chart with a globally smooth inverse.
The hypotheses are actual smoothness and the actual derivative's injectivity. -/
private theorem immersionAt_of_global_chart
    {M : Type*} [TopologicalSpace M] [ChartedSpace E2 M] [IsManifold (𝓡 2) ∞ M]
    {f : M → E3} (d : OpenPartialHomeomorph M E2)
    (hd : d ∈ IsManifold.maximalAtlas (𝓡 2) ∞ M)
    (hg : ContDiff ℝ ∞ (f ∘ d.symm)) (x : M) (hx : x ∈ d.source)
    (hi : Injective (fderiv ℝ (f ∘ d.symm) (d x))) :
    Manifold.IsImmersionAtOfComplement ℝ (𝓡 2) 𝓘(ℝ, E3) ∞ f x := by
  let g : E2 → E3 := f ∘ d.symm
  obtain ⟨e, he⟩ := exists_plane_complement (fderiv ℝ g (d x)) hi
  let H : E2 × ℝ → E3 := fun p => g p.1 + e (0, p.2)
  have hH : ContDiff ℝ ∞ H := by
    exact (hg.comp contDiff_fst).add
      (e.contDiff.comp (contDiff_const.prodMk contDiff_snd))
  have hHe : HasFDerivAt H (e : (E2 × ℝ) →L[ℝ] E3) (d x, 0) := by
    have h := ((hg.differentiable (by simp) (d x)).hasFDerivAt.comp (d x, 0)
      (hasFDerivAt_fst (p := (d x, (0 : ℝ))))).add
      (e.hasFDerivAt.comp (d x, 0)
        ((hasFDerivAt_const (0 : E2) (d x, (0 : ℝ))).prodMk
          (hasFDerivAt_snd (p := (d x, (0 : ℝ))))))
    convert h using 1
    · rfl
    · apply ContinuousLinearMap.ext
      intro p
      change e p = fderiv ℝ g (d x) p.1 + e (0, p.2)
      rw [← he]
      rw [← map_add]
      congr 1
      simp
  obtain ⟨c, hc, hxc, hcs, hct⟩ := smooth_local_coordinates hH (d x, 0) e hHe
  let U : Set E2 := {u | (u, (0 : ℝ)) ∈ c.source}
  have hU : IsOpen U := c.open_source.preimage (continuous_id.prodMk continuous_const)
  let V : Set M := d.source ∩ d ⁻¹' U
  have hV : IsOpen V := d.isOpen_inter_preimage hU
  let a := d.restr V
  let b := c.symm.trans e.toHomeomorph.toOpenPartialHomeomorph
  have hax : x ∈ a.source := by
    rw [OpenPartialHomeomorph.restr_source' _ _ hV]
    exact ⟨hx, hx, hxc⟩
  have hbfx : f x ∈ b.source := by
    have hh : H (d x, 0) = f x := by simp [H, g, d.left_inv hx]
    have hctarget : f x ∈ c.target := by rw [← hh, ← hc]; exact c.map_source hxc
    exact ⟨hctarget, Set.mem_univ _⟩
  have haAtlas : a ∈ IsManifold.maximalAtlas (𝓡 2) ∞ M :=
    restr_mem_maximalAtlas (contDiffGroupoid ∞ (𝓡 2)) hd hV
  have hbAtlas : b ∈ IsManifold.maximalAtlas 𝓘(ℝ, E3) ∞ E3 := by
    apply b.mem_maximalAtlas_of_contMDiffOn
    · apply ContDiffOn.contMDiffOn
      exact e.contDiff.comp_contDiffOn (hct.mono fun _ hy => hy.1)
    · apply ContDiffOn.contMDiffOn
      exact hcs.comp e.symm.contDiff.contDiffOn (fun _ hy => hy.2)
  refine Manifold.IsImmersionAtOfComplement.mk_of_charts e a b hax hbfx haAtlas hbAtlas ?_ ?_
  · intro y hy
    rw [OpenPartialHomeomorph.restr_source' _ _ hV] at hy
    have hcy : (d y, (0 : ℝ)) ∈ c.source := hy.2.2
    have heq : c (d y, 0) = f y := by rw [hc]; simp [H, g, d.left_inv hy.1]
    exact ⟨heq ▸ c.map_source hcy, Set.mem_univ _⟩
  · intro u hu
    have hua : u ∈ a.target := by simpa only [OpenPartialHomeomorph.extend_target,
      modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, range_id,
      preimage_id, inter_univ] using hu
    have hsrc := a.map_target hua
    rw [OpenPartialHomeomorph.restr_source' _ _ hV] at hsrc
    have hdu : d (d.symm u) = u := a.right_inv hua
    have hcu : (u, (0 : ℝ)) ∈ c.source := by
      have ht : (d (d.symm u), (0 : ℝ)) ∈ c.source := hsrc.2.2
      simpa only [hdu] using ht
    have heq : c (u, 0) = f (d.symm u) := by rw [hc]; simp [H, g]
    change e (c.symm (f (d.symm u))) = e (u, 0)
    rw [← heq, c.left_inv hcu]

/-- Transfer the explicit stereographic coordinates to the library's Euclidean
two-dimensional model, preserving their globally smooth inverse. -/
private theorem sphere_model_chart
    (p : OpenPartialHomeomorph SpherePoint PolarPoint)
    (hp : ContMDiffOn (𝓡 2) 𝓘(ℝ, PolarPoint) ∞ p p.source)
    (hp' : ContMDiff 𝓘(ℝ, PolarPoint) (𝓡 2) ∞ p.symm)
    (x : SpherePoint) (hx : x ∈ p.source) :
    ∃ d : OpenPartialHomeomorph SpherePoint E2,
      x ∈ d.source ∧ d ∈ IsManifold.maximalAtlas (𝓡 2) ∞ SpherePoint ∧
      ContMDiff (𝓡 2) (𝓡 2) ∞ d.symm := by
  let e : PolarPoint ≃L[ℝ] E2 := ContinuousLinearEquiv.ofFinrankEq (by simp [PolarPoint])
  let d := p.trans e.toHomeomorph.toOpenPartialHomeomorph
  have hback : ContMDiff (𝓡 2) (𝓡 2) ∞ d.symm :=
    hp'.comp e.symm.contDiff.contMDiff
  refine ⟨d, ⟨hx, Set.mem_univ _⟩, ?_, hback⟩
  apply d.mem_maximalAtlas_of_contMDiffOn
  · exact e.contDiff.contMDiff.comp_contMDiffOn (hp.mono fun _ hy => hy.1)
  · exact hback.contMDiffOn

private theorem exists_sphere_model_chart (x : SpherePoint) :
    ∃ d : OpenPartialHomeomorph SpherePoint E2,
      x ∈ d.source ∧ d ∈ IsManifold.maximalAtlas (𝓡 2) ∞ SpherePoint ∧
      ContMDiff (𝓡 2) (𝓡 2) ∞ d.symm := by
  by_cases hn : x ∈ sphereNorthSource
  · exact sphere_model_chart sphereNorthCoordinates
      (fun y hy => (contMDiffAt_sphereNorthChart y hy).contMDiffWithinAt)
      contMDiff_sphereNorthInverse x hn
  · have hs : x ∈ sphereSouthSource := by
      change (x : E3) 2 ≠ 1
      have hz : (x : E3) 2 = -1 := by simpa only [sphereNorthSource, mem_ofPred_eq, not_not] using hn
      rw [hz]
      norm_num
    exact sphere_model_chart sphereSouthCoordinates
      (fun y hy => (contMDiffAt_sphereSouthChart y hy).contMDiffWithinAt)
      contMDiff_sphereSouthInverse x hs

/-- On the actual standard sphere, smoothness and an injective manifold
differential imply the library's genuine immersion normal form. -/
theorem isImmersion_sphere_of_mfderiv_injective {f : SpherePoint → E3}
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ f)
    (hi : ∀ x, Injective (mfderiv (𝓡 2) 𝓘(ℝ, E3) f x)) :
    Manifold.IsImmersion (𝓡 2) 𝓘(ℝ, E3) ∞ f := by
  apply Manifold.IsImmersionOfComplement.isImmersion (F := ℝ)
  intro x
  obtain ⟨d, hx, hd, hd'⟩ := exists_sphere_model_chart x
  have hg : ContDiff ℝ ∞ (f ∘ d.symm) := (hf.comp hd').contDiff
  have hdm : d.MDifferentiable (𝓡 2) (𝓡 2) := by
    constructor
    · exact (contMDiffOn_of_mem_maximalAtlas hd).mdifferentiableOn (by simp)
    · exact (hd'.mdifferentiable (by simp)).mdifferentiableOn
  have him : Injective (mfderiv (𝓡 2) 𝓘(ℝ, E3) (f ∘ d.symm) (d x)) := by
    rw [mfderiv_comp _ ((hf _).mdifferentiableAt (by simp))
      ((hd' _).mdifferentiableAt (by simp))]
    exact (hi _).comp (hdm.symm.mfderiv_injective (d.map_source hx))
  have hig : Injective (fderiv ℝ (f ∘ d.symm) (d x)) := by
    rw [mfderiv_eq_fderiv] at him
    intro u v huv
    apply (NormedSpace.fromTangentSpace (𝕜 := ℝ) (d x)).symm.injective
    apply him
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply] using
      congrArg (NormedSpace.fromTangentSpace (𝕜 := ℝ) ((f ∘ d.symm) (d x))).symm huv
  exact immersionAt_of_global_chart d hd hg x hx hig

theorem isSmoothEmbedding_sphere_of_mfderiv_injective {f : SpherePoint → E3}
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ f)
    (hi : ∀ x, Injective (mfderiv (𝓡 2) 𝓘(ℝ, E3) f x))
    (he : Topology.IsEmbedding f) :
    Manifold.IsSmoothEmbedding (𝓡 2) 𝓘(ℝ, E3) ∞ f :=
  ⟨isImmersion_sphere_of_mfderiv_injective hf hi, he⟩

/-- Every phase of the actual marked family is an immersion in normal-form
coordinates, including the equator and both poles. -/
theorem IsometricGraphDevelopment.markedSphereFamily_isImmersion {A : FlatAnnularCore}
    (D : IsometricGraphDevelopment A) {R L k ρ : ℝ}
    (hR : A.b < R) (hL : 0 < L) (hk : 0 ≤ k) (hρ : 0 < ρ) (hsmall : ρ < L / 64)
    (t : ℝ) : Manifold.IsImmersion (𝓡 2) 𝓘(ℝ, E3) ∞ (fun x : SpherePoint =>
      sphereGraphCapFamily D (markedCapMap R A.cRight L k ρ) R L (x, t)) := by
  apply isImmersion_sphere_of_mfderiv_injective
  · exact (D.contMDiff_markedSphereFamily hR hL hρ hsmall).comp
      (contMDiff_id.prodMk contMDiff_const)
  · exact D.markedSphereFamily_mfderiv_injective hR hL hk hρ hsmall t

/-- The same cap length gives the actual jointly smooth sphere family with
genuine smooth embeddings at every phase, for all admissible marker parameters. -/
theorem IsometricGraphDevelopment.exists_markedSphereFamily_smoothEmbedding
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) {R : ℝ} (hR : A.b < R) :
    ∃ L : ℝ, 0 < L ∧ ∀ k ρ : ℝ, 0 ≤ k → 0 < ρ → ρ < L / 64 →
      ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E3) ∞
        (sphereGraphCapFamily D (markedCapMap R A.cRight L k ρ) R L) ∧
      ∀ t : ℝ, Manifold.IsSmoothEmbedding (𝓡 2) 𝓘(ℝ, E3) ∞ (fun x : SpherePoint =>
        sphereGraphCapFamily D (markedCapMap R A.cRight L k ρ) R L (x, t)) := by
  obtain ⟨L, hL, hfamily⟩ := D.exists_markedSphereFamily_regular hR
  refine ⟨L, hL, ?_⟩
  intro k ρ hk hρ hsmall
  obtain ⟨hsm, hem⟩ := hfamily k ρ hk hρ hsmall
  refine ⟨hsm, ?_⟩
  intro t
  exact ⟨D.markedSphereFamily_isImmersion hR hL hk hρ hsmall t, (hem t).1⟩

end ContinuousFlexibility
