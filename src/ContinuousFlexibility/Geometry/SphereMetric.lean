module

public import ContinuousFlexibility.Geometry.SphereCapGluing
public import ContinuousFlexibility.Geometry.SphereImmersion
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-!
# The actual pullback metric of the constructed sphere family

All forms below use the genuine vector-valued manifold differential into E3.
The north-side formula is the proved graph pullback tensor; the south-side
germ is phase independent. No chord-distance isometry is substituted for it.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility

open Filter Set Bundle
open scoped ContDiff Manifold Topology

local notation "SpherePoint" => {v : E3 // v ∈ Metric.sphere (0 : E3) 1}
local notation "SphereModel" => EuclideanSpace ℝ (Fin 2)
local notation "TSphere" => (fun x : SpherePoint => TangentSpace (𝓡 2) x)

set_option backward.isDefEq.respectTransparency false

local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp [E3]⟩

def spherePullbackForm (F : SpherePoint → E3) (x : SpherePoint) :
    TangentSpace (𝓡 2) x →L[ℝ] TangentSpace (𝓡 2) x →L[ℝ] ℝ :=
  ((mvfderiv (𝓡 2) F x).precomp ℝ).comp
    ((innerSL ℝ (E := E3)).comp (mvfderiv (𝓡 2) F x))

@[simp] theorem spherePullbackForm_apply (F : SpherePoint → E3) (x : SpherePoint)
    (v w : TangentSpace (𝓡 2) x) :
    spherePullbackForm F x v w =
      inner ℝ (mvfderiv (𝓡 2) F x v) (mvfderiv (𝓡 2) F x w) := rfl

theorem spherePullbackForm_symm (F : SpherePoint → E3) (x : SpherePoint)
    (v w : TangentSpace (𝓡 2) x) :
    spherePullbackForm F x v w = spherePullbackForm F x w v := by
  rw [spherePullbackForm_apply, spherePullbackForm_apply]
  exact real_inner_comm _ _

theorem spherePullbackForm_pos {F : SpherePoint → E3} {x : SpherePoint}
    (hi : Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, E3) F x))
    (v : TangentSpace (𝓡 2) x) (hv : v ≠ 0) : 0 < spherePullbackForm F x v v := by
  rw [spherePullbackForm_apply]
  have hvi : Function.Injective (mvfderiv (𝓡 2) F x) :=
    (NormedSpace.fromTangentSpace (𝕜 := ℝ) (F x)).injective.comp hi
  apply real_inner_self_pos.mpr
  intro hzero
  apply hv
  apply hvi
  simpa only [map_zero] using hzero

theorem spherePullbackForm_isVonNBounded {F : SpherePoint → E3} {x : SpherePoint}
    (hi : Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, E3) F x)) :
    Bornology.IsVonNBounded ℝ {v : TangentSpace (𝓡 2) x | spherePullbackForm F x v v < 1} := by
  let d := mvfderiv (𝓡 2) F x
  have hd : Function.Injective d :=
    (NormedSpace.fromTangentSpace (𝕜 := ℝ) (F x)).injective.comp hi
  let : FiniteDimensional ℝ (TangentSpace (𝓡 2) x) :=
    FiniteDimensional.of_injective d.toLinearMap hd
  have he : Topology.IsClosedEmbedding d :=
    LinearMap.isClosedEmbedding_of_injective (f := d.toLinearMap) (LinearMap.ker_eq_bot.mpr hd)
  have hc : IsCompact (d ⁻¹' Metric.closedBall (0 : E3) 1) :=
    he.isCompact_preimage (isCompact_closedBall _ _)
  apply Bornology.IsVonNBounded.subset (s₂ := d ⁻¹' Metric.closedBall (0 : E3) 1) ?_
    (hc.isVonNBounded ℝ)
  intro v hv
  change spherePullbackForm F x v v < 1 at hv
  rw [spherePullbackForm_apply, real_inner_self_eq_norm_sq] at hv
  change ‖d v‖ ^ 2 < 1 at hv
  simp only [mem_preimage, Metric.mem_closedBall, dist_zero_right]
  nlinarith [norm_nonneg (d v)]

theorem spherePullbackForm_contMDiff {F : SpherePoint → E3}
    (hF : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ F) :
    ContMDiff (𝓡 2) ((𝓡 2).prod 𝓘(ℝ, SphereModel →L[ℝ] SphereModel →L[ℝ] ℝ)) ∞
      (fun x => Bundle.TotalSpace.mk' (SphereModel →L[ℝ] SphereModel →L[ℝ] ℝ)
        x (spherePullbackForm F x)) := by
  intro x0
  rw [contMDiffAt_section]
  let e := trivializationAt SphereModel TSphere x0
  let A : SpherePoint → SphereModel →L[ℝ] E3 :=
    fun x => (mvfderiv (𝓡 2) F x).comp (e.symmL ℝ x)
  have hAEq : inTangentCoordinates (𝓡 2) 𝓘(ℝ, E3) id F
      (mfderiv (𝓡 2) 𝓘(ℝ, E3) F) x0 = A := by
    funext x
    dsimp only [inTangentCoordinates, ContinuousLinearMap.inCoordinates, id_eq]
    rw [TangentBundle.continuousLinearMapAt_model_space]
    ext v
    rfl
  have hA : ContMDiffAt (𝓡 2) 𝓘(ℝ, SphereModel →L[ℝ] E3) ∞ A x0 := by
    have hd := (hF x0).mfderiv_const (m := ∞) (by simp)
    rw [hAEq] at hd
    exact hd
  let I : E3 →L[ℝ] E3 →L[ℝ] ℝ := innerSL ℝ (E := E3)
  let B : SpherePoint → SphereModel →L[ℝ] SphereModel →L[ℝ] ℝ :=
    fun x => ((A x).precomp ℝ).comp (I.comp (A x))
  have hi : ContMDiffAt (𝓡 2) 𝓘(ℝ, E3 →L[ℝ] E3 →L[ℝ] ℝ) ∞
      (fun _ : SpherePoint => I) x0 := contMDiffAt_const
  have hB : ContMDiffAt (𝓡 2) 𝓘(ℝ, SphereModel →L[ℝ] SphereModel →L[ℝ] ℝ) ∞ B x0 :=
    (hA.clm_precomp (F₃ := ℝ)).clm_comp (hi.clm_comp hA)
  apply hB.congr_of_eventuallyEq
  have hn : e.baseSet ∈ 𝓝 x0 :=
    e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt SphereModel TSphere x0)
  filter_upwards [hn] with x hx
  rw [hom_trivializationAt_apply]
  ext v w
  have hxr : x ∈ (trivializationAt ℝ (Bundle.Trivial SpherePoint ℝ) x0).baseSet :=
    Set.mem_univ x
  rw [inCoordinates_apply_eq₂ hx hx hxr]
  have hlin :
      (trivializationAt ℝ (Bundle.Trivial SpherePoint ℝ) x0).linearMapAt ℝ x = LinearMap.id :=
    Bundle.Trivial.linearMapAt_trivialization ℝ SpherePoint ℝ x
  rw [hlin, LinearMap.id_apply, spherePullbackForm_apply]
  change inner ℝ
      (mvfderiv (𝓡 2) F x (e.symm x v)) (mvfderiv (𝓡 2) F x (e.symm x w)) =
    inner ℝ
      (mvfderiv (𝓡 2) F x (e.symmL ℝ x v)) (mvfderiv (𝓡 2) F x (e.symmL ℝ x w))
  simp only [e.symmL_apply hx]

/-- The genuine smooth positive-definite pullback metric, with the existing
topology on each tangent fiber. -/
def spherePullbackRiemannianMetric {F : SpherePoint → E3}
    (hF : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ F)
    (hi : ∀ x : SpherePoint, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, E3) F x)) :
    Bundle.ContMDiffRiemannianMetric (𝓡 2) ∞ SphereModel TSphere where
  inner := spherePullbackForm F
  symm := spherePullbackForm_symm F
  pos x v hv := spherePullbackForm_pos (hi x) v hv
  isVonNBounded x := spherePullbackForm_isVonNBounded (hi x)
  contMDiff := spherePullbackForm_contMDiff hF

theorem sphere_mvfderiv_congr {F G : SpherePoint → E3} {x : SpherePoint}
    (he : F =ᶠ[𝓝 x] G) : mvfderiv (𝓡 2) F x = mvfderiv (𝓡 2) G x := by
  unfold mvfderiv
  rw [he.mfderiv_eq (I := 𝓡 2) (I' := 𝓘(ℝ, E3))]
  rfl

theorem sphere_mvfderiv_comp {φ : SpherePoint → PolarPoint} {F : PolarPoint → E3}
    (x : SpherePoint) (hF : DifferentiableAt ℝ F (φ x))
    (hφ : MDifferentiableAt (𝓡 2) 𝓘(ℝ, PolarPoint) φ x) :
    mvfderiv (𝓡 2) (F ∘ φ) x =
      (fderiv ℝ F (φ x)).comp (mvfderiv (𝓡 2) φ x) := by
  rw [mvfderiv_comp x hF.mdifferentiableAt hφ, mvfderiv_eq_fderiv]
  rfl

def sphereNorthPlanarMap (R : ℝ) (x : SpherePoint) : PolarPoint := R • sphereNorthChart x

theorem contMDiffAt_sphereNorthPlanarMap (R : ℝ) (x : SpherePoint)
    (hx : x ∈ sphereNorthSource) :
    ContMDiffAt (𝓡 2) 𝓘(ℝ, PolarPoint) ∞ (sphereNorthPlanarMap R) x := by
  have hr : ContDiff ℝ ∞ (fun _ : PolarPoint => R) := contDiff_const
  have hs : ContDiff ℝ ∞ (fun u : PolarPoint => R • u) := hr.smul contDiff_id
  have hm : ContMDiffAt 𝓘(ℝ, PolarPoint) 𝓘(ℝ, PolarPoint) ∞
      (fun u : PolarPoint => R • u) (sphereNorthChart x) := hs.contDiffAt.contMDiffAt
  change ContMDiffAt (𝓡 2) 𝓘(ℝ, PolarPoint) ∞
    (fun y : SpherePoint => R • sphereNorthChart y) x
  simpa only [Function.comp_def] using hm.comp x (contMDiffAt_sphereNorthChart x hx)

def sphereFamilyForm {A : FlatAnnularCore} (D : IsometricGraphDevelopment A)
    (C : PolarPoint → E3) (R L t : ℝ) (x : SpherePoint) :
    TangentSpace (𝓡 2) x →L[ℝ] TangentSpace (𝓡 2) x →L[ℝ] ℝ :=
  spherePullbackForm (fun y : SpherePoint => sphereGraphCapFamily D C R L (y, t)) x

theorem sphereFamilyForm_phase_invariant {A : FlatAnnularCore}
    (D : IsometricGraphDevelopment A) {C : PolarPoint → E3} {R L : ℝ}
    (hR : A.b < R)
    (hcollar : ∀ y : PolarPoint, cartesianRadius y = 1 →
      (C ∘ capSphereRadialMap (capSphereRatio R L)) =ᶠ[𝓝 y]
        fun z => graphMap id (fun _ => A.cRight) ((R / cartesianRadius z ^ 2) • z))
    (t : ℝ) (x : SpherePoint) :
    sphereFamilyForm D C R L t x = sphereFamilyForm D C R L 0 x := by
  have hslice (s : ℝ) : Tendsto (fun y : SpherePoint => (y, s)) (𝓝 x) (𝓝 (x, s)) :=
    (continuousAt_id.prodMk continuousAt_const).tendsto
  by_cases hx : 0 ≤ (x : E3) 2
  · have hnx : x ∈ sphereNorthSource := by change (x : E3) 2 ≠ -1; linarith
    have hφ := (contMDiffAt_sphereNorthPlanarMap R x hnx).mdifferentiableAt (by simp)
    have hd (s : ℝ) :
        mvfderiv (𝓡 2) (fun y : SpherePoint => sphereGraphCapFamily D C R L (y, s)) x =
          (fderiv ℝ (D.rotationFamily s) (sphereNorthPlanarMap R x)).comp
            (mvfderiv (𝓡 2) (sphereNorthPlanarMap R) x) := by
      have he : (fun y : SpherePoint => sphereGraphCapFamily D C R L (y, s)) =ᶠ[𝓝 x]
          (D.rotationFamily s ∘ sphereNorthPlanarMap R) := by
        simpa only [Function.comp_def, sphereNorthFamily, sphereNorthPlanarMap] using
          (sphereGraphCapFamily_north_germ D hR hcollar (x, s) hx).comp_tendsto (hslice s)
      rw [sphere_mvfderiv_congr he]
      exact sphere_mvfderiv_comp x ((D.rotationFamily_smooth s).differentiable (by simp) _) hφ
    ext v w
    simp only [sphereFamilyForm, spherePullbackForm_apply]
    rw [hd t, hd 0]
    simp only [ContinuousLinearMap.comp_apply]
    rw [D.rotationFamily_metric, D.rotationFamily_metric]
  · have he (s : ℝ) :
        (fun y : SpherePoint => sphereGraphCapFamily D C R L (y, s)) =ᶠ[𝓝 x]
          sphereSouthCap C R L := by
      simpa only [Function.comp_def] using
        (sphereGraphCapFamily_south_germ D C R L (x, s) (lt_of_not_ge hx)).comp_tendsto (hslice s)
    ext v w
    simp only [sphereFamilyForm, spherePullbackForm_apply]
    rw [sphere_mvfderiv_congr (he t), sphere_mvfderiv_congr (he 0)]

theorem IsometricGraphDevelopment.markedSphereFamilyForm_phase_invariant {A : FlatAnnularCore}
    (D : IsometricGraphDevelopment A) {R L k ρ : ℝ}
    (hR : A.b < R) (hL : 0 < L) (hρ : 0 < ρ) (hsmall : ρ < L / 64)
    (t : ℝ) (x : SpherePoint) :
    sphereFamilyForm D (markedCapMap R A.cRight L k ρ) R L t x =
      sphereFamilyForm D (markedCapMap R A.cRight L k ρ) R L 0 x :=
  sphereFamilyForm_phase_invariant D hR (fun _ hy =>
    markedCapMap_capSphereRadialMap_rim_germ (A.b_pos.trans hR) hL hρ hsmall A.cRight hy) t x

theorem IsometricGraphDevelopment.markedSphereFamilyForm_pos {A : FlatAnnularCore}
    (D : IsometricGraphDevelopment A) {R L k ρ : ℝ}
    (hR : A.b < R) (hL : 0 < L) (hk : 0 ≤ k) (hρ : 0 < ρ) (hsmall : ρ < L / 64)
    (t : ℝ) (x : SpherePoint) (v : TangentSpace (𝓡 2) x) (hv : v ≠ 0) :
    0 < sphereFamilyForm D (markedCapMap R A.cRight L k ρ) R L t x v v :=
  spherePullbackForm_pos (D.markedSphereFamily_mfderiv_injective hR hL hk hρ hsmall t x) v hv

theorem IsometricGraphDevelopment.markedSphereFamily_slice_contMDiff {A : FlatAnnularCore}
    (D : IsometricGraphDevelopment A) {R L k ρ : ℝ}
    (hR : A.b < R) (hL : 0 < L) (hρ : 0 < ρ) (hsmall : ρ < L / 64) (t : ℝ) :
    ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ (fun x : SpherePoint =>
      sphereGraphCapFamily D (markedCapMap R A.cRight L k ρ) R L (x, t)) := by
  have hi : ContMDiff (𝓡 2) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞
      (fun x : SpherePoint => (x, t)) := contMDiff_id.prodMk contMDiff_const
  exact (D.contMDiff_markedSphereFamily hR hL hρ hsmall).comp hi

/-- The fixed metric is exactly the pullback at phase zero of the same
constructed marked family. -/
def IsometricGraphDevelopment.markedSphereMetric {A : FlatAnnularCore}
    (D : IsometricGraphDevelopment A) {R L k ρ : ℝ}
    (hR : A.b < R) (hL : 0 < L) (hk : 0 ≤ k) (hρ : 0 < ρ) (hsmall : ρ < L / 64) :
    Bundle.ContMDiffRiemannianMetric (𝓡 2) ∞ SphereModel TSphere :=
  spherePullbackRiemannianMetric
    (D.markedSphereFamily_slice_contMDiff hR hL hρ hsmall 0)
    (D.markedSphereFamily_mfderiv_injective hR hL hk hρ hsmall 0)

@[simp] theorem IsometricGraphDevelopment.markedSphereMetric_inner {A : FlatAnnularCore}
    (D : IsometricGraphDevelopment A) {R L k ρ : ℝ}
    (hR : A.b < R) (hL : 0 < L) (hk : 0 ≤ k) (hρ : 0 < ρ) (hsmall : ρ < L / 64)
    (x : SpherePoint) (v w : TangentSpace (𝓡 2) x) :
    (D.markedSphereMetric hR hL hk hρ hsmall).inner x v w =
      sphereFamilyForm D (markedCapMap R A.cRight L k ρ) R L 0 x v w := rfl

theorem IsometricGraphDevelopment.markedSphereFamily_pullback_metric {A : FlatAnnularCore}
    (D : IsometricGraphDevelopment A) {R L k ρ : ℝ}
    (hR : A.b < R) (hL : 0 < L) (hk : 0 ≤ k) (hρ : 0 < ρ) (hsmall : ρ < L / 64)
    (t : ℝ) (x : SpherePoint) (v w : TangentSpace (𝓡 2) x) :
    inner ℝ
      (mvfderiv (𝓡 2) (fun y : SpherePoint =>
        sphereGraphCapFamily D (markedCapMap R A.cRight L k ρ) R L (y, t)) x v)
      (mvfderiv (𝓡 2) (fun y : SpherePoint =>
        sphereGraphCapFamily D (markedCapMap R A.cRight L k ρ) R L (y, t)) x w) =
      (D.markedSphereMetric hR hL hk hρ hsmall).inner x v w := by
  change sphereFamilyForm D (markedCapMap R A.cRight L k ρ) R L t x v w =
    sphereFamilyForm D (markedCapMap R A.cRight L k ρ) R L 0 x v w
  exact congrArg (fun B : TangentSpace (𝓡 2) x →L[ℝ] TangentSpace (𝓡 2) x →L[ℝ] ℝ => B v w)
    (D.markedSphereFamilyForm_phase_invariant hR hL hρ hsmall t x)

/-- The same actual cap and the same actual standard-sphere family carry one
smooth positive-definite metric for every real phase. -/
theorem IsometricGraphDevelopment.exists_markedSphereFamily_fixedMetric {A : FlatAnnularCore}
    (D : IsometricGraphDevelopment A) {R : ℝ} (hR : A.b < R) :
    ∃ L : ℝ, 0 < L ∧ ∀ k ρ : ℝ, 0 ≤ k → 0 < ρ → ρ < L / 64 →
      ∃ g : Bundle.ContMDiffRiemannianMetric (𝓡 2) ∞ SphereModel TSphere,
        ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E3) ∞
          (sphereGraphCapFamily D (markedCapMap R A.cRight L k ρ) R L) ∧
        (∀ t : ℝ, Manifold.IsSmoothEmbedding (𝓡 2) 𝓘(ℝ, E3) ∞ (fun x : SpherePoint =>
          sphereGraphCapFamily D (markedCapMap R A.cRight L k ρ) R L (x, t))) ∧
        ∀ (t : ℝ) (x : SpherePoint) (v w : TangentSpace (𝓡 2) x),
          inner ℝ
            (mvfderiv (𝓡 2) (fun y : SpherePoint =>
              sphereGraphCapFamily D (markedCapMap R A.cRight L k ρ) R L (y, t)) x v)
            (mvfderiv (𝓡 2) (fun y : SpherePoint =>
              sphereGraphCapFamily D (markedCapMap R A.cRight L k ρ) R L (y, t)) x w) =
            g.inner x v w := by
  obtain ⟨L, hL, hfamily⟩ := D.exists_markedSphereFamily_smoothEmbedding hR
  refine ⟨L, hL, ?_⟩
  intro k ρ hk hρ hsmall
  obtain ⟨hsm, hem⟩ := hfamily k ρ hk hρ hsmall
  refine ⟨D.markedSphereMetric hR hL hk hρ hsmall, hsm, hem, ?_⟩
  exact D.markedSphereFamily_pullback_metric hR hL hk hρ hsmall

end ContinuousFlexibility
