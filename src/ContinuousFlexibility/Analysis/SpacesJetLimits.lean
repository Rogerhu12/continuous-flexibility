module

public import ContinuousFlexibility.Analysis.SpacesCylinderReconstruction

/-!
# Smooth limits of the complete mixed jet tower

Uniform convergence on compact sets passes the actual first derivatives
to the limit. The adjacent mixed jets therefore form a classical smooth
derivative tower, and reconstruct one smooth function on the material
plane.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory ContinuousFlexibility.Analysis
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

/-- Complete real values turn compact uniform Cauchy convergence into
locally uniform convergence on the plane. -/
theorem spaces_exists_locallyUniform_limit (f : ℕ → PolarPoint → ℝ)
    (h : ∀ K : Set PolarPoint, IsCompact K → UniformCauchySeqOn f atTop K) :
    ∃ g : PolarPoint → ℝ, TendstoLocallyUniformly f g atTop ∧
      ∀ p, Tendsto (fun n => f n p) atTop (𝓝 (g p)) := by
  have hpoint (p : PolarPoint) : ∃ z : ℝ, Tendsto (fun n => f n p) atTop (𝓝 z) :=
    cauchySeq_tendsto_of_complete ((h {p} isCompact_singleton).cauchySeq (mem_singleton p))
  choose g hg using hpoint
  refine ⟨g, ?_, hg⟩
  apply tendstoLocallyUniformly_iff_forall_isCompact.mpr
  intro K hK
  exact (h K hK).tendstoUniformlyOn_of_tendsto (fun p _ => hg p)

/-- The derivative on the max-norm coordinate plane, assembled from its
two actual coordinate values. -/
def spacesPlaneDifferentialMap : PolarPoint →L[ℝ] (PolarPoint →L[ℝ] ℝ) :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (ContinuousLinearMap.fst ℝ ℝ ℝ) +
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (ContinuousLinearMap.snd ℝ ℝ ℝ)

@[simp] theorem spacesPlaneDifferentialMap_apply (v w : PolarPoint) :
    spacesPlaneDifferentialMap v w = v.1 * w.1 + v.2 * w.2 := by
  simp only [spacesPlaneDifferentialMap, add_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_apply, smul_eq_mul]

theorem spaces_fderiv_eq_planeDifferential (f : PolarPoint → ℝ) (p : PolarPoint) :
    fderiv ℝ f p = spacesPlaneDifferentialMap (radialPartial f p, angularPartial f p) := by
  apply ContinuousLinearMap.ext
  rintro ⟨r, θ⟩
  rw [spacesPlaneDifferentialMap_apply]
  have he : (r, θ) = r • ((1, 0) : PolarPoint) + θ • ((0, 1) : PolarPoint) := by
    ext <;> simp
  calc
    (fderiv ℝ f p) (r, θ) = (fderiv ℝ f p) (r • (1, 0) + θ • (0, 1)) := congrArg _ he
    _ = _ := by
      simp only [map_add, map_smul, smul_eq_mul, radialPartial, angularPartial]
      ring

/-- A locally uniformly convergent smooth mixed jet tower is the actual
mixed derivative tower of its order-zero limit. -/
theorem spaces_smooth_of_locallyUniform_mixedJets
    (f : ℕ → PolarPoint → ℝ) (v : ℕ → ℕ → PolarPoint → ℝ)
    (hf : ∀ n, ContDiff ℝ ∞ (f n))
    (hv : ∀ a b, TendstoLocallyUniformly (fun n => mixedDerivative a b (f n)) (v a b) atTop) :
    ContDiff ℝ ∞ (v 0 0) ∧ ∀ a b, mixedDerivative a b (v 0 0) = v a b := by
  have hvpoint (a b : ℕ) (p : PolarPoint) :
      Tendsto (fun n => mixedDerivative a b (f n) p) atTop (𝓝 (v a b p)) :=
    (hv a b).tendstoLocallyUniformlyOn.tendsto_at (mem_univ p)
  have hvc (a b : ℕ) : Continuous (v a b) :=
    (hv a b).continuous (Eventually.of_forall (fun n => (contDiff_mixedDerivative (hf n) a b).continuous)).frequently
  have hd (a b : ℕ) (p : PolarPoint) : HasFDerivAt (v a b)
      (spacesPlaneDifferentialMap (v (a + 1) b p, v a (b + 1) p)) p := by
    have hlimit : TendstoLocallyUniformly
        (fun n q => spacesPlaneDifferentialMap
          (mixedDerivative (a + 1) b (f n) q, mixedDerivative a (b + 1) (f n) q))
        (fun q => spacesPlaneDifferentialMap (v (a + 1) b q, v a (b + 1) q)) atTop := by
      simpa only [Function.comp_def] using
        spacesPlaneDifferentialMap.uniformContinuous.comp_tendstoLocallyUniformly
          ((hv (a + 1) b).prodMk (hv a (b + 1)))
    apply hasFDerivAt_of_tendstoLocallyUniformlyOn isOpen_univ
      hlimit.tendstoLocallyUniformlyOn (fun n q _ => ?_)
      (fun q _ => hvpoint a b q) (mem_univ p)
    have hn := ((contDiff_mixedDerivative (hf n) a b).differentiable (by simp) q).hasFDerivAt
    rw [spaces_fderiv_eq_planeDifferential,
      congrFun (radialPartial_mixedDerivative (hf n) a b) q,
      congrFun (angularPartial_mixedDerivative (hf n) a b) q] at hn
    exact hn
  have hs (n : ℕ) : ∀ a b, ContDiff ℝ n (v a b) := by
    induction n with
    | zero => exact fun a b => contDiff_zero.mpr (hvc a b)
    | succ n ih =>
      intro a b
      apply contDiff_succ_iff_hasFDerivAt.mpr
      refine ⟨fun q => spacesPlaneDifferentialMap (v (a + 1) b q, v a (b + 1) q), ?_, hd a b⟩
      simpa only [Function.comp_def] using
        spacesPlaneDifferentialMap.contDiff.comp ((ih (a + 1) b).prodMk (ih a (b + 1)))
  have hsmooth (a b : ℕ) : ContDiff ℝ ∞ (v a b) :=
    contDiff_infty.mpr (fun n => hs n a b)
  have hr (a b : ℕ) : radialPartial (v a b) = v (a + 1) b := by
    funext p
    simp only [radialPartial, (hd a b p).fderiv, spacesPlaneDifferentialMap_apply,
      mul_one, mul_zero, add_zero]
  have hθ (a b : ℕ) : angularPartial (v a b) = v a (b + 1) := by
    funext p
    simp only [angularPartial, (hd a b p).fderiv, spacesPlaneDifferentialMap_apply,
      mul_one, mul_zero, zero_add]
  refine ⟨hsmooth 0 0, ?_⟩
  intro a b
  induction a with
  | zero =>
    induction b with
    | zero =>
      funext p
      simp only [mixedDerivative, iteratedDeriv_zero, Prod.eta]
    | succ b ih => rw [← angularPartial_mixedDerivative (hsmooth 0 0) 0 b, ih, hθ]
  | succ a ih => rw [← radialPartial_mixedDerivative (hsmooth 0 0) a b, ih, hr]

/-- Reconstruction from compact-local integral limits of all mixed jets.
The result is a smooth periodic function and every jet converges locally
uniformly to its matching classical derivative. -/
theorem spaces_exists_smooth_periodic_of_local_L1_jets
    (f : ℕ → PolarPoint → ℝ) (g : ℕ → ℕ → PolarPoint → ℝ)
    (hf : ∀ n, ContDiff ℝ ∞ (f n))
    (hp : ∀ n x, Function.Periodic (fun θ => f n (x, θ)) Real.pi)
    (hg : ∀ a b, LocallyIntegrable (g a b) volume)
    (hlim : ∀ a b K, IsCompact K → Tendsto
      (fun n => ∫ p in K, |mixedDerivative a b (f n) p - g a b p|) atTop (𝓝 0)) :
    ∃ v : PolarPoint → ℝ, ContDiff ℝ ∞ v ∧ Function.Periodic v (0, Real.pi) ∧
      ∀ a b, TendstoLocallyUniformly (fun n => mixedDerivative a b (f n))
        (mixedDerivative a b v) atTop := by
  have hC (a b : ℕ) (K : Set PolarPoint) (hK : IsCompact K) :=
    spaces_uniformCauchy_mixedDerivative_of_local_L1 f g hf hp hg hlim a b hK
  choose v hv hvpoint using fun a b =>
    spaces_exists_locallyUniform_limit (fun n => mixedDerivative a b (f n)) (hC a b)
  obtain ⟨hs, hj⟩ := spaces_smooth_of_locallyUniform_mixedJets f v hf hv
  refine ⟨v 0 0, hs, ?_, fun a b => ?_⟩
  · intro p
    rcases p with ⟨x, θ⟩
    have h₁ : Tendsto (fun n => f n (x, θ + Real.pi)) atTop (𝓝 (v 0 0 (x, θ + Real.pi))) := by
      simpa only [mixedDerivative, iteratedDeriv_zero] using hvpoint 0 0 (x, θ + Real.pi)
    have h₂ : Tendsto (fun n => f n (x, θ)) atTop (𝓝 (v 0 0 (x, θ))) := by
      simpa only [mixedDerivative, iteratedDeriv_zero] using hvpoint 0 0 (x, θ)
    have he : (fun n => f n (x, θ + Real.pi)) = fun n => f n (x, θ) :=
      funext (fun n => hp n x θ)
    rw [he] at h₁
    simpa only [Prod.mk_add_mk, add_zero] using tendsto_nhds_unique h₁ h₂
  · rw [hj a b]
    exact hv a b

end ContinuousFlexibility.Statements
