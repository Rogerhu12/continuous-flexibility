import ContinuousFlexibility.Analysis.N01FlowJointRegularity
import ContinuousFlexibility.Analysis.N01FlowAngularSmoothness
import ContinuousFlexibility.Analysis.ReturnFlowInverseRegularity

/-!
# Joint regularity of the actual angular variation

The radial derivative of the first angular variation is obtained by FTC
from its already proved exponential formula. The second angular jet is
jointly continuous by the actual angular bootstrap. Together these give
a joint strict derivative and C¹ regularity of the first angular
variation throughout the open component, including radii where the
radial square root itself need only be continuous.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology
open ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

local instance : NormedSpace ℝ ℝ := NormedField.toNormedSpace

theorem returnFlow_coprod_toSpan (a b : ℝ) :
    (ContinuousLinearMap.toSpanSingleton ℝ a).coprod
        (ContinuousLinearMap.toSpanSingleton ℝ b) =
      a • ContinuousLinearMap.fst ℝ ℝ ℝ + b • ContinuousLinearMap.snd ℝ ℝ ℝ := by
  apply ContinuousLinearMap.ext
  intro p
  simp only [ContinuousLinearMap.coprod_apply, ContinuousLinearMap.toSpanSingleton_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul]
  ring

section ActualVariation

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
  (hN01 : N01Properties D T S C base loss ε)
  (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
  {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
  (hsector : stateSector S z.1) (m : ℕ)

include hN01 hS hT hz hsector

theorem N01Properties.minusFlow_angular_deriv_hasDerivAt_radial
    {r : ℝ} (hr : r ∈ Ioo (C.left m) (C.right m)) (θ : ℝ) :
    HasDerivAt (fun s => deriv (C.minusFlow z m s) θ)
      (characteristicAngularDerivative D S C z (r, C.minusFlow z m r θ) *
        deriv (C.minusFlow z m r) θ) r := by
  have hC : controlGeometryConditions D S C := hN01.2.2.2.1
  let H : PolarPoint → ℝ := fun p =>
    characteristicAngularDerivative D S C z (p.1, C.minusFlow z m p.1 p.2)
  have hH : ContinuousOn H (Icc (C.left m) (C.right m) ×ˢ univ) :=
    (hN01.characteristicAngularDerivative_continuousOn hS hT hz hsector m).comp
      (continuous_fst.continuousOn.prodMk (hN01.minusFlow_continuousOn hz m))
      (fun p hp => ⟨hp.1, mem_univ _⟩)
  let α : ℝ → ℝ := fun s => closedStripExtend (hC.1 m).2.1.le H (s, θ)
  have hα : Continuous α :=
    (continuous_closedStripExtend (hC.1 m).2.1.le hH).comp
      (continuous_id.prodMk continuous_const)
  have hint (s : ℝ) (hs : s ∈ Icc (C.left m) (C.right m)) :
      (∫ t in C.left m..s, α t) = ∫ t in C.left m..s,
        characteristicAngularDerivative D S C z (t, C.minusFlow z m t θ) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hs.1] at ht
    exact closedStripExtend_eq (hC.1 m).2.1.le H
      (p := (t, θ)) ⟨ht.1, ht.2.trans hs.2⟩
  have hpoint : α r =
      characteristicAngularDerivative D S C z (r, C.minusFlow z m r θ) :=
    closedStripExtend_eq (hC.1 m).2.1.le H (p := (r, θ)) ⟨hr.1.le, hr.2.le⟩
  have hJ := (hN01.minusFlow_hasDerivAt_exp_integral hS hT hz hsector m
    ⟨hr.1.le, hr.2.le⟩ θ).deriv
  have h := ((hα.integral_hasStrictDerivAt (C.left m) r).hasDerivAt.exp).congr_deriv
    (g' := characteristicAngularDerivative D S C z (r, C.minusFlow z m r θ) *
      deriv (C.minusFlow z m r) θ) (by
        rw [hint r ⟨hr.1.le, hr.2.le⟩, hpoint, hJ]
        ring)
  apply h.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hr.1 hr.2] with s hs
  rw [(hN01.minusFlow_hasDerivAt_exp_integral hS hT hz hsector m
    ⟨hs.1.le, hs.2.le⟩ θ).deriv, hint s ⟨hs.1.le, hs.2.le⟩]

theorem N01Properties.minusFlow_angular_deriv_hasStrictFDerivAt
    (p : PolarPoint) (hp : p.1 ∈ Ioo (C.left m) (C.right m)) :
    HasStrictFDerivAt (fun q : PolarPoint => deriv (C.minusFlow z m q.1) q.2)
      ((ContinuousLinearMap.toSpanSingleton ℝ
        (characteristicAngularDerivative D S C z (p.1, C.minusFlow z m p.1 p.2) *
          deriv (C.minusFlow z m p.1) p.2)).coprod
        (ContinuousLinearMap.toSpanSingleton ℝ (deriv (deriv (C.minusFlow z m p.1)) p.2))) p := by
  have hopen : Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ) ∈ 𝓝 p :=
    (isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨hp, mem_univ _⟩
  have hclosed : Icc (C.left m) (C.right m) ×ˢ (univ : Set ℝ) ∈ 𝓝 p :=
    mem_of_superset hopen (fun q hq => ⟨⟨hq.1.1.le, hq.1.2.le⟩, hq.2⟩)
  have hΦ := hN01.minusFlow_continuousOn hz m
  have hJ := hN01.minusFlow_angular_deriv_continuousOn hS hT hz hsector m
  have hH : ContinuousOn (fun q : PolarPoint =>
      characteristicAngularDerivative D S C z (q.1, C.minusFlow z m q.1 q.2))
      (Icc (C.left m) (C.right m) ×ˢ univ) :=
    (hN01.characteristicAngularDerivative_continuousOn hS hT hz hsector m).comp
      (continuous_fst.continuousOn.prodMk hΦ) (fun q hq => ⟨hq.1, mem_univ _⟩)
  have hJJ : ContinuousOn (fun q : PolarPoint => deriv (deriv (C.minusFlow z m q.1)) q.2)
      (Icc (C.left m) (C.right m) ×ˢ univ) := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
      hN01.minusFlow_angular_iteratedDeriv_continuousOn hS hT hz hsector m 2
  have hlin : Continuous (fun c : ℝ => ContinuousLinearMap.toSpanSingleton ℝ c) := by
    have heq : (fun c : ℝ => ContinuousLinearMap.toSpanSingleton ℝ c) =
        (ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ : ℝ → (ℝ →L[ℝ] ℝ)) := by
      funext c
      exact (ContinuousLinearMap.toSpanSingletonLIE_apply ℝ ℝ c).symm
    rw [heq]
    exact (ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ).continuous
  have hpartial := hasStrictFDerivAt_uncurry_coprod
    (f := fun r => deriv (C.minusFlow z m r))
    (f₁ := fun r θ => ContinuousLinearMap.toSpanSingleton ℝ
      (characteristicAngularDerivative D S C z (r, C.minusFlow z m r θ) *
        deriv (C.minusFlow z m r) θ))
    (f₂ := fun r θ => ContinuousLinearMap.toSpanSingleton ℝ
      (deriv (deriv (C.minusFlow z m r)) θ))
    (by
      filter_upwards [hopen] with q hq
      simpa only [Function.HasUncurry.uncurry, Function.hasUncurryBase,
        Function.hasUncurryInduction, id_eq, Function.comp_def] using
        (hN01.minusFlow_angular_deriv_hasDerivAt_radial hS hT hz hsector m hq.1 q.2).hasFDerivAt)
    (by
      filter_upwards [hopen] with q hq
      have hreg : ContDiff ℝ 2 (C.minusFlow z m q.1) :=
        (hN01.minusFlow_angular_contDiff hS hT hz hsector m
          ⟨hq.1.1.le, hq.1.2.le⟩).of_le (by simp)
      simpa only [Function.HasUncurry.uncurry, Function.hasUncurryBase,
        Function.hasUncurryInduction, id_eq, Function.comp_def] using
        (hreg.differentiable_deriv_two q.2).hasDerivAt.hasFDerivAt)
    (by simpa only [Function.HasUncurry.uncurry, Function.hasUncurryBase,
        Function.hasUncurryInduction, id_eq, Function.comp_def, Pi.mul_apply] using
      hlin.continuousAt.comp ((hH.mul hJ).continuousAt hclosed))
    (by simpa only [Function.HasUncurry.uncurry, Function.hasUncurryBase,
        Function.hasUncurryInduction, id_eq, Function.comp_def] using hlin.continuousAt.comp (hJJ.continuousAt hclosed))
  simpa only [Function.HasUncurry.uncurry, Function.hasUncurryBase,
        Function.hasUncurryInduction, id_eq, Function.comp_def] using hpartial

theorem N01Properties.minusFlow_angular_deriv_contDiffAt_one
    (p : PolarPoint) (hp : p.1 ∈ Ioo (C.left m) (C.right m)) :
    ContDiffAt ℝ 1 (fun q : PolarPoint => deriv (C.minusFlow z m q.1) q.2) p := by
  let U : Set PolarPoint := Ioo (C.left m) (C.right m) ×ˢ univ
  have hU : U ∈ 𝓝 p := (isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨hp, mem_univ _⟩
  have hΦ := hN01.minusFlow_continuousOn hz m
  have hJ := hN01.minusFlow_angular_deriv_continuousOn hS hT hz hsector m
  have hH : ContinuousOn (fun q : PolarPoint =>
      characteristicAngularDerivative D S C z (q.1, C.minusFlow z m q.1 q.2))
      (Icc (C.left m) (C.right m) ×ˢ univ) :=
    (hN01.characteristicAngularDerivative_continuousOn hS hT hz hsector m).comp
      (continuous_fst.continuousOn.prodMk hΦ) (fun q hq => ⟨hq.1, mem_univ _⟩)
  have hJJ : ContinuousOn (fun q : PolarPoint => deriv (deriv (C.minusFlow z m q.1)) q.2)
      (Icc (C.left m) (C.right m) ×ˢ univ) := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
      hN01.minusFlow_angular_iteratedDeriv_continuousOn hS hT hz hsector m 2
  apply contDiffAt_one_iff.mpr
  refine ⟨fun q =>
      (characteristicAngularDerivative D S C z (q.1, C.minusFlow z m q.1 q.2) *
        deriv (C.minusFlow z m q.1) q.2) • ContinuousLinearMap.fst ℝ ℝ ℝ +
      deriv (deriv (C.minusFlow z m q.1)) q.2 • ContinuousLinearMap.snd ℝ ℝ ℝ,
    U, hU, ?_, ?_⟩
  · exact (((hH.mul hJ).smul continuousOn_const).add
      (hJJ.smul continuousOn_const)).mono
        (fun q hq => ⟨⟨hq.1.1.le, hq.1.2.le⟩, hq.2⟩)
  · intro q hq
    simpa only [returnFlow_coprod_toSpan] using
      (hN01.minusFlow_angular_deriv_hasStrictFDerivAt hS hT hz hsector m q hq.1).hasFDerivAt

theorem N01Properties.minusFlow_contDiffAt_one
    (p : PolarPoint) (hp : p.1 ∈ Ioo (C.left m) (C.right m)) :
    ContDiffAt ℝ 1 (fun q : PolarPoint => C.minusFlow z m q.1 q.2) p := by
  let U : Set PolarPoint := Ioo (C.left m) (C.right m) ×ˢ univ
  have hU : U ∈ 𝓝 p := (isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨hp, mem_univ _⟩
  have hC : controlGeometryConditions D S C := hN01.2.2.2.1
  have hv : ContinuousOn (fun q : PolarPoint =>
      minusCharacteristicSpeed (originalCoefficients D S C z)
        (q.1, C.minusFlow z m q.1 q.2)) U := by
    intro q hq
    have hΦ := (hN01.minusFlow_hasStrictFDerivAt hS hT hz hsector m q hq.1).continuousAt
    exact ((hN01.minusCharacteristicSpeed_continuousAt hS hT hz hsector
      (p := (q.1, C.minusFlow z m q.1 q.2))
      ⟨⟨(hC.1 m).1.trans hq.1.1, hq.1.2.trans (hC.1 m).2.2⟩,
        mem_univ _⟩).comp (f := fun r : PolarPoint => (r.1, C.minusFlow z m r.1 r.2))
        (continuousAt_fst.prodMk hΦ)).continuousWithinAt
  have hJ := (hN01.minusFlow_angular_deriv_continuousOn hS hT hz hsector m).mono
    (show U ⊆ Icc (C.left m) (C.right m) ×ˢ univ from
      fun q hq => ⟨⟨hq.1.1.le, hq.1.2.le⟩, hq.2⟩)
  apply contDiffAt_one_iff.mpr
  refine ⟨fun q =>
      minusCharacteristicSpeed (originalCoefficients D S C z)
        (q.1, C.minusFlow z m q.1 q.2) • ContinuousLinearMap.fst ℝ ℝ ℝ +
      deriv (C.minusFlow z m q.1) q.2 • ContinuousLinearMap.snd ℝ ℝ ℝ,
    U, hU, (hv.smul continuousOn_const).add (hJ.smul continuousOn_const), ?_⟩
  intro q hq
  simpa only [returnFlow_coprod_toSpan] using
    (hN01.minusFlow_hasStrictFDerivAt hS hT hz hsector m q hq.1).hasFDerivAt

theorem N01Properties.minusFlow_invFun_contDiffAt_one
    (p : PolarPoint) (hp : p.1 ∈ Ioo (C.left m) (C.right m)) :
    ContDiffAt ℝ 1 (fun q : PolarPoint => Function.invFun (C.minusFlow z m q.1) q.2) p := by
  have hflow : ordinaryFlowConditions D S C (stateNeighborhood S C base ε) :=
    hN01.2.2.2.2.2.2.1
  have hclosed : p.1 ∈ Icc (C.left m) (C.right m) := ⟨hp.1.le, hp.2.le⟩
  have hsurj := returnLift_surjective Real.pi_pos
    (N01Properties.minusFlow_differentiable S C z m hN01 hz hclosed).continuous
    (hN01.minusFlow_add_period hz m hclosed)
  let α := Function.invFun (C.minusFlow z m p.1) p.2
  have hpoint : (p.1, C.minusFlow z m p.1 α) = p := by
    apply Prod.ext
    · rfl
    · exact Function.rightInverse_invFun hsurj p.2
  have hinj : ∀ᶠ r in 𝓝 p.1, Function.Injective (C.minusFlow z m r) := by
    filter_upwards [Ioo_mem_nhds hp.1 hp.2] with r hr
    exact (strictMono_of_deriv_pos fun θ =>
      ((hflow z hz m θ).2.2.2 r ⟨hr.1.le, hr.2.le⟩).1).injective
  have h := returnFlow_invFun_contDiffAt
    (hN01.minusFlow_contDiffAt_one hS hT hz hsector m (p.1, α) hp)
    one_ne_zero (((hflow z hz m α).2.2.2 p.1 hclosed).1.ne') hinj
  rw [hpoint] at h
  exact h

end ActualVariation

end ContinuousFlexibility.Statements
