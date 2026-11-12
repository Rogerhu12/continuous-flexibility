import ContinuousFlexibility.Analysis.N05CanonicalMollifierL2Estimate
import ContinuousFlexibility.Analysis.PhysicalJetMollification

/-!
# Strong local L² approximation by smooth compact kernels

Shrinking normalized smooth bumps approximate every locally square
integrable planar function on each compact set. The periodic planar
representative of every actual cylinder L² class satisfies the required
local square integrability, so this applies to all its weak angular jets.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter Function MeasureTheory
open scoped Topology Convolution ENNReal

theorem n05_tendsto_integral_sq_bump_convolution_sub
    {ι : Type*} {l : Filter ι} {φ : ι → ContDiffBump (0 : SpacesPlane)}
    (hφ : Tendsto (fun i => (φ i).rOut) l (𝓝 0))
    {f : SpacesPlane → ℝ} (hf₁ : Integrable f volume) (hf₂ : MemLp f 2 volume) :
    Tendsto (fun i => ∫ x,
      (((φ i).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x - f x) ^ 2)
      l (𝓝 0) := by
  have hc : Tendsto (fun y : SpacesPlane => ∫ x, (f (x - y) - f x) ^ 2)
      (𝓝 0) (𝓝 0) := by
    simpa only [sub_zero, sub_self, zero_pow (by decide : (2 : ℕ) ≠ 0), integral_zero] using
      (n05_continuous_integral_sq_translation_sub hf₂).tendsto (0 : SpacesPlane)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hnear : ∀ᶠ y : SpacesPlane in 𝓝 0,
      (∫ x, (f (x - y) - f x) ^ 2) < ε / 2 :=
    hc.eventually (gt_mem_nhds (half_pos hε))
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hnear
  filter_upwards [hφ.eventually (gt_mem_nhds hδ)] with i hi
  have hbound := n05_integral_sq_convolution_sub_le hf₁ hf₂
    (φ i).integrable_normed (φ i).nonneg_normed (φ i).integral_normed
    (ε := ε / 2) (by
      intro y hy
      have hyr : y ∈ Metric.ball (0 : SpacesPlane) (φ i).rOut := by
        simpa only [(φ i).support_normed_eq] using hy
      exact (hδsub (Metric.ball_subset_ball hi.le hyr)).le)
  have hn : 0 ≤ ∫ x,
      (((φ i).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x - f x) ^ 2 :=
    integral_nonneg (fun _ => sq_nonneg _)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hn]
  exact hbound.trans_lt (half_lt_self hε)

theorem n05_tendsto_setIntegral_sq_bump_convolution_sub
    {ι : Type*} {l : Filter ι} {φ : ι → ContDiffBump (0 : SpacesPlane)}
    (hφ : Tendsto (fun i => (φ i).rOut) l (𝓝 0))
    {f : SpacesPlane → ℝ} (hf₁ : LocallyIntegrable f volume)
    (hf₂ : ∀ K : Set SpacesPlane, IsCompact K → MemLp f 2 (volume.restrict K))
    {K : Set SpacesPlane} (hK : IsCompact K) :
    Tendsto (fun i => ∫ x in K,
      (((φ i).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x - f x) ^ 2)
      l (𝓝 0) := by
  obtain ⟨R, hR, hKR⟩ := hK.isBounded.subset_closedBall_lt 0 (0 : SpacesPlane)
  let B : Set SpacesPlane := Metric.closedBall 0 (R + 1)
  let g : SpacesPlane → ℝ := B.indicator f
  have hB : IsCompact B := isCompact_closedBall 0 (R + 1)
  have hg₁ : Integrable g volume :=
    (hf₁.integrableOn_isCompact hB).integrable_indicator hB.measurableSet
  have hg₂ : MemLp g 2 volume :=
    (memLp_indicator_iff_restrict hB.measurableSet).mpr (hf₂ B hB)
  have hKB : K ⊆ B := hKR.trans (Metric.closedBall_subset_closedBall (by linarith))
  have hgf (x : SpacesPlane) (hx : x ∈ K) : g x = f x :=
    indicator_of_mem (hKB hx) f
  have heq (i : ι) (hi : (φ i).rOut < 1) (x : SpacesPlane) (hx : x ∈ K) :
      ((φ i).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x =
        ((φ i).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x := by
    simp only [convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
    apply integral_congr_ae
    filter_upwards [] with y
    by_cases hy : (φ i).normed volume y = 0
    · rw [hy, zero_mul, zero_mul]
    · have hyr : y ∈ Metric.ball (0 : SpacesPlane) (φ i).rOut := by
        rw [← (φ i).support_normed_eq (μ := volume)]
        exact hy
      have hyn : ‖y‖ < (φ i).rOut := by
        simpa only [Metric.mem_ball, dist_zero_right] using hyr
      have hyNorm : ‖y‖ < 1 := hyn.trans hi
      have hxNorm : ‖x‖ ≤ R := by
        simpa only [Metric.mem_closedBall, dist_zero_right] using hKR hx
      have hxy : x - y ∈ B := by
        apply (Metric.mem_closedBall).mpr
        rw [dist_zero_right]
        exact (norm_sub_le x y).trans (add_le_add hxNorm hyNorm.le)
      rw [show g (x - y) = f (x - y) from indicator_of_mem hxy f]
  have ht := n05_tendsto_integral_sq_bump_convolution_sub hφ hg₁ hg₂
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hsmall := Metric.tendsto_nhds.mp ht ε hε
  filter_upwards [hφ.eventually (gt_mem_nhds zero_lt_one), hsmall] with i hi hbound
  have hnon : 0 ≤ ∫ x in K,
      (((φ i).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x - f x) ^ 2 :=
    integral_nonneg (fun _ => sq_nonneg _)
  have hglobalNon : 0 ≤ ∫ x,
      (((φ i).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x - g x) ^ 2 :=
    integral_nonneg (fun _ => sq_nonneg _)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnon]
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hglobalNon] at hbound
  calc
    (∫ x in K,
        (((φ i).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x - f x) ^ 2) =
        ∫ x in K,
          (((φ i).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x - g x) ^ 2 := by
      apply setIntegral_congr_fun hK.measurableSet
      intro x hx
      dsimp only
      rw [heq i hi x hx, hgf x hx]
    _ ≤ ∫ x,
        (((φ i).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x - g x) ^ 2 :=
      setIntegral_le_integral
        (n05_memLp_convolution_sub hg₁ hg₂ (φ i).integrable_normed
          (φ i).nonneg_normed (φ i).integral_normed).integrable_sq
        (Eventually.of_forall (fun _ => sq_nonneg _))
    _ < ε := hbound

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory ContinuousFlexibility.Analysis
open scoped Topology Convolution

theorem n05_cylinderPeriodicExtension_local_L2_mollification
    {ι : Type*} {l : Filter ι} {φ : ι → ContDiffBump (0 : PolarPoint)}
    (hφ : Tendsto (fun i => (φ i).rOut) l (𝓝 0))
    (u : CylinderL2) {K : Set PolarPoint} (hK : IsCompact K) :
    Tendsto (fun i => ∫ x in K,
      (((φ i).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        cylinderPeriodicExtension u) x - cylinderPeriodicExtension u x) ^ 2)
      l (𝓝 0) :=
  n05_tendsto_setIntegral_sq_bump_convolution_sub hφ
    (locallyIntegrable_cylinderPeriodicExtension u)
    (fun _ h => memLp_cylinderPeriodicExtension_restrict_compact u h) hK

end ContinuousFlexibility.Statements
