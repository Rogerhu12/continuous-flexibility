import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Local integral convergence of planar mollification

The source functions in the physical weak graph are locally integrable
on the periodically extended plane. Translation continuity in `L¹`,
followed by Fubini, gives the integral approximation needed for the
two-dimensional pointwise Sobolev estimate.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter Function MeasureTheory
open scoped Topology Convolution ENNReal

set_option backward.isDefEq.respectTransparency false

abbrev SpacesPlane := ℝ × ℝ

instance spaces_plane_volume_isAddHaarMeasure :
    (volume : Measure SpacesPlane).IsAddHaarMeasure := by
  rw [Measure.volume_eq_prod]
  infer_instance

/-- Translation of an integrable function is continuous in the actual
integral distance. This formulation avoids any choice of representative
in subsequent convolution estimates. -/
theorem spaces_continuous_integral_translation_sub
    {f : SpacesPlane → ℝ} (hf : Integrable f volume) :
    Continuous (fun y : SpacesPlane => ∫ x, |f (x - y) - f x|) := by
  let u := hf.toL1 f
  let g (y : SpacesPlane) : C(SpacesPlane, SpacesPlane) :=
    ⟨fun x => x - y, continuous_id.sub continuous_const⟩
  have hg : Continuous g :=
    ContinuousMap.continuous_of_continuous_uncurry g
      (continuous_snd.sub continuous_fst)
  have hgm (y : SpacesPlane) : MeasurePreserving (g y) volume volume :=
    measurePreserving_sub_right volume y
  let τ (y : SpacesPlane) := Lp.compMeasurePreserving (g y) (hgm y) u
  have hτ : Continuous τ :=
    continuous_const.compMeasurePreservingLp hg hgm (by simp : (1 : ℝ≥0∞) ≠ ∞)
  have he (y : SpacesPlane) :
      dist (τ y) u = ∫ x, |f (x - y) - f x| := by
    rw [L1.dist_eq_integral_dist]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_compMeasurePreserving u (hgm y), hf.coeFn_toL1,
      (hgm y).quasiMeasurePreserving.ae hf.coeFn_toL1] with x hτx hx hxy
    rw [hτx]
    simpa only [Function.comp_apply, g, ContinuousMap.coe_mk, Real.dist_eq] using
      congrArg₂ dist hxy hx
  simpa only [he] using hτ.dist (continuous_const (y := u))

/-- A normalized nonnegative convolution is close in `L¹` whenever all
translations appearing in its support are close in `L¹`. -/
theorem spaces_integral_abs_convolution_sub_le
    {f κ : SpacesPlane → ℝ} (hf : Integrable f volume) (hκ : Integrable κ volume)
    (hnon : ∀ y, 0 ≤ κ y) (hmass : ∫ y, κ y = 1) {ε : ℝ}
    (hsmall : ∀ y ∈ support κ, (∫ x, |f (x - y) - f x|) ≤ ε) :
    (∫ x, |(κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x - f x|) ≤ ε := by
  let H (p : SpacesPlane × SpacesPlane) := κ p.2 * (f (p.1 - p.2) - f p.1)
  have hH : Integrable H (volume.prod volume) := by
    have h₁ := hκ.convolution_integrand (ContinuousLinearMap.lsmul ℝ ℝ) hf
    have h₂ := (hκ.mul_prod hf).swap
    simpa only [H, Pi.sub_def, mul_sub, ContinuousLinearMap.lsmul_apply, smul_eq_mul,
      Function.comp_def, Prod.fst_swap, Prod.snd_swap] using h₁.sub h₂
  have hconv := hκ.integrable_convolution (ContinuousLinearMap.lsmul ℝ ℝ) hf
  have he : ∀ᵐ x : SpacesPlane ∂volume,
      (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x - f x =
        ∫ y, H (x, y) := by
    filter_upwards [hκ.ae_convolution_exists (ContinuousLinearMap.lsmul ℝ ℝ) hf] with x hx
    rw [show (∫ y, H (x, y)) =
        (∫ y, κ y * f (x - y)) - ∫ y, κ y * f x by
      simp only [H, mul_sub]
      exact integral_sub hx (hκ.mul_const (f x))]
    simp only [convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul,
      integral_mul_const, hmass, one_mul]
  have hint : Integrable (fun x : SpacesPlane => ∫ y, |H (x, y)|) volume := by
    simpa only [Real.norm_eq_abs] using hH.norm.integral_prod_left
  have hbound : (∫ x, |(κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x - f x|) ≤
      ∫ x, ∫ y, |H (x, y)| := by
    apply integral_mono_ae (hconv.sub hf).abs hint
    filter_upwards [he] with x hx
    simp only [Pi.sub_apply]
    rw [hx]
    simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun y => H (x, y))
  calc
    (∫ x, |(κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x - f x|) ≤
        ∫ x, ∫ y, |H (x, y)| := hbound
    _ = ∫ y, κ y * ∫ x, |f (x - y) - f x| := by
      rw [integral_integral_swap (by
        simpa only [Function.uncurry_def, Prod.eta, Real.norm_eq_abs] using hH.norm)]
      apply integral_congr_ae
      filter_upwards [] with y
      simp only [H, abs_mul, abs_of_nonneg (hnon y), integral_const_mul]
    _ ≤ ∫ y, κ y * ε := by
      have hi : Integrable (fun y : SpacesPlane => κ y * ∫ x, |f (x - y) - f x|) volume := by
        have hi := hH.norm.integral_prod_right
        simpa only [H, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hnon _),
          integral_const_mul] using hi
      apply integral_mono hi (hκ.mul_const ε)
      intro y
      by_cases hy : y ∈ support κ
      · exact mul_le_mul_of_nonneg_left (hsmall y hy) (hnon y)
      · simp only [notMem_support.mp hy, zero_mul, le_refl]
    _ = ε := by rw [integral_mul_const, hmass, one_mul]

/-- Shrinking normalized smooth kernels approximate every integrable
function in the actual `L¹` integral norm. -/
theorem spaces_tendsto_integral_abs_bump_convolution_sub
    {ι : Type*} {l : Filter ι} {φ : ι → ContDiffBump (0 : SpacesPlane)}
    (hφ : Tendsto (fun i => (φ i).rOut) l (𝓝 0))
    {f : SpacesPlane → ℝ} (hf : Integrable f volume) :
    Tendsto (fun i => ∫ x,
      |((φ i).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x - f x|)
      l (𝓝 0) := by
  have hc : Tendsto (fun y : SpacesPlane => ∫ x, |f (x - y) - f x|) (𝓝 0) (𝓝 0) := by
    simpa only [sub_zero, sub_self, abs_zero, integral_zero] using
      (spaces_continuous_integral_translation_sub hf).tendsto (0 : SpacesPlane)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hnear : ∀ᶠ y : SpacesPlane in 𝓝 0,
      (∫ x, |f (x - y) - f x|) < ε / 2 :=
    hc.eventually (gt_mem_nhds (half_pos hε))
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hnear
  filter_upwards [hφ.eventually (gt_mem_nhds hδ)] with i hi
  have hbound := spaces_integral_abs_convolution_sub_le hf
    (φ i).integrable_normed (φ i).nonneg_normed (φ i).integral_normed
    (ε := ε / 2) (by
      intro y hy
      have hyr : y ∈ Metric.ball (0 : SpacesPlane) (φ i).rOut := by
        simpa only [(φ i).support_normed_eq] using hy
      exact (hδsub (Metric.ball_subset_ball hi.le hyr)).le)
  have hn : 0 ≤ ∫ x,
      |((φ i).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x - f x| :=
    integral_nonneg (fun _ => abs_nonneg _)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hn]
  exact hbound.trans_lt (half_lt_self hε)

/-- Local `L¹` approximation needs no global integrability of the source.
On a compact set, sufficiently small convolutions see only one fixed
compact truncation of the source. -/
theorem spaces_tendsto_setIntegral_abs_bump_convolution_sub
    {ι : Type*} {l : Filter ι} {φ : ι → ContDiffBump (0 : SpacesPlane)}
    (hφ : Tendsto (fun i => (φ i).rOut) l (𝓝 0))
    {f : SpacesPlane → ℝ} (hf : LocallyIntegrable f volume)
    {K : Set SpacesPlane} (hK : IsCompact K) :
    Tendsto (fun i => ∫ x in K,
      |((φ i).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x - f x|)
      l (𝓝 0) := by
  obtain ⟨R, hR, hKR⟩ := hK.isBounded.subset_closedBall_lt 0 (0 : SpacesPlane)
  let B : Set SpacesPlane := Metric.closedBall 0 (R + 1)
  let g : SpacesPlane → ℝ := B.indicator f
  have hB : IsCompact B := isCompact_closedBall 0 (R + 1)
  have hg : Integrable g volume :=
    (hf.integrableOn_isCompact hB).integrable_indicator hB.measurableSet
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
  have ht := spaces_tendsto_integral_abs_bump_convolution_sub hφ hg
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hsmall := Metric.tendsto_nhds.mp ht ε hε
  filter_upwards [hφ.eventually (gt_mem_nhds zero_lt_one), hsmall] with i hi hbound
  have hnon : 0 ≤ ∫ x in K,
      |((φ i).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x - f x| :=
    integral_nonneg (fun _ => abs_nonneg _)
  have hglobalNon : 0 ≤ ∫ x,
      |((φ i).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x - g x| :=
    integral_nonneg (fun _ => abs_nonneg _)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnon]
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hglobalNon] at hbound
  calc
    (∫ x in K, |((φ i).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x - f x|) =
        ∫ x in K, |((φ i).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x - g x| := by
      apply setIntegral_congr_fun hK.measurableSet
      intro x hx
      dsimp only
      rw [heq i hi x hx, hgf x hx]
    _ ≤ ∫ x, |((φ i).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x - g x| :=
      setIntegral_le_integral
        (((φ i).integrable_normed.integrable_convolution
          (ContinuousLinearMap.lsmul ℝ ℝ) hg).sub hg).abs
        (Eventually.of_forall (fun _ => abs_nonneg _))
    _ < ε := hbound

end ContinuousFlexibility.Analysis
