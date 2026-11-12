import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.UniformSpace.Cauchy

/-!
# Derivatives of a pointwise limit with uniform first-order remainders

A uniform quadratic Taylor estimate forces the derivatives at the base
point to be Cauchy. Their limit is the derivative of the pointwise limit.
No convergence of the derivatives is assumed. This is the scalar step
used to transfer interior directional jets to a continuous endpoint.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology

local instance scalarDerivativeLimitRealNormedSpace : NormedSpace ℝ ℝ := NormedField.toNormedSpace

/-- Two applications of the scalar mean value theorem give a uniform
slope remainder. The bound is valid on both sides of the base point. -/
theorem abs_slope_sub_derivative_le_of_second_derivative_bound
    {f f' f'' : ℝ → ℝ} {δ B h : ℝ}
    (hδ : 0 < δ) (hB : 0 ≤ B)
    (hf : ∀ t : ℝ, |t| < δ → HasDerivAt f (f' t) t)
    (hf' : ∀ t : ℝ, |t| < δ → HasDerivAt f' (f'' t) t)
    (hbound : ∀ t : ℝ, |t| < δ → |f'' t| ≤ B)
    (hh : |h| < δ) (hne : h ≠ 0) :
    |h⁻¹ * (f h - f 0) - f' 0| ≤ B * |h| := by
  have hseg (t : ℝ) (ht : t ∈ uIcc (0 : ℝ) h) : |t| ≤ |h| := by
    simpa only [sub_zero] using abs_sub_left_of_mem_uIcc ht
  have hprime (t : ℝ) (ht : t ∈ uIcc (0 : ℝ) h) :
      |f' t - f' 0| ≤ B * |h| := by
    have hb := (convex_uIcc (0 : ℝ) h).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun s hs => (hf' s ((hseg s hs).trans_lt hh)).hasDerivWithinAt)
      (fun s hs => by
        simpa only [Real.norm_eq_abs] using (hbound s ((hseg s hs).trans_lt hh)))
      (left_mem_uIcc : (0 : ℝ) ∈ uIcc 0 h) ht
    have hb' : |f' t - f' 0| ≤ B * |t| := by
      simpa only [Real.norm_eq_abs, sub_zero] using hb
    exact hb'.trans (mul_le_mul_of_nonneg_left (hseg t ht) hB)
  have hrem : |(f h - f 0) - h * f' 0| ≤ (B * |h|) * |h| := by
    have hd (t : ℝ) (ht : t ∈ uIcc (0 : ℝ) h) :
        HasDerivAt (fun s => f s - s * f' 0) (f' t - f' 0) t := by
      simpa only [one_mul, Pi.sub_apply, id_eq] using
        (hf t ((hseg t ht).trans_lt hh)).fun_sub ((hasDerivAt_id t).mul_const (f' 0))
    have hb := (convex_uIcc (0 : ℝ) h).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun t ht => (hd t ht).hasDerivWithinAt)
      (fun t ht => by simpa only [Real.norm_eq_abs] using hprime t ht)
      (left_mem_uIcc : (0 : ℝ) ∈ uIcc 0 h) (right_mem_uIcc : h ∈ uIcc 0 h)
    have heq : f h - h * f' 0 - f 0 = (f h - f 0) - h * f' 0 := by ring
    simpa only [Real.norm_eq_abs, zero_mul, sub_zero, heq] using hb
  have heq : h⁻¹ * (f h - f 0) - f' 0 = h⁻¹ * ((f h - f 0) - h * f' 0) := by
    rw [mul_sub h⁻¹ (f h - f 0) (h * f' 0), ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  rw [heq, abs_mul, abs_inv]
  calc
    |h|⁻¹ * |(f h - f 0) - h * f' 0| ≤ |h|⁻¹ * ((B * |h|) * |h|) :=
      mul_le_mul_of_nonneg_left hrem (inv_nonneg.mpr (abs_nonneg _))
    _ = B * |h| := by
      have hne' : |h| ≠ 0 := abs_ne_zero.mpr hne
      field_simp

/-- A uniform first-order remainder bound determines a convergent family
of derivatives and the genuine derivative of the pointwise limit. -/
theorem exists_tendsto_derivative_of_uniform_slope_error
    {ι : Type*} {l : Filter ι} [NeBot l]
    {f : ι → ℝ → ℝ} {g : ℝ → ℝ} {d : ι → ℝ} {x δ B : ℝ}
    (hδ : 0 < δ) (hB : 0 ≤ B)
    (hf : ∀ h : ℝ, |h| < δ →
      Tendsto (fun i => f i (x + h)) l (𝓝 (g (x + h))))
    (herror : ∀ i h, |h| < δ → h ≠ 0 →
      |h⁻¹ * (f i (x + h) - f i x) - d i| ≤ B * |h|) :
    ∃ D : ℝ, Tendsto d l (𝓝 D) ∧ HasDerivAt g D x := by
  have hzero : Tendsto (fun i => f i x) l (𝓝 (g x)) := by
    simpa only [abs_zero, add_zero] using hf 0 (by simpa only [abs_zero] using hδ)
  have hslope (h : ℝ) (hh : |h| < δ) :
      Tendsto (fun i => h⁻¹ * (f i (x + h) - f i x)) l
        (𝓝 (h⁻¹ * (g (x + h) - g x))) :=
    tendsto_const_nhds.mul ((hf h hh).sub hzero)
  have hcauchy : Cauchy (Filter.map d l) := by
    apply Metric.cauchy_iff.mpr
    refine ⟨inferInstance, ?_⟩
    intro ε hε
    let h : ℝ := min (δ / 2) ((ε / 8) / (B + 1))
    have hpos : 0 < h := lt_min (by positivity) (by positivity)
    have hsmall : |h| < δ := by
      rw [abs_of_pos hpos]
      exact (min_le_left _ _).trans_lt (by linarith)
    have hBh : B * |h| ≤ ε / 8 := by
      have hh : h * (B + 1) ≤ ε / 8 :=
        (le_div_iff₀ (by positivity : 0 < B + 1)).mp (min_le_right _ _)
      rw [abs_of_pos hpos]
      nlinarith
    let b : ℝ := h⁻¹ * (g (x + h) - g x)
    have hnear : ∀ᶠ i in l,
        dist (h⁻¹ * (f i (x + h) - f i x)) b < ε / 8 :=
      (hslope h hsmall).eventually (Metric.ball_mem_nhds b (by positivity))
    refine ⟨Metric.ball b (ε / 2), ?_, ?_⟩
    · change ∀ᶠ i in l, d i ∈ Metric.ball b (ε / 2)
      filter_upwards [hnear] with i hi
      have he := (herror i h hsmall hpos.ne').trans hBh
      rw [Metric.mem_ball, Real.dist_eq]
      have ht : |d i - b| ≤
          |h⁻¹ * (f i (x + h) - f i x) - d i| +
            |h⁻¹ * (f i (x + h) - f i x) - b| := by
        calc
          |d i - b| ≤ |d i - h⁻¹ * (f i (x + h) - f i x)| +
              |h⁻¹ * (f i (x + h) - f i x) - b| := abs_sub_le _ _ _
          _ = _ := by rw [abs_sub_comm (d i)]
      rw [Real.dist_eq] at hi
      linarith
    · intro u hu v hv
      have hu' : dist u b < ε / 2 := hu
      have hv' : dist b v < ε / 2 := by simpa only [Metric.mem_ball, dist_comm] using hv
      exact (dist_triangle u b v).trans_lt (by linarith)
  obtain ⟨D, hD⟩ := cauchy_map_iff_exists_tendsto.mp hcauchy
  refine ⟨D, hD, ?_⟩
  have hlimiterror (h : ℝ) (hh : |h| < δ) (hne : h ≠ 0) :
      |h⁻¹ * (g (x + h) - g x) - D| ≤ B * |h| :=
    le_of_tendsto (((hslope h hh).sub hD).abs)
      (Eventually.of_forall (fun i => herror i h hh hne))
  have hnear : ∀ᶠ h : ℝ in 𝓝 (0 : ℝ), |h| < δ := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with h hh
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hh
  have hbound : ∀ᶠ h : ℝ in 𝓝[≠] (0 : ℝ),
      |h⁻¹ * (g (x + h) - g x) - D| ≤ B * |h| := by
    filter_upwards [hnear.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with h hh hne
    exact hlimiterror h hh hne
  have hsmall : Tendsto (fun h : ℝ => B * |h|) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    simpa only [abs_zero, mul_zero] using
      (tendsto_const_nhds.mul ((continuous_abs.tendsto (0 : ℝ)).mono_left
        nhdsWithin_le_nhds) :
        Tendsto (fun h : ℝ => B * |h|) (𝓝[≠] (0 : ℝ)) (𝓝 (B * |(0 : ℝ)|)))
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Real.norm_eq_abs, smul_eq_mul] using
    squeeze_zero' (Eventually.of_forall (fun h : ℝ =>
      abs_nonneg (h⁻¹ * (g (x + h) - g x) - D))) hbound hsmall

end ContinuousFlexibility.Analysis
