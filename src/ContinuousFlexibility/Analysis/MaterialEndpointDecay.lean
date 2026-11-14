module

public import ContinuousFlexibility.Statements.Analysis

/-!
# Material decay in ordinary endpoint distance

In the endpoint variable, distance is (d_0 e^{-X^2}) and (H) is
(e^{-2X^3/3}). A positive power of (H) therefore absorbs any fixed
inverse power of the ordinary distance, in addition to the material weights.
-/

@[expose] public section

noncomputable section

open Set Filter
open scoped Topology

namespace ContinuousFlexibility.Analysis

theorem tendsto_endpoint_H_rpow_div_pow_zero {d₀ γ : ℝ}
    (hd₀ : 0 < d₀) (hγ : 0 < γ) (k : ℕ) :
    Tendsto (fun d => materialH (endpointX d₀ d) ^ γ / d ^ k)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hc : 0 < γ / 3 := div_pos hγ (by norm_num)
  have hp : Tendsto (fun x : ℝ => -(γ / 3) * x ^ (3 : ℕ)) atTop atBot :=
    (tendsto_pow_atTop (by decide : (3 : ℕ) ≠ 0)).const_mul_atTop_of_neg (neg_lt_zero.mpr hc)
  have hexponent : Tendsto (fun x : ℝ => (-2 * x ^ 3 / 3) * γ + (k : ℝ) * x ^ 2)
      atTop atBot := by
    apply tendsto_atBot.mpr
    intro B
    filter_upwards [hp.eventually_le_atBot B, eventually_ge_atTop (3 * (k : ℝ) / γ)]
      with x hxB hx
    have hk : (k : ℝ) ≤ γ / 3 * x := by
      calc
        (k : ℝ) = γ / 3 * (3 * (k : ℝ) / γ) := by field_simp [hγ.ne']
        _ ≤ γ / 3 * x := mul_le_mul_of_nonneg_left hx hc.le
    have hmul := mul_nonneg (sub_nonneg.mpr hk) (sq_nonneg x)
    exact le_trans (by nlinarith only [hmul]) hxB
  have hmodel : Tendsto (fun x : ℝ =>
      (d₀ ^ k)⁻¹ * Real.exp ((-2 * x ^ 3 / 3) * γ + (k : ℝ) * x ^ 2))
      atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_apply] using
      (Real.tendsto_exp_atBot.comp hexponent).const_mul ((d₀ ^ k)⁻¹)
  apply (hmodel.comp (tendsto_endpointX_atTop hd₀)).congr'
  have hsmall : ∀ᶠ d in 𝓝[>] (0 : ℝ), d < d₀ :=
    nhdsWithin_le_nhds (Iio_mem_nhds hd₀)
  filter_upwards [eventually_mem_nhdsWithin, hsmall] with d hd hlt
  change 0 < d at hd
  let x := endpointX d₀ d
  change (d₀ ^ k)⁻¹ * Real.exp ((-2 * x ^ 3 / 3) * γ + (k : ℝ) * x ^ 2) =
    materialH x ^ γ / d ^ k
  have hdist : endpointDistance d₀ x = d := endpointDistance_endpointX hd₀ hd hlt
  have hpow : (Real.exp (-x ^ 2)) ^ k = Real.exp (-((k : ℝ) * x ^ 2)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [← hdist, materialH, ← Real.exp_mul, endpointDistance, mul_pow, hpow, Real.exp_neg]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, Real.exp_add]
  ring

theorem tendsto_endpoint_H_rpow_M_rpow_div_pow_zero {d₀ γ : ℝ}
    (hd₀ : 0 < d₀) (hγ : 0 < γ) (A : ℝ) (k : ℕ) :
    Tendsto (fun d => materialH (endpointX d₀ d) ^ γ * materialM (endpointX d₀ d) ^ A / d ^ k)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hhalf : 0 < γ / 2 := half_pos hγ
  have h := (tendsto_endpoint_H_rpow_M_rpow_zero hd₀ A hhalf).mul
    (tendsto_endpoint_H_rpow_div_pow_zero hd₀ hhalf k)
  rw [zero_mul] at h
  apply h.congr'
  refine Filter.Eventually.of_forall fun d => ?_
  have hpow : materialH (endpointX d₀ d) ^ (γ / 2) *
      materialH (endpointX d₀ d) ^ (γ / 2) = materialH (endpointX d₀ d) ^ γ := by
    rw [← Real.rpow_add (materialH_pos _), show γ / 2 + γ / 2 = γ by ring]
  change (materialH (endpointX d₀ d) ^ (γ / 2) * materialM (endpointX d₀ d) ^ A) *
      (materialH (endpointX d₀ d) ^ (γ / 2) / d ^ k) = _
  calc
    _ = (materialH (endpointX d₀ d) ^ (γ / 2) * materialH (endpointX d₀ d) ^ (γ / 2)) *
        materialM (endpointX d₀ d) ^ A / d ^ k := by ring
    _ = _ := by rw [hpow]

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

/-- A uniform two-ended estimate in the actual material data. Its radius
threshold depends on the weights and the requested powers. -/
theorem exists_material_endpoint_decay {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) {γ ε : ℝ} (hγ : 0 < γ) (hε : 0 < ε)
    (A : ℝ) (k : ℕ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r ∈ Ioo D.a D.b, endpointDistance D r < δ →
      T.H r ^ γ * T.M r ^ A / endpointDistance D r ^ k < ε := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, ⟨d₀, δ₀, hd₀, hδ₀, _, hleft, hright⟩, _⟩ := hT
  have ht := Analysis.tendsto_endpoint_H_rpow_M_rpow_div_pow_zero hd₀ hγ A k
  have he : ∀ᶠ d in 𝓝[>] (0 : ℝ),
      Analysis.materialH (Analysis.endpointX d₀ d) ^ γ *
        Analysis.materialM (Analysis.endpointX d₀ d) ^ A / d ^ k < ε :=
    ht.eventually (Iio_mem_nhds hε)
  obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhds_iff.mp (eventually_nhdsWithin_iff.mp he)
  have hb (d : ℝ) (hd : 0 < d) (hnear : d < δ) :
      Analysis.materialH (Analysis.endpointX d₀ d) ^ γ *
        Analysis.materialM (Analysis.endpointX d₀ d) ^ A / d ^ k < ε :=
    hsub (by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hd] using hnear) hd
  refine ⟨min δ δ₀, lt_min hδ hδ₀, fun r hr hnear => ?_⟩
  unfold endpointDistance at hnear ⊢
  by_cases hs : r - D.a ≤ D.b - r
  · rw [min_eq_left hs] at hnear ⊢
    have hrl : r ∈ Ioo D.a (D.a + δ₀) :=
      ⟨hr.1, by linarith [hnear.trans_le (min_le_right δ δ₀)]⟩
    obtain ⟨_, hH, _, hM⟩ := hleft r hrl
    rw [hH, hM]
    exact hb _ (sub_pos.mpr hr.1) (hnear.trans_le (min_le_left δ δ₀))
  · rw [min_eq_right (le_of_not_ge hs)] at hnear ⊢
    have hrr : r ∈ Ioo (D.b - δ₀) D.b :=
      ⟨by linarith [hnear.trans_le (min_le_right δ δ₀)], hr.2⟩
    obtain ⟨_, hH, _, hM⟩ := hright r hrr
    rw [hH, hM]
    exact hb _ (sub_pos.mpr hr.2) (hnear.trans_le (min_le_left δ δ₀))

end ContinuousFlexibility.Statements
