import ContinuousFlexibility.Analysis.N04bFlowFirstVariation

/-!
# Endpoint derivatives from the uniform flow remainder

The endpoint derivative follows by dividing the proved quantitative error
by the nonzero parameter. The uniform velocity expansion and the actual
integral equations are still explicit hypotheses; no N04b trajectory or
parameter regularity of a chart is asserted by this file.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped Topology

/-- The elementary difference-quotient consequence of the uniform
quadratic remainder used by the flow estimate. -/
theorem n04b_hasDerivAt_of_uniform_quadratic_bound
    (F η : ℝ → ℝ) (value c d M L : ℝ)
    (hzero : F 0 = value)
    (hη : Tendsto η (𝓝[≠] (0 : ℝ)) (𝓝 0))
    (hbound : ∀ᶠ q in 𝓝[≠] (0 : ℝ),
      |F q - value - q * c| ≤
        d * |q| * η q + d ^ 2 * q ^ 2 * L * (M + η q)) :
    HasDerivAt F c 0 := by
  have ha : Tendsto (fun q : ℝ => |q|) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    simpa only [abs_zero] using
      (continuous_abs.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have hq0 : ∀ᶠ q : ℝ in 𝓝[≠] (0 : ℝ), q ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with q hq
    simpa using hq
  have hM : Tendsto (fun _ : ℝ => M) (𝓝[≠] (0 : ℝ)) (𝓝 M) :=
    tendsto_const_nhds
  have herr : Tendsto
      (fun q : ℝ => d * η q + d ^ 2 * |q| * L * (M + η q))
      (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    simpa only [mul_zero, zero_mul, add_zero, zero_add] using
      (hη.const_mul d).add (((ha.const_mul (d ^ 2)).mul_const L).mul (hM.add hη))
  have hslope : Tendsto (fun q : ℝ => (F q - value) / q)
      (𝓝[≠] (0 : ℝ)) (𝓝 c) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have he : ∀ᶠ q in 𝓝[≠] (0 : ℝ),
        d * η q + d ^ 2 * |q| * L * (M + η q) < ε :=
      herr.eventually (Iio_mem_nhds hε)
    filter_upwards [hbound, hq0, he] with q hq hq0 hεq
    have hqa : 0 < |q| := abs_pos.mpr hq0
    have hid : (F q - value) / q - c = (F q - value - q * c) / q := by
      field_simp [hq0] <;> ring
    rw [Real.dist_eq, hid, abs_div]
    apply lt_of_le_of_lt _ hεq
    calc
      _ ≤ (d * |q| * η q + d ^ 2 * q ^ 2 * L * (M + η q)) / |q| :=
        div_le_div_of_nonneg_right hq hqa.le
      _ = d * η q + d ^ 2 * |q| * L * (M + η q) := by
        rw [← sq_abs q]
        field_simp [ne_of_gt hqa] <;> ring
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  simpa only [zero_add, hzero, smul_eq_mul, div_eq_mul_inv, mul_comm] using hslope

/-- The actual endpoint derivative follows from a uniform first-order
velocity expansion and actual trajectory integral equations on a
punctured parameter neighborhood. -/
theorem n04b_flow_endpoint_hasDerivAt
    (V Y : ℝ → ℝ → ℝ → ℝ) (v₀ : ℝ → ℝ) (v₁ : ℝ → ℝ → ℝ)
    (η : ℝ → ℝ) (a b M L : ℝ) (hab : a ≤ b) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (h₀ : IntervalIntegrable v₀ volume a b)
    (h₁ : ∀ θ, IntervalIntegrable
      (fun r => v₁ r (n04bFlowReference v₀ a r θ)) volume a b)
    (hfirst : ∀ r ∈ Icc a b, ∀ θ, |v₁ r θ| ≤ M)
    (hLip : ∀ r ∈ Icc a b, ∀ θ φ, |v₁ r θ - v₁ r φ| ≤ L * |θ - φ|)
    (hzero : ∀ θ, Y 0 b θ = n04bFlowReference v₀ a b θ)
    (hη : Tendsto η (𝓝[≠] (0 : ℝ)) (𝓝 0))
    (hdata : ∀ᶠ q in 𝓝[≠] (0 : ℝ),
      0 ≤ η q ∧
      (∀ θ, IntervalIntegrable (fun r => V q r (Y q r θ)) volume a b) ∧
      (∀ θ t, t ∈ Icc a b → Y q t θ = θ + ∫ r in a..t, V q r (Y q r θ)) ∧
      (∀ r ∈ Icc a b, ∀ θ,
        |V q r θ - v₀ r - q * v₁ r θ| ≤ |q| * η q))
    (θ : ℝ) :
    HasDerivAt (fun q => Y q b θ) (n04bFlowFirstVariation v₀ v₁ a b θ) 0 := by
  apply n04b_hasDerivAt_of_uniform_quadratic_bound
    (fun q => Y q b θ) η (n04bFlowReference v₀ a b θ)
    (n04bFlowFirstVariation v₀ v₁ a b θ) (b - a) M L (hzero θ) hη
  filter_upwards [hdata] with q hq
  exact n04b_flow_first_variation_bound (V q) (Y q) v₀ v₁ a b q (η q) M L
    hab hq.1 hM hL h₀ hq.2.1 h₁ hq.2.2.1 hfirst hLip hq.2.2.2
    θ b ⟨hab, le_rfl⟩

end ContinuousFlexibility.Analysis
