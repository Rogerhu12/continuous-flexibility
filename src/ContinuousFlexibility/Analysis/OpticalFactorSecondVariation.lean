import ContinuousFlexibility.Analysis.OpticalTravelSecondVariation

/-!
# Second variation with a fixed possibly vanishing optical factor

A simple turning point is kept entirely in the fixed continuous factor
`a r`.  The parameter-dependent factor `sqrt (1 + t * v r)` stays
uniformly positive on a common parameter interval.  Thus both actual
parameter derivatives are obtained on the full closed radial interval,
including its turning points.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped Topology ContDiff

theorem hasDerivAt_sqrtFactor_integral_twice
    {a v : ℝ → ℝ} {l h : ℝ} (hlh : l < h)
    (ha : ContinuousOn a (Icc l h)) (hv : ContinuousOn v (Icc l h)) :
    HasDerivAt (fun t : ℝ => ∫ r in l..h, a r * Real.sqrt (1 + t * v r))
      (∫ r in l..h, a r * v r / 2) 0 ∧
    HasDerivAt (deriv (fun t : ℝ => ∫ r in l..h, a r * Real.sqrt (1 + t * v r)))
      (-(∫ r in l..h, a r * v r ^ 2 / 4)) 0 := by
  obtain ⟨δ, hδ, hrad⟩ := sqrtAffine_positive_parameter_interval
    (q := fun _ => 1) hlh continuousOn_const hv (fun _ _ => zero_lt_one)
  let K := Icc (-δ) δ ×ˢ Icc l h
  let U := Ioo (-δ) δ
  let Y (t r : ℝ) := Real.sqrt (1 + t * v r)
  let F (t r : ℝ) := a r * Y t r
  let G (t r : ℝ) := a r * v r / (2 * Y t r)
  let H (t r : ℝ) := -(a r * v r ^ 2 / (4 * Y t r ^ 3))
  have haK : ContinuousOn (fun p : ℝ × ℝ => a p.2) K :=
    ha.comp continuous_snd.continuousOn (fun p hp => hp.2)
  have hvK : ContinuousOn (fun p : ℝ × ℝ => v p.2) K :=
    hv.comp continuous_snd.continuousOn (fun p hp => hp.2)
  have hYc : ContinuousOn (fun p : ℝ × ℝ => Y p.1 p.2) K :=
    Real.continuous_sqrt.comp_continuousOn
      (continuousOn_const.add (continuous_fst.continuousOn.mul hvK))
  have hYpos (p : ℝ × ℝ) (hp : p ∈ K) : 0 < Y p.1 p.2 :=
    Real.sqrt_pos.mpr (hrad p.1 hp.1 p.2 hp.2)
  have hFc : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) K := haK.mul hYc
  have hGc : ContinuousOn (fun p : ℝ × ℝ => G p.1 p.2) K :=
    (haK.mul hvK).div (continuousOn_const.mul hYc)
      (fun p hp => (mul_pos zero_lt_two (hYpos p hp)).ne')
  have hHc : ContinuousOn (fun p : ℝ × ℝ => H p.1 p.2) K :=
    ((haK.mul (hvK.pow 2)).div (continuousOn_const.mul (hYc.pow 3))
      (fun p hp => (mul_pos (by norm_num) (pow_pos (hYpos p hp) 3)).ne')).neg
  have hYd (t : ℝ) (ht : t ∈ U) (r : ℝ) (hr : r ∈ Icc l h) :
      HasDerivAt (fun s => Y s r) (v r / (2 * Y t r)) t := by
    have hlin : HasDerivAt (fun s : ℝ => 1 + s * v r) (v r) t := by
      simpa only [id_eq, one_mul] using ((hasDerivAt_id t).mul_const (v r)).const_add 1
    exact hlin.sqrt (hrad t (Ioo_subset_Icc_self ht) r hr).ne'
  have hFd (t : ℝ) (ht : t ∈ U) (r : ℝ) (hr : r ∈ Icc l h) :
      HasDerivAt (fun s => F s r) (G t r) t := by
    convert (hYd t ht r hr).const_mul (a r) using 1 <;> dsimp only [F, G] <;> ring
  have hGd (t : ℝ) (ht : t ∈ U) (r : ℝ) (hr : r ∈ Icc l h) :
      HasDerivAt (fun s => G s r) (H t r) t := by
    have hp : 0 < Y t r := hYpos (t, r) ⟨Ioo_subset_Icc_self ht, hr⟩
    have hd := (hasDerivAt_const t (a r * v r)).div
      ((hYd t ht r hr).const_mul 2) (mul_pos zero_lt_two hp).ne'
    convert hd using 1
    dsimp only [G, H]
    field_simp [hp.ne'] <;> ring
  have h0 : (0 : ℝ) ∈ U := ⟨neg_neg_of_pos hδ, hδ⟩
  have hFi (t : ℝ) (ht : t ∈ U) :=
    hasDerivAt_intervalIntegral_of_compact_rectangle hlh ht hFc hGc hFd
  have hGi := hasDerivAt_intervalIntegral_of_compact_rectangle hlh h0 hGc hHc hGd
  have heq : deriv (fun t : ℝ => ∫ r in l..h, F t r) =ᶠ[𝓝 (0 : ℝ)]
      (fun t => ∫ r in l..h, G t r) := by
    filter_upwards [Ioo_mem_nhds h0.1 h0.2] with t ht
    exact (hFi t ht).deriv
  constructor
  · simpa only [F, G, Y, zero_mul, add_zero, Real.sqrt_one, mul_one] using hFi 0 h0
  · simpa only [F, G, H, Y, zero_mul, add_zero, Real.sqrt_one, one_pow, mul_one,
      intervalIntegral.integral_neg] using hGi.congr_of_eventuallyEq heq

theorem sqrtFactor_variation_pointwise {a v B c : ℝ}
    (ha : 0 ≤ a) (hB : |a ^ 2 * v| ≤ B) (hc : 0 ≤ c) :
    3 * c ^ 2 * (a * v / 2) - 2 * c ^ 3 ≤
      (B / 2) * (a * v ^ 2 / 4) := by
  by_cases ha0 : a = 0
  · simpa only [ha0, zero_mul, zero_div, mul_zero, zero_sub] using
      neg_nonpos.mpr (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (pow_nonneg hc 3))
  have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hfirst : a ^ 2 * v / (2 * a) = a * v / 2 := by
    field_simp [ha0] <;> ring
  have hsecond : (a ^ 2 * v) ^ 2 / (4 * a ^ 3) = a * v ^ 2 / 4 := by
    field_simp [ha0] <;> ring
  simpa only [hfirst, hsecond] using
    sqrtAffine_variation_pointwise (u := a ^ 2 * v) hap hB hc

theorem sqrtFactor_normalized_curvature_bound
    {a v : ℝ → ℝ} {l h B : ℝ} (hlh : l < h)
    (ha : ContinuousOn a (Icc l h)) (hv : ContinuousOn v (Icc l h))
    (ha0 : ∀ r ∈ Icc l h, 0 ≤ a r)
    (hB : ∀ r ∈ Icc l h, |a r ^ 2 * v r| ≤ B)
    (hunit : (∫ r in l..h, a r * v r / 2) = 1) :
    2 ≤ (h - l) ^ 2 * B * ∫ r in l..h, a r * v r ^ 2 / 4 := by
  let f (r : ℝ) := a r * v r / 2
  let d (r : ℝ) := a r * v r ^ 2 / 4
  let c : ℝ := (h - l)⁻¹
  have hc : 0 ≤ c := (inv_pos.mpr (sub_pos.mpr hlh)).le
  have hfi : IntervalIntegrable f volume l h :=
    ((ha.mul hv).div_const 2).intervalIntegrable_of_Icc hlh.le
  have hdi : IntervalIntegrable d volume l h :=
    ((ha.mul (hv.pow 2)).div_const 4).intervalIntegrable_of_Icc hlh.le
  have hineq : (∫ r in l..h, 3 * c ^ 2 * f r - 2 * c ^ 3) ≤
      ∫ r in l..h, (B / 2) * d r :=
    intervalIntegral.integral_mono_on hlh.le
      ((hfi.const_mul _).sub intervalIntegrable_const) (hdi.const_mul _)
      (fun r hr => sqrtFactor_variation_pointwise (ha0 r hr) (hB r hr) hc)
  have hleft : (∫ r in l..h, 3 * c ^ 2 * f r - 2 * c ^ 3) = 1 / (h - l) ^ 2 := by
    rw [intervalIntegral.integral_sub (hfi.const_mul _) intervalIntegrable_const,
      intervalIntegral.integral_const_mul, hunit, intervalIntegral.integral_const, smul_eq_mul]
    dsimp only [c]
    field_simp [(sub_pos.mpr hlh).ne'] <;> ring
  rw [hleft, intervalIntegral.integral_const_mul] at hineq
  have hmul := (div_le_iff₀ (sq_pos_of_pos (sub_pos.mpr hlh))).mp hineq
  change 1 ≤ ((B / 2) * ∫ r in l..h, d r) * (h - l) ^ 2 at hmul
  calc
    2 ≤ 2 * (((B / 2) * ∫ r in l..h, d r) * (h - l) ^ 2) := by linarith only [hmul]
    _ = _ := by dsimp only [d]; ring

/-- The lower bound concerns the two actual derivatives of the same
integral.  It remains valid when the fixed factor vanishes at either
endpoint or at additional points. -/
theorem sqrtFactor_normalized_secondDerivative_lower_bound
    {a v : ℝ → ℝ} {l h B D : ℝ} (hlh : l < h)
    (ha : ContinuousOn a (Icc l h)) (hv : ContinuousOn v (Icc l h))
    (ha0 : ∀ r ∈ Icc l h, 0 ≤ a r)
    (hB : ∀ r ∈ Icc l h, |a r ^ 2 * v r| ≤ B)
    (hunit : HasDerivAt (fun t : ℝ => ∫ r in l..h, a r * Real.sqrt (1 + t * v r)) 1 0)
    (hD : |deriv (deriv (fun t : ℝ => ∫ r in l..h, a r * Real.sqrt (1 + t * v r))) 0| ≤ D) :
    2 ≤ (h - l) ^ 2 * B * D := by
  obtain ⟨hfirst, hsecond⟩ := hasDerivAt_sqrtFactor_integral_twice hlh ha hv
  have hunitInt : (∫ r in l..h, a r * v r / 2) = 1 := hfirst.unique hunit
  have hcurv : (∫ r in l..h, a r * v r ^ 2 / 4) ≤ D := by
    calc
      _ = -deriv (deriv (fun t : ℝ => ∫ r in l..h, a r * Real.sqrt (1 + t * v r))) 0 := by
        rw [hsecond.deriv, neg_neg]
      _ ≤ D := (neg_le_abs _).trans hD
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB l ⟨le_rfl, hlh.le⟩)
  exact (sqrtFactor_normalized_curvature_bound hlh ha hv ha0 hB hunitInt).trans
    (mul_le_mul_of_nonneg_left hcurv (mul_nonneg (sq_nonneg _) hB0))

end ContinuousFlexibility.Analysis
