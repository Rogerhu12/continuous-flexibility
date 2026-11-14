module

public import ContinuousFlexibility.Radial.ModeCompactLocal
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Affine compression of radial test functions

A test whose ordinary support lies in an open interval can be compressed
towards its midpoint. Its compressed topological supports lie strictly
inside the interval. The tests and their first two derivatives converge
against every integrable radial coefficient.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology ContDiff

def matchedTestScale (n : ℕ) : ℝ := 1 + 1 / ((n : ℝ) + 1)

theorem matchedTestScale_one_lt (n : ℕ) : 1 < matchedTestScale n := by
  unfold matchedTestScale
  have hn : 0 < (n : ℝ) + 1 := by positivity
  linarith [one_div_pos.mpr hn]

theorem matchedTestScale_tendsto :
    Tendsto matchedTestScale atTop (𝓝 (1 : ℝ)) := by
  change Tendsto (fun n : ℕ => 1 + 1 / ((n : ℝ) + 1)) atTop (𝓝 (1 : ℝ))
  simpa only [add_zero] using
    (tendsto_const_nhds (x := (1 : ℝ))).add
      (tendsto_one_div_add_atTop_nhds_zero_nat : Tendsto
        (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 (0 : ℝ)))

def matchedTestDilate (c s : ℝ) (ψ : ℝ → ℝ) (r : ℝ) : ℝ :=
  ψ (c + s * (r - c))

theorem matchedTestDilate_contDiff (c s : ℝ) {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) :
    ContDiff ℝ ∞ (matchedTestDilate c s ψ) := by
  unfold matchedTestDilate
  exact hψ.comp (contDiff_const.add (contDiff_const.mul (contDiff_id.sub contDiff_const)))

theorem matchedTestDilate_hasDerivAt (c s : ℝ) {ψ : ℝ → ℝ}
    (hψ : Differentiable ℝ ψ) (r : ℝ) :
    HasDerivAt (matchedTestDilate c s ψ)
      (s * deriv ψ (c + s * (r - c))) r := by
  have ha : HasDerivAt (fun t : ℝ => c + s * (t - c)) s r := by
    simpa using (((hasDerivAt_id r).sub_const c).const_mul s).const_add c
  have he := (hψ (c + s * (r - c))).hasDerivAt.comp r ha
  exact he.congr_deriv (mul_comm _ _)

theorem matchedTestDilate_deriv (c s : ℝ) {ψ : ℝ → ℝ}
    (hψ : Differentiable ℝ ψ) :
    deriv (matchedTestDilate c s ψ) =
      fun r => s * deriv ψ (c + s * (r - c)) := by
  funext r
  exact (matchedTestDilate_hasDerivAt c s hψ r).deriv

theorem matchedTestDilate_deriv_deriv (c s : ℝ) {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) :
    deriv (deriv (matchedTestDilate c s ψ)) =
      fun r => s ^ 2 * deriv (deriv ψ) (c + s * (r - c)) := by
  have hdψ : ContDiff ℝ ∞ (deriv ψ) := (contDiff_infty_iff_deriv.mp hψ).2
  rw [matchedTestDilate_deriv c s (hψ.differentiable (by simp))]
  funext r
  have he := (matchedTestDilate_hasDerivAt c s (hdψ.differentiable (by simp)) r).const_mul s
  have he' : HasDerivAt
      (fun t => s * deriv ψ (c + s * (t - c)))
      (s ^ 2 * deriv (deriv ψ) (c + s * (r - c))) r := by
    exact he.congr_deriv (by ring)
  exact he'.deriv

theorem matchedTestDilate_tsupport {a b s : ℝ} (hab : a < b) (hs : 1 < s)
    {ψ : ℝ → ℝ} (hψs : Function.support ψ ⊆ Ioo a b) :
    tsupport (matchedTestDilate ((a + b) / 2) s ψ) ⊆ Ioo a b := by
  let c : ℝ := (a + b) / 2
  have hc : Continuous (fun r : ℝ => c + s * (r - c)) := by fun_prop
  have hpre : tsupport (matchedTestDilate c s ψ) ⊆
      (fun r : ℝ => c + s * (r - c)) ⁻¹' Icc a b := by
    apply closure_minimal _ (isClosed_Icc.preimage hc)
    intro r hr
    exact Ioo_subset_Icc_self (hψs hr)
  intro r hr
  obtain ⟨hra, hrb⟩ := hpre hr
  have hs0 : 0 ≤ s := by linarith
  have hca : 0 < c - a := by dsimp only [c]; linarith
  have hbc : 0 < b - c := by dsimp only [c]; linarith
  constructor
  · by_contra h
    have hrle : r ≤ a := le_of_not_gt h
    have hmul : s * (r - a) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hs0 (sub_nonpos.mpr hrle)
    have hgap : 0 < (s - 1) * (c - a) := mul_pos (sub_pos.mpr hs) hca
    nlinarith
  · by_contra h
    have hrge : b ≤ r := le_of_not_gt h
    have hmul : 0 ≤ s * (r - b) :=
      mul_nonneg hs0 (sub_nonneg.mpr hrge)
    have hgap : 0 < (s - 1) * (b - c) := mul_pos (sub_pos.mpr hs) hbc
    nlinarith

theorem matchedTestDilate_hasCompactSupport {a b s : ℝ} (hab : a < b) (hs : 1 < s)
    {ψ : ℝ → ℝ} (hψs : Function.support ψ ⊆ Ioo a b) :
    HasCompactSupport (matchedTestDilate ((a + b) / 2) s ψ) := by
  apply HasCompactSupport.of_support_subset_isCompact (show IsCompact (Icc a b) from isCompact_Icc)
  exact (show Function.support _ ⊆ tsupport _ from subset_closure).trans
    ((matchedTestDilate_tsupport hab hs hψs).trans Ioo_subset_Icc_self)

theorem matchedTestDilate_tendsto_integral {μ : Measure ℝ}
    {g ψ : ℝ → ℝ} (hg : Integrable g μ) (hψ : Continuous ψ)
    (hcψ : HasCompactSupport ψ) (c : ℝ) :
    Tendsto (fun n => ∫ r, g r * matchedTestDilate c (matchedTestScale n) ψ r ∂μ)
      atTop (𝓝 (∫ r, g r * ψ r ∂μ)) := by
  obtain ⟨B, hB⟩ := hψ.bounded_above_of_compact_support hcψ
  apply tendsto_integral_of_dominated_convergence (fun r => ‖g r‖ * B)
  · intro n
    apply hg.aestronglyMeasurable.mul
    apply Continuous.aestronglyMeasurable
    exact hψ.comp (by fun_prop)
  · exact hg.norm.mul_const B
  · intro n
    filter_upwards with r
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hB _) (norm_nonneg _)
  · filter_upwards with r
    have ha : Tendsto (fun n => c + matchedTestScale n * (r - c)) atTop (𝓝 r) := by
      have hlim : Tendsto (fun n => c + matchedTestScale n * (r - c)) atTop
          (𝓝 (c + 1 * (r - c))) :=
        (tendsto_const_nhds (x := c)).add (matchedTestScale_tendsto.mul_const (r - c))
      have he : c + 1 * (r - c) = r := by ring
      simpa only [he] using hlim
    exact tendsto_const_nhds.mul (hψ.continuousAt.tendsto.comp ha)

theorem matchedTestDilate_tendsto_intervalIntegral {a b : ℝ} (hab : a ≤ b)
    {g ψ : ℝ → ℝ} (hg : IntervalIntegrable g volume a b)
    (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ) (c : ℝ) :
    Tendsto (fun n => ∫ r in a..b, g r * matchedTestDilate c (matchedTestScale n) ψ r)
      atTop (𝓝 (∫ r in a..b, g r * ψ r)) := by
  have hi := (intervalIntegrable_iff_integrableOn_Ioo_of_le hab).mp hg
  simpa only [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo] using
    matchedTestDilate_tendsto_integral hi hψ hcψ c

theorem matchedTestDilate_tendsto_deriv_integral {a b : ℝ} (hab : a ≤ b)
    {g ψ : ℝ → ℝ} (hg : IntervalIntegrable g volume a b)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) (c : ℝ) :
    Tendsto (fun n => ∫ r in a..b, g r *
      deriv (matchedTestDilate c (matchedTestScale n) ψ) r)
      atTop (𝓝 (∫ r in a..b, g r * deriv ψ r)) := by
  have hdψ : ContDiff ℝ ∞ (deriv ψ) := (contDiff_infty_iff_deriv.mp hψ).2
  have hi := matchedTestDilate_tendsto_intervalIntegral hab hg hdψ.continuous hcψ.deriv c
  have he (n : ℕ) :
      (∫ r in a..b, g r * deriv (matchedTestDilate c (matchedTestScale n) ψ) r) =
        matchedTestScale n *
          ∫ r in a..b, g r * matchedTestDilate c (matchedTestScale n) (deriv ψ) r := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro r _
    rw [matchedTestDilate_deriv c (matchedTestScale n) (hψ.differentiable (by simp))]
    dsimp only [matchedTestDilate]
    ring
  simp_rw [he]
  simpa only [one_mul] using matchedTestScale_tendsto.mul hi

theorem matchedTestDilate_tendsto_second_integral {a b : ℝ} (hab : a ≤ b)
    {g ψ : ℝ → ℝ} (hg : IntervalIntegrable g volume a b)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) (c : ℝ) :
    Tendsto (fun n => ∫ r in a..b, g r *
      deriv (deriv (matchedTestDilate c (matchedTestScale n) ψ)) r)
      atTop (𝓝 (∫ r in a..b, g r * deriv (deriv ψ) r)) := by
  have hdψ : ContDiff ℝ ∞ (deriv ψ) := (contDiff_infty_iff_deriv.mp hψ).2
  have hddψ : ContDiff ℝ ∞ (deriv (deriv ψ)) := (contDiff_infty_iff_deriv.mp hdψ).2
  have hi := matchedTestDilate_tendsto_intervalIntegral hab hg hddψ.continuous
    hcψ.deriv.deriv c
  have he (n : ℕ) :
      (∫ r in a..b, g r * deriv (deriv (matchedTestDilate c (matchedTestScale n) ψ)) r) =
        matchedTestScale n ^ 2 *
          ∫ r in a..b, g r *
            matchedTestDilate c (matchedTestScale n) (deriv (deriv ψ)) r := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro r _
    rw [matchedTestDilate_deriv_deriv c (matchedTestScale n) hψ]
    dsimp only [matchedTestDilate]
    ring
  simp_rw [he]
  simpa only [one_pow, one_mul] using (matchedTestScale_tendsto.pow 2).mul hi

end ContinuousFlexibility.Radial
