import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Real.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# One normal derivative on an interval without boundary conditions

This file formalizes the elementary interval estimate used for
`eq:rad-eq-rm39` (§6) and `eq:vol-reference-first-normal-bound` (§8) of the
manuscript.  No boundary data are imposed.

* `interval_abs_deriv_le`: a pointwise bound for `u'` on `[a, a + h]` by the
  `L¹` norms of `u` and `u''` (mean value theorem plus the fundamental theorem
  of calculus).
* `interval_integral_deriv_sq_le`: its `L²` (additive, interpolation) form.
* `unit_integral_deriv_sq_le`: the `ε`-form on `[0, 1]` obtained by
  subdividing into `N` equal intervals:
  `‖u'‖² ≤ 162 N² ‖u‖² + (2 / N²) ‖u''‖²`.
* `unit_first_normal_bound`, `unit_second_normal_bound`: for a solution of
  `A u'' + B u' + (j² C + D₀) u = F` with `|A| ≥ 1 / K` and coefficients
  bounded by `K`, the first and second derivatives are controlled by `F` and
  `(1 + j²)`-weighted (resp. `(1 + j²)²`-weighted) `L²` norms of `u`.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory intervalIntegral

/-- Regularity facts extracted from global `C²` regularity. -/
theorem contDiff_two_interval_facts {u : ℝ → ℝ} (hu : ContDiff ℝ 2 u) :
    Continuous u ∧ Differentiable ℝ u ∧ Continuous (deriv u) ∧
      Differentiable ℝ (deriv u) ∧ Continuous (deriv (deriv u)) := by
  have h2 : ContDiff ℝ (1 + 1) u := by rw [one_add_one_eq_two]; exact hu
  have h1 : ContDiff ℝ 1 (deriv u) := (contDiff_succ_iff_deriv.mp h2).2.2
  exact ⟨hu.continuous, hu.differentiable (by norm_num), h1.continuous,
    h1.differentiable (by norm_num), h1.continuous_deriv le_rfl⟩

/-- A continuous function on `[p, q]` has a point where `(q - p) |g|` is at most
the integral of `|g|`. -/
theorem exists_mul_abs_le_integral_abs {g : ℝ → ℝ} (hg : Continuous g) {p q : ℝ}
    (hpq : p < q) : ∃ s ∈ Icc p q, (q - p) * |g s| ≤ ∫ t in p..q, |g t| := by
  have hga : Continuous fun t => |g t| := continuous_abs.comp hg
  obtain ⟨s, hs, hsmin⟩ :=
    isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hpq.le) hga.continuousOn
  refine ⟨s, hs, ?_⟩
  have hmono : ∫ _ in p..q, |g s| ≤ ∫ t in p..q, |g t| :=
    intervalIntegral.integral_mono_on hpq.le intervalIntegrable_const
      (hga.intervalIntegrable p q) (fun t ht => hsmin ht)
  rwa [intervalIntegral.integral_const, smul_eq_mul] at hmono

/-- Cauchy--Schwarz on an interval: `(∫ |g|)² ≤ (q - p) ∫ g²`. -/
theorem sq_integral_abs_le_mul_integral_sq {g : ℝ → ℝ} (hg : Continuous g) {p q : ℝ}
    (hpq : p ≤ q) : (∫ t in p..q, |g t|) ^ 2 ≤ (q - p) * ∫ t in p..q, g t ^ 2 := by
  rcases hpq.eq_or_lt with rfl | hlt
  · simp
  have hL : 0 < q - p := sub_pos.2 hlt
  have hga : Continuous fun t => |g t| := continuous_abs.comp hg
  have hgen : ∀ c : ℝ, 2 * c * ∫ t in p..q, |g t| ≤
      (∫ t in p..q, g t ^ 2) + (q - p) * c ^ 2 := by
    intro c
    have hpt : ∀ t ∈ Icc p q, 2 * c * |g t| ≤ g t ^ 2 + c ^ 2 := fun t _ => by
      nlinarith [sq_nonneg (|g t| - c), sq_abs (g t)]
    have hint := intervalIntegral.integral_mono_on (μ := volume) hpq
      ((show Continuous fun t => 2 * c * |g t| by fun_prop).intervalIntegrable p q)
      ((show Continuous fun t => g t ^ 2 + c ^ 2 by fun_prop).intervalIntegrable p q) hpt
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add
        ((show Continuous fun t => g t ^ 2 by fun_prop).intervalIntegrable p q)
        intervalIntegrable_const,
      intervalIntegral.integral_const, smul_eq_mul] at hint
    exact hint
  obtain ⟨c, hc⟩ : ∃ c : ℝ, ∫ t in p..q, |g t| = (q - p) * c :=
    ⟨(∫ t in p..q, |g t|) / (q - p), by field_simp⟩
  have h1 := hgen c
  rw [hc] at h1 ⊢
  nlinarith [mul_le_mul_of_nonneg_left h1 hL.le]

/-- The absolute value of an interval integral over a subinterval of `[a, b]`
is bounded by the integral of the absolute value over `[a, b]`. -/
theorem abs_integral_le_integral_abs_of_mem {g : ℝ → ℝ} (hg : Continuous g)
    {a b p q : ℝ} (hp : p ∈ Icc a b) (hq : q ∈ Icc a b) :
    |∫ t in p..q, g t| ≤ ∫ t in a..b, |g t| := by
  have hga : Continuous fun t => |g t| := continuous_abs.comp hg
  have hnn : (0 : ℝ → ℝ) ≤ᵐ[volume.restrict (Ioc a b)] fun t => |g t| :=
    Filter.Eventually.of_forall fun t => abs_nonneg (g t)
  rcases le_total p q with hpq | hqp
  · calc |∫ t in p..q, g t| ≤ ∫ t in p..q, |g t| :=
          intervalIntegral.abs_integral_le_integral_abs hpq
      _ ≤ ∫ t in a..b, |g t| :=
          intervalIntegral.integral_mono_interval hp.1 hpq hq.2 hnn
            (hga.intervalIntegrable a b)
  · rw [intervalIntegral.integral_symm, abs_neg]
    calc |∫ t in q..p, g t| ≤ ∫ t in q..p, |g t| :=
          intervalIntegral.abs_integral_le_integral_abs hqp
      _ ≤ ∫ t in a..b, |g t| :=
          intervalIntegral.integral_mono_interval hq.1 hqp hp.2 hnn
            (hga.intervalIntegrable a b)

/-- Item 1: pointwise bound for `u'` on one interval, without boundary
conditions. -/
theorem interval_abs_deriv_le {u : ℝ → ℝ} (hu : ContDiff ℝ 2 u) {a h : ℝ} (hh : 0 < h)
    {x : ℝ} (hx : x ∈ Icc a (a + h)) :
    |deriv u x| ≤
      9 / h ^ 2 * (∫ t in a..a + h, |u t|) + ∫ t in a..a + h, |deriv (deriv u) t| := by
  obtain ⟨hcu, hdu, _hcd, hdd, hcdd⟩ := contDiff_two_interval_facts hu
  have hga : Continuous fun t => |u t| := continuous_abs.comp hcu
  obtain ⟨s, hs, hs'⟩ := exists_mul_abs_le_integral_abs hcu
    (show a < a + h / 3 by linarith)
  obtain ⟨t, ht, ht'⟩ := exists_mul_abs_le_integral_abs hcu
    (show a + 2 * h / 3 < a + h by linarith)
  have e1 : a + h / 3 - a = h / 3 := by ring
  have e2 : a + h - (a + 2 * h / 3) = h / 3 := by ring
  rw [e1] at hs'
  rw [e2] at ht'
  have hst : s < t := by linarith [hs.2, ht.1]
  have hts : h / 3 ≤ t - s := by linarith [hs.2, ht.1]
  obtain ⟨ξ, hξ, hξeq⟩ := exists_deriv_eq_slope u hst hcu.continuousOn
    hdu.differentiableOn
  -- splitting the integral of `|u|` into thirds
  have hsplit : (∫ t in a..a + h / 3, |u t|) + (∫ t in a + 2 * h / 3..a + h, |u t|) ≤
      ∫ t in a..a + h, |u t| := by
    have i1 := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hga.intervalIntegrable a (a + h / 3)) (hga.intervalIntegrable (a + h / 3) (a + h))
    have i2 := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hga.intervalIntegrable (a + h / 3) (a + 2 * h / 3))
      (hga.intervalIntegrable (a + 2 * h / 3) (a + h))
    have hmid : 0 ≤ ∫ t in a + h / 3..a + 2 * h / 3, |u t| :=
      intervalIntegral.integral_nonneg (by linarith) (fun _ _ => abs_nonneg _)
    linarith
  -- bound on `u'` at the mean value point
  have key : h / 3 * |deriv u ξ| ≤ |u t| + |u s| := by
    rw [hξeq, abs_div, abs_of_pos (sub_pos.2 hst)]
    have hnum : |u t - u s| ≤ |u t| + |u s| := by
      rw [abs_le]
      constructor <;> linarith [le_abs_self (u t), neg_abs_le (u t), le_abs_self (u s),
        neg_abs_le (u s)]
    have hne : t - s ≠ 0 := (sub_pos.2 hst).ne'
    calc h / 3 * (|u t - u s| / (t - s)) ≤ (t - s) * (|u t - u s| / (t - s)) :=
          mul_le_mul_of_nonneg_right hts (div_nonneg (abs_nonneg _) (sub_pos.2 hst).le)
      _ = |u t - u s| := by field_simp
      _ ≤ |u t| + |u s| := hnum
  have k2 : h ^ 2 * |deriv u ξ| ≤ 9 * ∫ t in a..a + h, |u t| := by
    nlinarith [mul_le_mul_of_nonneg_left key (by linarith : (0 : ℝ) ≤ 3 * h)]
  have hξb : |deriv u ξ| ≤ 9 / h ^ 2 * ∫ t in a..a + h, |u t| := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    linarith
  -- fundamental theorem of calculus from `ξ` to `x`
  have hξmem : ξ ∈ Icc a (a + h) := ⟨by linarith [hs.1, hξ.1], by linarith [ht.2, hξ.2]⟩
  have hftc : ∫ y in ξ..x, deriv (deriv u) y = deriv u x - deriv u ξ :=
    intervalIntegral.integral_deriv_eq_sub (fun y _ => hdd y)
      (hcdd.intervalIntegrable ξ x)
  have hbd : |deriv u x - deriv u ξ| ≤ ∫ t in a..a + h, |deriv (deriv u) t| := by
    rw [← hftc]
    exact abs_integral_le_integral_abs_of_mem hcdd hξmem hx
  have htri := abs_sub_abs_le_abs_sub (deriv u x) (deriv u ξ)
  linarith

/-- Item 2: the `L²` form on one interval. -/
theorem interval_integral_deriv_sq_le {u : ℝ → ℝ} (hu : ContDiff ℝ 2 u) {a h : ℝ}
    (hh : 0 < h) :
    ∫ x in a..a + h, deriv u x ^ 2 ≤
      162 / h ^ 2 * (∫ x in a..a + h, u x ^ 2) +
        2 * h ^ 2 * ∫ x in a..a + h, deriv (deriv u) x ^ 2 := by
  obtain ⟨hcu, _hdu, hcd, _hdd, hcdd⟩ := contDiff_two_interval_facts hu
  have hga : Continuous fun t => |u t| := continuous_abs.comp hcu
  have hS0 : 0 ≤ ∫ t in a..a + h, |u t| :=
    intervalIntegral.integral_nonneg (by linarith) (fun _ _ => abs_nonneg _)
  have hQ0 : 0 ≤ ∫ t in a..a + h, |deriv (deriv u) t| :=
    intervalIntegral.integral_nonneg (by linarith) (fun _ _ => abs_nonneg _)
  have hP0 : 0 ≤ 9 / h ^ 2 * ∫ t in a..a + h, |u t| := by positivity
  have hpt : ∀ x ∈ Icc a (a + h), deriv u x ^ 2 ≤
      2 * (9 / h ^ 2 * ∫ t in a..a + h, |u t|) ^ 2 +
        2 * (∫ t in a..a + h, |deriv (deriv u) t|) ^ 2 := by
    intro x hx
    have hb := interval_abs_deriv_le hu hh hx
    have h0 := abs_nonneg (deriv u x)
    nlinarith [mul_le_mul hb hb h0 (h0.trans hb), sq_abs (deriv u x),
      sq_nonneg ((9 / h ^ 2 * ∫ t in a..a + h, |u t|) -
        ∫ t in a..a + h, |deriv (deriv u) t|)]
  have hint := intervalIntegral.integral_mono_on (μ := volume) (by linarith : a ≤ a + h)
    ((show Continuous fun x => deriv u x ^ 2 by fun_prop).intervalIntegrable a (a + h))
    intervalIntegrable_const hpt
  have eh : a + h - a = h := by ring
  rw [intervalIntegral.integral_const, smul_eq_mul, eh] at hint
  have cs1 := sq_integral_abs_le_mul_integral_sq hcu (by linarith : a ≤ a + h)
  have cs2 := sq_integral_abs_le_mul_integral_sq hcdd (by linarith : a ≤ a + h)
  rw [eh] at cs1 cs2
  have hne : h ≠ 0 := hh.ne'
  have r1 : h * (2 * (9 / h ^ 2 * ∫ t in a..a + h, |u t|) ^ 2) =
      162 / h ^ 3 * (∫ t in a..a + h, |u t|) ^ 2 := by
    field_simp
    ring
  have r2 : 162 / h ^ 3 * (h * ∫ x in a..a + h, u x ^ 2) =
      162 / h ^ 2 * ∫ x in a..a + h, u x ^ 2 := by
    field_simp
  have b1 : 162 / h ^ 3 * (∫ t in a..a + h, |u t|) ^ 2 ≤
      162 / h ^ 3 * (h * ∫ x in a..a + h, u x ^ 2) :=
    mul_le_mul_of_nonneg_left cs1 (by positivity)
  have b2 : h * (2 * (∫ t in a..a + h, |deriv (deriv u) t|) ^ 2) ≤
      2 * h ^ 2 * ∫ x in a..a + h, deriv (deriv u) x ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left cs2 (by linarith : (0 : ℝ) ≤ 2 * h)]
  nlinarith [r1, r2, b1, b2]

/-- Item 3: the subdivided (`ε`-)form of the interpolation inequality on `[0, 1]`. -/
theorem unit_integral_deriv_sq_le {u : ℝ → ℝ} (hu : ContDiff ℝ 2 u) (N : ℕ) (hN : 1 ≤ N) :
    ∫ x in (0 : ℝ)..1, deriv u x ^ 2 ≤
      162 * (N : ℝ) ^ 2 * (∫ x in (0 : ℝ)..1, u x ^ 2) +
        2 / (N : ℝ) ^ 2 * ∫ x in (0 : ℝ)..1, deriv (deriv u) x ^ 2 := by
  obtain ⟨hcu, _hdu, hcd, _hdd, hcdd⟩ := contDiff_two_interval_facts hu
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.2 (by omega)
  have hN0 : (N : ℝ) ≠ 0 := hNpos.ne'
  have hloc : ∀ k : ℕ, ∫ x in (k : ℝ) / N..((k + 1 : ℕ) : ℝ) / N, deriv u x ^ 2 ≤
      162 * (N : ℝ) ^ 2 * (∫ x in (k : ℝ) / N..((k + 1 : ℕ) : ℝ) / N, u x ^ 2) +
        2 / (N : ℝ) ^ 2 *
          ∫ x in (k : ℝ) / N..((k + 1 : ℕ) : ℝ) / N, deriv (deriv u) x ^ 2 := by
    intro k
    have e : ((k + 1 : ℕ) : ℝ) / N = (k : ℝ) / N + 1 / N := by push_cast; ring
    rw [e]
    have hloc := interval_integral_deriv_sq_le hu (a := (k : ℝ) / N)
      (h := 1 / (N : ℝ)) (by positivity)
    have e1 : (162 : ℝ) / (1 / (N : ℝ)) ^ 2 = 162 * (N : ℝ) ^ 2 := by field_simp
    have e2 : (2 : ℝ) * (1 / (N : ℝ)) ^ 2 = 2 / (N : ℝ) ^ 2 := by field_simp
    rw [e1, e2] at hloc
    exact hloc
  have hsum : ∑ k ∈ Finset.range N,
      ∫ x in (k : ℝ) / N..((k + 1 : ℕ) : ℝ) / N, deriv u x ^ 2 ≤
      ∑ k ∈ Finset.range N,
        (162 * (N : ℝ) ^ 2 * (∫ x in (k : ℝ) / N..((k + 1 : ℕ) : ℝ) / N, u x ^ 2) +
          2 / (N : ℝ) ^ 2 *
            ∫ x in (k : ℝ) / N..((k + 1 : ℕ) : ℝ) / N, deriv (deriv u) x ^ 2) :=
    Finset.sum_le_sum fun k _ => hloc k
  have hadj : ∀ g : ℝ → ℝ, Continuous g →
      ∑ k ∈ Finset.range N, ∫ x in (k : ℝ) / N..((k + 1 : ℕ) : ℝ) / N, g x =
        ∫ x in (0 : ℝ)..1, g x := by
    intro g hg
    have := intervalIntegral.sum_integral_adjacent_intervals
      (a := fun k : ℕ => (k : ℝ) / N) (n := N) (f := g) (μ := volume)
      (fun k _ => hg.intervalIntegrable _ _)
    simp only [Nat.cast_zero, zero_div, div_self hN0] at this
    exact this
  have E1 : ∑ k ∈ Finset.range N,
      ∫ x in (k : ℝ) / N..((k + 1 : ℕ) : ℝ) / N, deriv u x ^ 2 =
        ∫ x in (0 : ℝ)..1, deriv u x ^ 2 := hadj (fun x => deriv u x ^ 2) (hcd.pow 2)
  have E2 : ∑ k ∈ Finset.range N,
      ∫ x in (k : ℝ) / N..((k + 1 : ℕ) : ℝ) / N, u x ^ 2 =
        ∫ x in (0 : ℝ)..1, u x ^ 2 := hadj (fun x => u x ^ 2) (hcu.pow 2)
  have E3 : ∑ k ∈ Finset.range N,
      ∫ x in (k : ℝ) / N..((k + 1 : ℕ) : ℝ) / N, deriv (deriv u) x ^ 2 =
        ∫ x in (0 : ℝ)..1, deriv (deriv u) x ^ 2 :=
    hadj (fun x => deriv (deriv u) x ^ 2) (hcdd.pow 2)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, E1, E2, E3] at hsum
  exact hsum

/-- Pointwise algebra behind the first-normal estimate. -/
theorem first_normal_pointwise {K j a b c d f p q w : ℝ} (hK : 1 ≤ K) (ha : 1 / K ≤ |a|)
    (hb : |b| ≤ K) (hc : |c| ≤ K) (hd : |d| ≤ K)
    (he : a * q + b * p + (j ^ 2 * c + d) * w = f) :
    q ^ 2 ≤ 3 * K ^ 2 * f ^ 2 + 3 * K ^ 4 * p ^ 2 + 3 * K ^ 4 * (1 + j ^ 2) ^ 2 * w ^ 2 := by
  have hKpos : 0 < K := by linarith
  have hE : |j ^ 2 * c + d| ≤ K * (1 + j ^ 2) := by
    have h1 : |j ^ 2 * c + d| ≤ |j ^ 2 * c| + |d| := abs_add_le _ _
    have h2 : |j ^ 2 * c| = j ^ 2 * |c| := by rw [abs_mul, abs_of_nonneg (sq_nonneg j)]
    have h3 : j ^ 2 * |c| ≤ j ^ 2 * K := mul_le_mul_of_nonneg_left hc (sq_nonneg j)
    nlinarith
  have hq : |a * q| ≤ |f| + K * |p| + K * (1 + j ^ 2) * |w| := by
    have hrw : a * q = f - b * p - (j ^ 2 * c + d) * w := by linarith
    rw [hrw]
    have t1 : |b * p| ≤ K * |p| := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_right hb (abs_nonneg _)
    have t2 : |(j ^ 2 * c + d) * w| ≤ K * (1 + j ^ 2) * |w| := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_right hE (abs_nonneg _)
    have t3 : |f - b * p - (j ^ 2 * c + d) * w| ≤
        |f| + |b * p| + |(j ^ 2 * c + d) * w| := by
      rw [abs_le]
      constructor <;> linarith [le_abs_self f, neg_abs_le f, le_abs_self (b * p),
        neg_abs_le (b * p), le_abs_self ((j ^ 2 * c + d) * w),
        neg_abs_le ((j ^ 2 * c + d) * w)]
    linarith
  have hq2 : |q| ≤ K * (|f| + K * |p| + K * (1 + j ^ 2) * |w|) := by
    have h1 : 1 / K * |q| ≤ |a| * |q| := mul_le_mul_of_nonneg_right ha (abs_nonneg q)
    have h2 : |q| = K * (1 / K * |q|) := by field_simp
    calc |q| = K * (1 / K * |q|) := h2
      _ ≤ K * (|a| * |q|) := mul_le_mul_of_nonneg_left h1 hKpos.le
      _ = K * |a * q| := by rw [abs_mul]
      _ ≤ K * (|f| + K * |p| + K * (1 + j ^ 2) * |w|) :=
          mul_le_mul_of_nonneg_left hq hKpos.le
  have hsq : q ^ 2 ≤ (K * (|f| + K * |p| + K * (1 + j ^ 2) * |w|)) ^ 2 := by
    rw [← sq_abs q]
    exact pow_le_pow_left₀ (abs_nonneg q) hq2 2
  have h3 : (|f| + K * |p| + K * (1 + j ^ 2) * |w|) ^ 2 ≤
      3 * (|f| ^ 2 + (K * |p|) ^ 2 + (K * (1 + j ^ 2) * |w|) ^ 2) := by
    nlinarith [sq_nonneg (|f| - K * |p|), sq_nonneg (K * |p| - K * (1 + j ^ 2) * |w|),
      sq_nonneg (|f| - K * (1 + j ^ 2) * |w|)]
  calc q ^ 2 ≤ (K * (|f| + K * |p| + K * (1 + j ^ 2) * |w|)) ^ 2 := hsq
    _ = K ^ 2 * (|f| + K * |p| + K * (1 + j ^ 2) * |w|) ^ 2 := mul_pow _ _ _
    _ ≤ K ^ 2 * (3 * (|f| ^ 2 + (K * |p|) ^ 2 + (K * (1 + j ^ 2) * |w|) ^ 2)) :=
        mul_le_mul_of_nonneg_left h3 (sq_nonneg K)
    _ = 3 * K ^ 2 * f ^ 2 + 3 * K ^ 4 * p ^ 2 + 3 * K ^ 4 * (1 + j ^ 2) ^ 2 * w ^ 2 := by
        simp only [mul_pow, sq_abs]
        ring

/-- Absorption arithmetic for the first-normal estimate. -/
theorem first_normal_absorb {K s M U0 U1 U2 Φ : ℝ} (hK : 1 ≤ K) (hs : 1 ≤ s)
    (hM1 : 16 * K ^ 4 * s ≤ M) (hM2 : M ≤ 25 * K ^ 4 * s) (hU0 : 0 ≤ U0) (hU1 : 0 ≤ U1)
    (hΦ : 0 ≤ Φ) (h3 : U1 ≤ 162 * M * U0 + 2 / M * U2)
    (h2 : U2 ≤ 3 * K ^ 2 * Φ + 3 * K ^ 4 * U1 + 3 * K ^ 4 * s ^ 2 * U0) :
    U1 ≤ 10000 * K ^ 4 * (Φ + s * U0) := by
  have hK4 : 1 ≤ K ^ 4 := one_le_pow₀ hK
  have hK4n : 0 ≤ K ^ 4 := by positivity
  have hK2le : K ^ 2 ≤ K ^ 4 := pow_le_pow_right₀ hK (by norm_num)
  have hs0 : 0 ≤ s := by linarith
  have hKs : 1 ≤ K ^ 4 * s := by nlinarith [mul_le_mul hK4 hs zero_le_one hK4n]
  have hM1' : 1 ≤ M := by linarith
  have hMpos : 0 < M := by linarith
  have hsM : s ≤ M := by nlinarith [mul_nonneg (sub_nonneg.2 hK4) hs0]
  have h16 : 16 * K ^ 4 ≤ M := by nlinarith [mul_nonneg hK4n (sub_nonneg.2 hs)]
  have main : M * U1 ≤ 162 * M ^ 2 * U0 + 2 * U2 := by
    have := mul_le_mul_of_nonneg_left h3 hMpos.le
    have e : M * (162 * M * U0 + 2 / M * U2) = 162 * M ^ 2 * U0 + 2 * U2 := by
      field_simp
    linarith
  have p1 : 162 * M * U0 * M ≤ 162 * M * U0 * (25 * K ^ 4 * s) :=
    mul_le_mul_of_nonneg_left hM2 (mul_nonneg (mul_nonneg (by norm_num) hMpos.le) hU0)
  have p2 : K ^ 2 * Φ ≤ M * K ^ 4 * Φ := by
    have : K ^ 4 ≤ M * K ^ 4 := le_mul_of_one_le_left hK4n hM1'
    exact mul_le_mul_of_nonneg_right (hK2le.trans this) hΦ
  have p3 : K ^ 4 * s * U0 * s ≤ K ^ 4 * s * U0 * M :=
    mul_le_mul_of_nonneg_left hsM (mul_nonneg (mul_nonneg hK4n hs0) hU0)
  have p4 : 16 * K ^ 4 * U1 ≤ M * U1 := mul_le_mul_of_nonneg_right h16 hU1
  have n1 : 0 ≤ M * K ^ 4 * Φ := mul_nonneg (mul_nonneg hMpos.le hK4n) hΦ
  have n2 : 0 ≤ M * K ^ 4 * s * U0 :=
    mul_nonneg (mul_nonneg (mul_nonneg hMpos.le hK4n) hs0) hU0
  have key : 5 / 8 * M * U1 ≤ 5 / 8 * M * (10000 * K ^ 4 * (Φ + s * U0)) := by
    nlinarith
  have hpos : 0 < 5 / 8 * M := by linarith
  exact le_of_mul_le_mul_left key hpos

/-- Substitution arithmetic for the second-derivative estimate. -/
theorem second_normal_substitute {K s U0 U1 U2 Φ : ℝ} (hK : 1 ≤ K) (hs : 1 ≤ s)
    (hU0 : 0 ≤ U0) (hΦ : 0 ≤ Φ) (h1 : U1 ≤ 10000 * K ^ 4 * (Φ + s * U0))
    (h2 : U2 ≤ 3 * K ^ 2 * Φ + 3 * K ^ 4 * U1 + 3 * K ^ 4 * s ^ 2 * U0) :
    U2 ≤ 40000 * K ^ 8 * (Φ + s ^ 2 * U0) := by
  have hK4n : 0 ≤ K ^ 4 := by positivity
  have hK8n : 0 ≤ K ^ 8 := by positivity
  have hs0 : 0 ≤ s := by linarith
  have q1 : K ^ 4 * U1 ≤ K ^ 4 * (10000 * K ^ 4 * (Φ + s * U0)) :=
    mul_le_mul_of_nonneg_left h1 hK4n
  have q2 : K ^ 2 * Φ ≤ K ^ 8 * Φ :=
    mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hK (by norm_num)) hΦ
  have hss : s ≤ s ^ 2 := by nlinarith
  have q3 : K ^ 8 * U0 * s ≤ K ^ 8 * U0 * s ^ 2 :=
    mul_le_mul_of_nonneg_left hss (mul_nonneg hK8n hU0)
  have q4 : K ^ 4 * (s ^ 2 * U0) ≤ K ^ 8 * (s ^ 2 * U0) :=
    mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hK (by norm_num))
      (mul_nonneg (sq_nonneg s) hU0)
  have n1 : 0 ≤ K ^ 8 * Φ := mul_nonneg hK8n hΦ
  have n2 : 0 ≤ K ^ 8 * (s ^ 2 * U0) := mul_nonneg hK8n (mul_nonneg (sq_nonneg s) hU0)
  nlinarith

/-- The integrated form of the equation: `‖u''‖²` is controlled by `F`, `u'` and `u`. -/
theorem unit_integral_second_deriv_sq_le_of_eq {u A B C D₀ F : ℝ → ℝ}
    (hu : ContDiff ℝ 2 u) (hF : Continuous F) {K j : ℝ} (hK : 1 ≤ K)
    (hcoef : ∀ x ∈ Icc (0 : ℝ) 1, 1 / K ≤ |A x| ∧ |A x| ≤ K ∧ |B x| ≤ K ∧ |C x| ≤ K ∧
      |D₀ x| ≤ K)
    (heq : ∀ x ∈ Icc (0 : ℝ) 1,
      A x * deriv (deriv u) x + B x * deriv u x + (j ^ 2 * C x + D₀ x) * u x = F x) :
    ∫ x in (0 : ℝ)..1, deriv (deriv u) x ^ 2 ≤
      3 * K ^ 2 * (∫ x in (0 : ℝ)..1, F x ^ 2) +
        3 * K ^ 4 * (∫ x in (0 : ℝ)..1, deriv u x ^ 2) +
          3 * K ^ 4 * (1 + j ^ 2) ^ 2 * ∫ x in (0 : ℝ)..1, u x ^ 2 := by
  obtain ⟨hcu, _hdu, hcd, _hdd, hcdd⟩ := contDiff_two_interval_facts hu
  have hpt : ∀ x ∈ Icc (0 : ℝ) 1, deriv (deriv u) x ^ 2 ≤
      3 * K ^ 2 * F x ^ 2 + 3 * K ^ 4 * deriv u x ^ 2 +
        3 * K ^ 4 * (1 + j ^ 2) ^ 2 * u x ^ 2 := by
    intro x hx
    obtain ⟨hA1, -, hB, hC, hD⟩ := hcoef x hx
    exact first_normal_pointwise hK hA1 hB hC hD (heq x hx)
  have I2 : Continuous fun x => 3 * K ^ 2 * F x ^ 2 + 3 * K ^ 4 * deriv u x ^ 2 +
      3 * K ^ 4 * (1 + j ^ 2) ^ 2 * u x ^ 2 := by fun_prop
  have hmono := intervalIntegral.integral_mono_on (μ := volume) zero_le_one
    ((show Continuous fun x => deriv (deriv u) x ^ 2 by fun_prop).intervalIntegrable 0 1)
    (I2.intervalIntegrable 0 1) hpt
  have lin : ∫ x in (0 : ℝ)..1, (3 * K ^ 2 * F x ^ 2 + 3 * K ^ 4 * deriv u x ^ 2 +
      3 * K ^ 4 * (1 + j ^ 2) ^ 2 * u x ^ 2) =
      3 * K ^ 2 * (∫ x in (0 : ℝ)..1, F x ^ 2) +
        3 * K ^ 4 * (∫ x in (0 : ℝ)..1, deriv u x ^ 2) +
          3 * K ^ 4 * (1 + j ^ 2) ^ 2 * ∫ x in (0 : ℝ)..1, u x ^ 2 := by
    rw [intervalIntegral.integral_add, intervalIntegral.integral_add,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
    all_goals exact Continuous.intervalIntegrable (by fun_prop) _ _
  exact hmono.trans lin.le

/-- A subdivision number adapted to the absorption: `16 K⁴ s ≤ N² ≤ 25 K⁴ s`. -/
theorem exists_absorbing_subdivision {K s : ℝ} (hK : 1 ≤ K) (hs : 1 ≤ s) :
    ∃ N : ℕ, 1 ≤ N ∧ 16 * K ^ 4 * s ≤ (N : ℝ) ^ 2 ∧ (N : ℝ) ^ 2 ≤ 25 * K ^ 4 * s := by
  have hσ0 : 0 ≤ Real.sqrt s := Real.sqrt_nonneg s
  have hσ2 : Real.sqrt s ^ 2 = s := Real.sq_sqrt (by linarith)
  have hσ1 : 1 ≤ Real.sqrt s := by nlinarith
  have hK2 : 1 ≤ K ^ 2 := one_le_pow₀ hK
  have hK2n : (0 : ℝ) ≤ K ^ 2 := by positivity
  have hKσ' := mul_le_mul hK2 hσ1 zero_le_one hK2n
  have hKσ : 1 ≤ K ^ 2 * Real.sqrt s := by linarith
  have hx0 : 0 ≤ 4 * K ^ 2 * Real.sqrt s := by linarith
  refine ⟨⌈4 * K ^ 2 * Real.sqrt s⌉₊, ?_, ?_, ?_⟩
  · have h1 : 4 * K ^ 2 * Real.sqrt s ≤ (⌈4 * K ^ 2 * Real.sqrt s⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (1 : ℝ) ≤ (⌈4 * K ^ 2 * Real.sqrt s⌉₊ : ℝ) := by linarith
    exact_mod_cast h2
  · have h1 : 4 * K ^ 2 * Real.sqrt s ≤ (⌈4 * K ^ 2 * Real.sqrt s⌉₊ : ℝ) := Nat.le_ceil _
    have h2 := pow_le_pow_left₀ hx0 h1 2
    calc 16 * K ^ 4 * s = (4 * K ^ 2 * Real.sqrt s) ^ 2 := by rw [mul_pow, hσ2]; ring
      _ ≤ _ := h2
  · have h1 : (⌈4 * K ^ 2 * Real.sqrt s⌉₊ : ℝ) < 4 * K ^ 2 * Real.sqrt s + 1 :=
      Nat.ceil_lt_add_one hx0
    have h3 : (⌈4 * K ^ 2 * Real.sqrt s⌉₊ : ℝ) ≤ 5 * K ^ 2 * Real.sqrt s := by linarith
    have h2 := pow_le_pow_left₀ (Nat.cast_nonneg _) h3 2
    calc (⌈4 * K ^ 2 * Real.sqrt s⌉₊ : ℝ) ^ 2 ≤ (5 * K ^ 2 * Real.sqrt s) ^ 2 := h2
      _ = 25 * K ^ 4 * s := by rw [mul_pow, hσ2]; ring

/-- Item 4, first part: one normal derivative of a solution of
`A u'' + B u' + (j² C + D₀) u = F` on `[0, 1]` is controlled by `F` and
`(1 + j²) ‖u‖²`, without boundary conditions (`eq:rad-eq-rm39`,
`eq:vol-reference-first-normal-bound`, squared form). -/
theorem unit_first_normal_bound {u A B C D₀ F : ℝ → ℝ} (hu : ContDiff ℝ 2 u)
    (hF : Continuous F) {K j : ℝ} (hK : 1 ≤ K)
    (hcoef : ∀ x ∈ Icc (0 : ℝ) 1, 1 / K ≤ |A x| ∧ |A x| ≤ K ∧ |B x| ≤ K ∧ |C x| ≤ K ∧
      |D₀ x| ≤ K)
    (heq : ∀ x ∈ Icc (0 : ℝ) 1,
      A x * deriv (deriv u) x + B x * deriv u x + (j ^ 2 * C x + D₀ x) * u x = F x) :
    ∫ x in (0 : ℝ)..1, deriv u x ^ 2 ≤
      10000 * K ^ 4 * ((∫ x in (0 : ℝ)..1, F x ^ 2) +
        (1 + j ^ 2) * ∫ x in (0 : ℝ)..1, u x ^ 2) := by
  have hs : 1 ≤ 1 + j ^ 2 := by nlinarith [sq_nonneg j]
  obtain ⟨N, hN1, hM1, hM2⟩ := exists_absorbing_subdivision hK hs
  have hU0 : 0 ≤ ∫ x in (0 : ℝ)..1, u x ^ 2 :=
    intervalIntegral.integral_nonneg zero_le_one (fun _ _ => sq_nonneg _)
  have hU1 : 0 ≤ ∫ x in (0 : ℝ)..1, deriv u x ^ 2 :=
    intervalIntegral.integral_nonneg zero_le_one (fun _ _ => sq_nonneg _)
  have hΦ : 0 ≤ ∫ x in (0 : ℝ)..1, F x ^ 2 :=
    intervalIntegral.integral_nonneg zero_le_one (fun _ _ => sq_nonneg _)
  exact first_normal_absorb hK hs hM1 hM2 hU0 hU1 hΦ (unit_integral_deriv_sq_le hu N hN1)
    (unit_integral_second_deriv_sq_le_of_eq hu hF hK hcoef heq)

/-- Item 4, second part: the second normal derivative, by substitution back
into the equation. -/
theorem unit_second_normal_bound {u A B C D₀ F : ℝ → ℝ} (hu : ContDiff ℝ 2 u)
    (hF : Continuous F) {K j : ℝ} (hK : 1 ≤ K)
    (hcoef : ∀ x ∈ Icc (0 : ℝ) 1, 1 / K ≤ |A x| ∧ |A x| ≤ K ∧ |B x| ≤ K ∧ |C x| ≤ K ∧
      |D₀ x| ≤ K)
    (heq : ∀ x ∈ Icc (0 : ℝ) 1,
      A x * deriv (deriv u) x + B x * deriv u x + (j ^ 2 * C x + D₀ x) * u x = F x) :
    ∫ x in (0 : ℝ)..1, deriv (deriv u) x ^ 2 ≤
      40000 * K ^ 8 * ((∫ x in (0 : ℝ)..1, F x ^ 2) +
        (1 + j ^ 2) ^ 2 * ∫ x in (0 : ℝ)..1, u x ^ 2) := by
  have hs : 1 ≤ 1 + j ^ 2 := by nlinarith [sq_nonneg j]
  have hU0 : 0 ≤ ∫ x in (0 : ℝ)..1, u x ^ 2 :=
    intervalIntegral.integral_nonneg zero_le_one (fun _ _ => sq_nonneg _)
  have hΦ : 0 ≤ ∫ x in (0 : ℝ)..1, F x ^ 2 :=
    intervalIntegral.integral_nonneg zero_le_one (fun _ _ => sq_nonneg _)
  exact second_normal_substitute hK hs hU0 hΦ
    (unit_first_normal_bound hu hF hK hcoef heq)
    (unit_integral_second_deriv_sq_le_of_eq hu hF hK hcoef heq)

end ContinuousFlexibility.Analysis
