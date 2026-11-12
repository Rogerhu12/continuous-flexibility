import ContinuousFlexibility.Scalar.WeightedRationalFactors
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Square-root stability at shared simple roots

A derivative bound for an error that vanishes at both endpoints retains
the distance to the nearer endpoint. A reference radicand bounded below
by a positive multiple of `(r-a)*(b-r)` therefore turns this absolute
derivative bound into a relative radicand bound. Rationalization then
gives a square-root error linear in the original error size, including
at both roots.

These are scalar estimates for actual functions on a closed interval.
They do not assume a desired speed estimate or assert an N04b obstruction.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set

/-- A relative radicand error gives the same relative square-root bound.
The reference radicand is allowed to vanish. -/
theorem n04b_sqrt_sub_le_of_relative_error {p d ε : ℝ}
    (hp : 0 ≤ p) (hd : 0 ≤ d) (hε : 0 ≤ ε)
    (herr : |p - d| ≤ ε * d) :
    |Real.sqrt p - Real.sqrt d| ≤ ε * Real.sqrt d := by
  by_cases hd0 : d = 0
  · subst d
    have hp0 : p = 0 := le_antisymm
      (by simpa only [sub_zero, mul_zero, abs_of_nonneg hp] using herr) hp
    simp only [hp0, Real.sqrt_zero, sub_self, abs_zero, mul_zero, le_refl]
  · have hdpos : 0 < d := lt_of_le_of_ne hd (Ne.symm hd0)
    have hs : 0 < Real.sqrt d := Real.sqrt_pos.mpr hdpos
    have hsum : 0 < Real.sqrt p + Real.sqrt d :=
      add_pos_of_nonneg_of_pos (Real.sqrt_nonneg p) hs
    have hratio : |Real.sqrt p / Real.sqrt d - 1| ≤ ε := by
      rw [sqrt_div_sqrt_sub_one_eq_factor hp hdpos, abs_div,
        abs_of_pos (mul_pos hsum hs)]
      apply (div_le_iff₀ (mul_pos hsum hs)).mpr
      calc
        |p - d| ≤ ε * d := herr
        _ = ε * (Real.sqrt d * Real.sqrt d) := by rw [Real.mul_self_sqrt hd]
        _ ≤ ε * ((Real.sqrt p + Real.sqrt d) * Real.sqrt d) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right
              (by linarith [Real.sqrt_nonneg p]) hs.le) hε
    have he : Real.sqrt p - Real.sqrt d =
        (Real.sqrt p / Real.sqrt d - 1) * Real.sqrt d := by
      rw [sub_mul, div_mul_cancel₀ _ hs.ne', one_mul]
    rw [he, abs_mul, abs_of_pos hs]
    exact mul_le_mul_of_nonneg_right hratio hs.le

/-- One mean-value estimate handles a zero at either endpoint, or at any
other point of the interval. -/
theorem n04b_abs_le_distance_of_zero_deriv_bound
    {e : ℝ → ℝ} {a b x y ε : ℝ}
    (he : ∀ r ∈ Icc a b, DifferentiableAt ℝ e r)
    (hderiv : ∀ r ∈ Icc a b, |deriv e r| ≤ ε)
    (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) (hzero : e x = 0) :
    |e y| ≤ ε * |y - x| := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le he
    (fun r hr => by simpa only [Real.norm_eq_abs] using hderiv r hr)
    (convex_Icc a b) hx hy
  simpa only [hzero, sub_zero, Real.norm_eq_abs] using h

/-- A shared zero at each endpoint gives the smaller of the two endpoint
distance bounds, with the original derivative-error constant. -/
theorem n04b_error_le_min_distance {e : ℝ → ℝ} {a b ε : ℝ}
    (hab : a ≤ b)
    (he : ∀ r ∈ Icc a b, DifferentiableAt ℝ e r)
    (hderiv : ∀ r ∈ Icc a b, |deriv e r| ≤ ε)
    (ha : e a = 0) (hb : e b = 0) {r : ℝ} (hr : r ∈ Icc a b) :
    |e r| ≤ ε * min (r - a) (b - r) := by
  have hleft : |e r| ≤ ε * (r - a) := by
    simpa only [abs_of_nonneg (sub_nonneg.mpr hr.1)] using
      n04b_abs_le_distance_of_zero_deriv_bound he hderiv
        (show a ∈ Icc a b from ⟨le_rfl, hab⟩) hr ha
  have hright : |e r| ≤ ε * (b - r) := by
    simpa only [abs_of_nonpos (sub_nonpos.mpr hr.2), neg_sub] using
      n04b_abs_le_distance_of_zero_deriv_bound he hderiv
        (show b ∈ Icc a b from ⟨hab, le_rfl⟩) hr hb
  rcases le_total (r - a) (b - r) with h | h
  · rw [min_eq_left h]
    exact hleft
  · rw [min_eq_right h]
    exact hright

private theorem n04b_length_mul_min_distance_le {a b r : ℝ}
    (hr : r ∈ Icc a b) :
    (b - a) * min (r - a) (b - r) ≤ 2 * (r - a) * (b - r) := by
  rcases le_total (r - a) (b - r) with h | h
  · rw [min_eq_left h]
    have hm := mul_le_mul_of_nonneg_left h (sub_nonneg.mpr hr.1)
    nlinarith
  · rw [min_eq_right h]
    have hm := mul_le_mul_of_nonneg_left h (sub_nonneg.mpr hr.2)
    nlinarith

/-- The derivative error and common endpoint values give a square-root
error of order `ε*sqrt(d)`, uniformly up to both roots. Shared zero values
are a special case of the endpoint equalities. -/
theorem n04b_sqrt_sub_le_of_shared_endpoint_deriv
    {p d : ℝ → ℝ} {a b c ε : ℝ}
    (hab : a < b) (hc : 0 < c) (hε : 0 ≤ ε)
    (he : ∀ r ∈ Icc a b, DifferentiableAt ℝ (fun t => p t - d t) r)
    (hderiv : ∀ r ∈ Icc a b, |deriv (fun t => p t - d t) r| ≤ ε)
    (ha : p a = d a) (hb : p b = d b)
    (hp : ∀ r ∈ Icc a b, 0 ≤ p r)
    (hd : ∀ r ∈ Icc a b, c * (r - a) * (b - r) ≤ d r)
    {r : ℝ} (hr : r ∈ Icc a b) :
    |Real.sqrt (p r) - Real.sqrt (d r)| ≤
      (2 * ε / (c * (b - a))) * Real.sqrt (d r) := by
  have hden : 0 < c * (b - a) := mul_pos hc (sub_pos.mpr hab)
  have hbound : |p r - d r| ≤ ε * min (r - a) (b - r) :=
    n04b_error_le_min_distance hab.le he hderiv
      (sub_eq_zero.mpr ha) (sub_eq_zero.mpr hb) hr
  have hscale : (c * (b - a)) * |p r - d r| ≤ 2 * ε * d r := by
    calc
      _ ≤ (c * (b - a)) * (ε * min (r - a) (b - r)) :=
        mul_le_mul_of_nonneg_left hbound hden.le
      _ = c * ε * ((b - a) * min (r - a) (b - r)) := by ring
      _ ≤ c * ε * (2 * (r - a) * (b - r)) :=
        mul_le_mul_of_nonneg_left (n04b_length_mul_min_distance_le hr)
          (mul_nonneg hc.le hε)
      _ = 2 * ε * (c * (r - a) * (b - r)) := by ring
      _ ≤ 2 * ε * d r := mul_le_mul_of_nonneg_left (hd r hr) (by positivity)
  have hrelative : |p r - d r| ≤ (2 * ε / (c * (b - a))) * d r := by
    calc
      _ ≤ (2 * ε * d r) / (c * (b - a)) :=
        (le_div_iff₀ hden).mpr (by simpa only [mul_comm] using hscale)
      _ = _ := by ring
  have hdnonneg : 0 ≤ d r :=
    (mul_nonneg (mul_nonneg hc.le (sub_nonneg.mpr hr.1))
      (sub_nonneg.mpr hr.2)).trans (hd r hr)
  exact n04b_sqrt_sub_le_of_relative_error (hp r hr) hdnonneg
    (div_nonneg (mul_nonneg (by norm_num) hε) hden.le) hrelative

/-- A fixed upper bound for the reference radicand converts the root
estimate into a uniform scalar speed bound linear in the derivative error. -/
theorem n04b_uniform_sqrt_sub_le_of_shared_endpoint_deriv
    {p d : ℝ → ℝ} {a b c ε M : ℝ}
    (hab : a < b) (hc : 0 < c) (hε : 0 ≤ ε)
    (he : ∀ r ∈ Icc a b, DifferentiableAt ℝ (fun t => p t - d t) r)
    (hderiv : ∀ r ∈ Icc a b, |deriv (fun t => p t - d t) r| ≤ ε)
    (ha : p a = d a) (hb : p b = d b)
    (hp : ∀ r ∈ Icc a b, 0 ≤ p r)
    (hd : ∀ r ∈ Icc a b, c * (r - a) * (b - r) ≤ d r)
    (hupper : ∀ r ∈ Icc a b, d r ≤ M) {r : ℝ} (hr : r ∈ Icc a b) :
    |Real.sqrt (p r) - Real.sqrt (d r)| ≤
      (2 * ε / (c * (b - a))) * Real.sqrt M := by
  apply (n04b_sqrt_sub_le_of_shared_endpoint_deriv
    hab hc hε he hderiv ha hb hp hd hr).trans
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hupper r hr))
    (div_nonneg (mul_nonneg (by norm_num) hε)
      (mul_nonneg hc.le (sub_nonneg.mpr hab.le)))

end ContinuousFlexibility.Analysis
