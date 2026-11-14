module

public import ContinuousFlexibility.Analysis.N06RadialGeometryJets
public import ContinuousFlexibility.Analysis.CircleInverseDerivativeBounds

/-!
# Actual second derivatives of the radial inverse

The first inverse derivative comes from the established scalar inverse
theorem, which obtains inverse continuity from the forward slope lower
bound. Differentiating that actual identity gives the second derivative.
The estimates therefore concern the genuine inverse, rather than a
separately specified derivative field.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-- The true second derivative of a right inverse. No regularity of the
inverse is included among the hypotheses. -/
theorem n06_deriv_two_inverse
    {Y R : ℝ → ℝ} {a : ℝ}
    (hY : ContDiff ℝ ∞ Y) (ha : 0 < a)
    (hlower : ∀ x, a ≤ deriv Y x) (hYR : ∀ y, Y (R y) = y) (y : ℝ) :
    deriv (deriv R) y = -deriv (deriv Y) (R y) / deriv Y (R y) ^ 3 := by
  have hR (t : ℝ) : HasDerivAt R (deriv Y (R t))⁻¹ t :=
    hasDerivAt_inverse_of_deriv_lower_bound ha hlower hYR t
  have hfirst : deriv R = fun t => (deriv Y (R t))⁻¹ :=
    funext fun t => (hR t).deriv
  have hY' : ContDiff ℝ ∞ (deriv Y) := (contDiff_infty_iff_deriv.mp hY).2
  have hJ : deriv Y (R y) ≠ 0 := (ha.trans_le (hlower (R y))).ne'
  have hinner : HasDerivAt (fun t => deriv Y (R t))
      (deriv (deriv Y) (R y) * (deriv Y (R y))⁻¹) y :=
    (hY'.differentiable (by simp) (R y)).hasDerivAt.comp y (hR y)
  have hinverse : HasDerivAt (fun t => (deriv Y (R t))⁻¹)
      (-(deriv (deriv Y) (R y) * (deriv Y (R y))⁻¹) / deriv Y (R y) ^ 2) y :=
    hinner.inv hJ
  rw [hfirst, hinverse.deriv]
  field_simp [hJ]

/-- Primitive forward derivative bounds and the inverse value bound give
an explicit polynomial bound for all three inverse jets. -/
theorem n06_inverse_twoJet_bound
    {Y R : ℝ → ℝ} {y B : ℝ}
    (hY : ContDiff ℝ ∞ Y) (hB : 1 ≤ B)
    (hlower : ∀ x, 1 / B ≤ deriv Y x) (hYR : ∀ t, Y (R t) = t)
    (hvalue : |R y| ≤ B) (hsecond : |deriv (deriv Y) (R y)| ≤ B) :
    N06ScalarJetTwoBound R y (B ^ 4) := by
  have hBp : 0 < B := zero_lt_one.trans_le hB
  have ha : 0 < 1 / B := one_div_pos.mpr hBp
  have hJ : 0 < deriv Y (R y) := ha.trans_le (hlower (R y))
  have hinv : |(deriv Y (R y))⁻¹| ≤ B := by
    rw [abs_of_pos (inv_pos.mpr hJ), inv_eq_one_div]
    have he := one_div_le_one_div_of_le ha (hlower (R y))
    simpa only [one_div_one_div] using he
  have hB4 : B ≤ B ^ 4 := by
    simpa only [pow_one] using pow_le_pow_right₀ hB (by norm_num : 1 ≤ 4)
  refine ⟨hvalue.trans hB4, ?_, ?_⟩
  · rw [(hasDerivAt_inverse_of_deriv_lower_bound ha hlower hYR y).deriv]
    exact hinv.trans hB4
  · rw [n06_deriv_two_inverse hY ha hlower hYR]
    calc
      _ = |deriv (deriv Y) (R y)| * |(deriv Y (R y))⁻¹| ^ 3 := by
        rw [abs_div, abs_neg, abs_pow, div_eq_mul_inv, ← inv_pow, ← abs_inv]
      _ ≤ B * B ^ 3 := mul_le_mul hsecond
        (pow_le_pow_left₀ (abs_nonneg _) hinv 3) (pow_nonneg (abs_nonneg _) _) hBp.le
      _ = _ := by ring

/-- The actual inverse sends the entire closed unit interval into the
closed physical interval, including its endpoint values. -/
theorem n06_inverse_mem_Icc
    {Y R : ℝ → ℝ} {l r a y : ℝ} (ha : 0 < a)
    (hlower : ∀ x, a ≤ deriv Y x) (hYR : ∀ t, Y (R t) = t)
    (hl : Y l = 0) (hr : Y r = 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    R y ∈ Icc l r := by
  have hmono : StrictMono Y := strictMono_of_deriv_pos (fun x => ha.trans_le (hlower x))
  constructor
  · apply hmono.le_iff_le.mp
    simpa only [hl, hYR y] using hy.1
  · apply hmono.le_iff_le.mp
    simpa only [hr, hYR y] using hy.2

/-- A bound for the physical endpoints controls the inverse value on the
unit interval; it does not require a global bound for an inverse map. -/
theorem n06_abs_le_of_mem_Icc {l r x B : ℝ}
    (hl : |l| ≤ B) (hr : |r| ≤ B) (hx : x ∈ Icc l r) : |x| ≤ B := by
  apply abs_le.mpr
  exact ⟨(abs_le.mp hl).1.trans hx.1, hx.2.trans (abs_le.mp hr).2⟩

end ContinuousFlexibility.Analysis
