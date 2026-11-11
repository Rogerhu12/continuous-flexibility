import ContinuousFlexibility.Analysis.SmoothDivisionBounds
import ContinuousFlexibility.Analysis.OneHighCircleFlowLocalization
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# One fixed smooth factor for the doubled-angle sine

The sine has a genuine smooth linear factor. It is positive between its
two nearest nonzero roots. A fixed smooth clamp supplies a global smooth
reciprocal agreeing with the true reciprocal on a larger interval than
the nearest-root window. All derivative bounds are numerical constants,
chosen before any state, coefficient field, or physical radius.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-- A single smooth factor and reciprocal work for every angular zero.
The larger closed interval leaves room for genuine equality of germs
throughout the nearest-zero window `[-π/4,π/4]`. -/
theorem exists_doubledSine_factor_and_inverse :
    ∃ q ψ : ℝ → ℝ, ContDiff ℝ ∞ q ∧ q 0 = 2 ∧
      (∀ x : ℝ, Real.sin (2 * x) = x * q x) ∧
      (∀ x ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2), 0 < q x) ∧
      ContDiff ℝ ∞ ψ ∧
      (∀ x ∈ Icc (-(Real.pi / 3)) (Real.pi / 3), ψ x * q x = 1) ∧
      ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧
        ∀ x ∈ Icc (-(Real.pi / 3)) (Real.pi / 3),
          |iteratedDeriv n ψ x| ≤ C := by
  have hs : ContDiff ℝ ∞ (fun x : ℝ => Real.sin (2 * x)) :=
    Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)
  have hs0 : Real.sin (2 * (0 : ℝ)) = 0 := by rw [mul_zero, Real.sin_zero]
  obtain ⟨q, hq, hq0, hfactor⟩ := exists_smooth_division_at_zero hs hs0
  have hd : HasDerivAt (fun x : ℝ => Real.sin (2 * x)) (2 : ℝ) 0 := by
    simpa only [Function.comp_def, id_eq, mul_zero, Real.cos_zero, one_mul, mul_one] using
      (Real.hasDerivAt_sin (2 * (0 : ℝ))).comp 0 ((hasDerivAt_id 0).const_mul 2)
  have hqzero : q 0 = 2 := hq0.trans hd.deriv
  have hqeven (x : ℝ) : q (-x) = q x := by
    by_cases hx : x = 0
    · subst x
      rw [neg_zero]
    apply mul_left_cancel₀ hx
    have hp := hfactor x
    have hn := hfactor (-x)
    rw [mul_neg, Real.sin_neg] at hn
    linarith only [hp, hn]
  have hqpos (x : ℝ) (hx : 0 < x) (hxp : x < Real.pi / 2) : 0 < q x := by
    have hsin : 0 < Real.sin (2 * x) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    rw [hfactor x] at hsin
    by_contra hn
    have hnonpos : q x ≤ 0 := le_of_not_gt hn
    have hprod := mul_nonpos_of_nonneg_of_nonpos hx.le hnonpos
    linarith
  have hpositive (x : ℝ) (hx : x ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2)) :
      0 < q x := by
    rcases lt_trichotomy x 0 with hneg | hz | hpos
    · rw [← hqeven x]
      exact hqpos (-x) (neg_pos.mpr hneg) (by linarith [hx.1])
    · rw [hz, hqzero]
      norm_num
    · exact hqpos x hpos hx.2
  have hab : -(Real.pi / 3) ≤ Real.pi / 3 := by linarith [Real.pi_pos]
  have heps : 0 < Real.pi / 12 := by positivity
  let C := circleFlowSmoothTimeClamp (-(Real.pi / 3)) (Real.pi / 3)
    (Real.pi / 12) hab heps
  have hC : ContDiff ℝ ∞ C := contDiff_circleFlowSmoothTimeClamp hab heps
  have hCpos (x : ℝ) : 0 < q (C x) := by
    apply hpositive
    have hm := circleFlowSmoothTimeClamp_mem hab heps x
    change -(Real.pi / 3) - Real.pi / 12 < C x ∧
      C x < Real.pi / 3 + Real.pi / 12 at hm
    constructor <;> linarith [Real.pi_pos, hm.1, hm.2]
  let ψ : ℝ → ℝ := fun x => (q (C x))⁻¹
  have hψ : ContDiff ℝ ∞ ψ := (hq.comp hC).inv (fun x => (hCpos x).ne')
  have hinverse (x : ℝ) (hx : x ∈ Icc (-(Real.pi / 3)) (Real.pi / 3)) :
      ψ x * q x = 1 := by
    have he : C x = x := circleFlowSmoothTimeClamp_eq hab heps hx
    have hnonzero : q x ≠ 0 := by
      apply (hpositive x ?_).ne'
      constructor <;> linarith [Real.pi_pos, hx.1, hx.2]
    change (q (C x))⁻¹ * q x = 1
    rw [he, inv_mul_cancel₀ hnonzero]
  refine ⟨q, ψ, hq, hqzero, hfactor, hpositive, hψ, hinverse, ?_⟩
  intro n
  obtain ⟨B, hB⟩ :=
    (isCompact_Icc : IsCompact (Icc (-(Real.pi / 3)) (Real.pi / 3))).exists_bound_of_continuousOn
      (hψ.continuous_iteratedDeriv n (by simp)).continuousOn
  refine ⟨max B 0, le_max_right _ _, ?_⟩
  intro x hx
  have hb : |iteratedDeriv n ψ x| ≤ B := by
    simpa only [Real.norm_eq_abs] using hB x hx
  exact hb.trans (le_max_left _ _)

end ContinuousFlexibility.Analysis
