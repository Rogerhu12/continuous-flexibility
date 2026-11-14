module

public import ContinuousFlexibility.Radial.MorseRadiusODE
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# The positive finite-interval Poisson problem

An arbitrary smooth nonnegative potential on a retained interval has a
unique homogeneous solution with any two endpoint values. The construction
uses the actual initial-value equation; positivity rules out a vanishing
Dirichlet determinant. There is no smallness or interval-length assumption.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory
open scoped ContDiff

theorem innerPositiveODE_energy {a b : ℝ} (hab : a ≤ b)
    {V u : ℝ → ℝ} (hV : Continuous V) (hu : ContDiff ℝ ∞ u)
    (heq : ∀ x ∈ Icc a b, deriv (deriv u) x = V x * u x) :
    (∫ x in a..b, deriv u x ^ 2 + V x * u x ^ 2) =
      u b * deriv u b - u a * deriv u a := by
  have hdu := (contDiff_infty_iff_deriv.mp hu).2
  have hc : Continuous (fun x => deriv u x ^ 2 + V x * u x ^ 2) :=
    (hdu.continuous.pow 2).add (hV.mul (hu.continuous.pow 2))
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun x => u x * deriv u x) _ (hc.intervalIntegrable a b)
  intro x hx
  have hx' : x ∈ Icc a b := by simpa only [uIcc_of_le hab] using hx
  convert ((hu.differentiable (by simp) x).hasDerivAt.mul
    (hdu.differentiable (by simp) x).hasDerivAt) using 1
  rw [heq x hx']
  ring

/-- Zero endpoint values force every derivative to vanish. The endpoint
derivatives are included; this will detect the nonzero Dirichlet determinant. -/
theorem innerPositiveODE_deriv_eq_zero {a b : ℝ} (hab : a < b)
    {V u : ℝ → ℝ} (hV : Continuous V) (hu : ContDiff ℝ ∞ u)
    (hVpos : ∀ x ∈ Icc a b, 0 ≤ V x)
    (heq : ∀ x ∈ Icc a b, deriv (deriv u) x = V x * u x)
    (hua : u a = 0) (hub : u b = 0) :
    ∀ x ∈ Icc a b, deriv u x = 0 := by
  have hE : (∫ x in a..b, deriv u x ^ 2 + V x * u x ^ 2) = 0 := by
    rw [innerPositiveODE_energy hab.le hV hu heq, hua, hub, zero_mul, zero_mul, sub_self]
  have hdu := (contDiff_infty_iff_deriv.mp hu).2
  have hc : Continuous (fun x => deriv u x ^ 2 + V x * u x ^ 2) :=
    (hdu.continuous.pow 2).add (hV.mul (hu.continuous.pow 2))
  intro x hx
  by_contra hne
  have hpos : 0 < deriv u x ^ 2 + V x * u x ^ 2 :=
    add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hne)
      (mul_nonneg (hVpos x hx) (sq_nonneg _))
  have hi := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    hab continuousOn_const hc.continuousOn
    (fun y hy => add_nonneg (sq_nonneg _) (mul_nonneg (hVpos y (Ioc_subset_Icc_self hy))
      (sq_nonneg _))) ⟨x, hx, hpos⟩
  simpa only [intervalIntegral.integral_zero, hE, lt_self_iff_false] using hi

theorem innerPositiveODE_zero {a b : ℝ} (hab : a < b)
    {V u : ℝ → ℝ} (hV : Continuous V) (hu : ContDiff ℝ ∞ u)
    (hVpos : ∀ x ∈ Icc a b, 0 ≤ V x)
    (heq : ∀ x ∈ Icc a b, deriv (deriv u) x = V x * u x)
    (hua : u a = 0) (hub : u b = 0) :
    ∀ x ∈ Icc a b, u x = 0 := by
  have hd := innerPositiveODE_deriv_eq_zero hab hV hu hVpos heq hua hub
  intro x hx
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun y (_ : y ∈ Icc a b) => hu.differentiable (by simp) y)
    (fun y hy => show ‖deriv u y‖ ≤ (0 : ℝ) by rw [hd y hy, norm_zero])
    (convex_Icc a b) (left_mem_Icc.mpr hab.le) hx
  have hn : ‖u x‖ ≤ 0 := by simpa only [hua, sub_zero, zero_mul] using h
  exact norm_eq_zero.mp (le_antisymm hn (norm_nonneg _))

/-- Linear combinations retain the actual second-order equation. -/
theorem innerSecondOrder_combination {a b : ℝ} {V u v : ℝ → ℝ}
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (huEq : ∀ x ∈ Icc a b, deriv (deriv u) x = V x * u x)
    (hvEq : ∀ x ∈ Icc a b, deriv (deriv v) x = V x * v x)
    (c d : ℝ) :
    ∀ x ∈ Icc a b,
      deriv (deriv (fun y => c * u y + d * v y)) x = V x * (c * u x + d * v x) := by
  have hdu := (contDiff_infty_iff_deriv.mp hu).2
  have hdv := (contDiff_infty_iff_deriv.mp hv).2
  have he : deriv (fun y => c * u y + d * v y) =
      (fun y => c * deriv u y + d * deriv v y) := by
    funext y
    exact (((hu.differentiable (by simp) y).hasDerivAt.const_mul c).add
      ((hv.differentiable (by simp) y).hasDerivAt.const_mul d)).deriv
  intro x hx
  have hsecond : deriv (fun y => c * deriv u y + d * deriv v y) x =
      c * deriv (deriv u) x + d * deriv (deriv v) x :=
    (((hdu.differentiable (by simp) x).hasDerivAt.const_mul c).fun_add
      ((hdv.differentiable (by simp) x).hasDerivAt.const_mul d)).deriv
  rw [he, hsecond, huEq x hx, hvEq x hx]
  ring

/-- Actual smooth initial values for the positive-sign equation. -/
theorem exists_innerPositiveODE_initial {a b t : ℝ} (ht : t ∈ Icc a b)
    {V : ℝ → ℝ} (hV : ContDiff ℝ ∞ V) (u₀ v₀ : ℝ) :
    ∃ u : ℝ → ℝ, ContDiff ℝ ∞ u ∧ u t = u₀ ∧ deriv u t = v₀ ∧
      ∀ x ∈ Icc a b, deriv (deriv u) x = V x * u x := by
  obtain ⟨u, hu, h₀, h₁, hEq⟩ := exists_smoothSecondOrder hV.neg ht u₀ v₀
  refine ⟨u, hu, h₀, h₁, ?_⟩
  intro x hx
  simpa only [Pi.neg_apply, neg_neg] using hEq x hx

/-- The zero-left-value, unit-left-derivative solution cannot vanish at
the other endpoint. Positivity proves this at every interval length. -/
theorem innerPositiveODE_dirichlet_determinant_ne_zero {a b : ℝ} (hab : a < b)
    {V u : ℝ → ℝ} (hV : Continuous V) (hu : ContDiff ℝ ∞ u)
    (hVpos : ∀ x ∈ Icc a b, 0 ≤ V x)
    (heq : ∀ x ∈ Icc a b, deriv (deriv u) x = V x * u x)
    (hua : u a = 0) (hdua : deriv u a = 1) : u b ≠ 0 := by
  intro hub
  have h := innerPositiveODE_deriv_eq_zero hab hV hu hVpos heq hua hub a
    (left_mem_Icc.mpr hab.le)
  rw [hdua] at h
  exact one_ne_zero h

/-- The finite positive interval admits the two-point homogeneous problem
with arbitrary boundary data, without treating a flux entry as a small error. -/
theorem exists_innerPositiveODE_boundary {a b : ℝ} (hab : a < b)
    {V : ℝ → ℝ} (hV : ContDiff ℝ ∞ V)
    (hVpos : ∀ x ∈ Icc a b, 0 ≤ V x) (α β : ℝ) :
    ∃ u : ℝ → ℝ, ContDiff ℝ ∞ u ∧ u a = α ∧ u b = β ∧
      ∀ x ∈ Icc a b, deriv (deriv u) x = V x * u x := by
  obtain ⟨f, hf, hfa, _, hfEq⟩ := exists_innerPositiveODE_initial
    (left_mem_Icc.mpr hab.le) hV α 0
  obtain ⟨g, hg, hga, hdga, hgEq⟩ := exists_innerPositiveODE_initial
    (left_mem_Icc.mpr hab.le) hV 0 1
  have hgb := innerPositiveODE_dirichlet_determinant_ne_zero hab hV.continuous hg
    hVpos hgEq hga hdga
  let c : ℝ := (β - f b) / g b
  refine ⟨fun x => 1 * f x + c * g x, (contDiff_const.mul hf).add (contDiff_const.mul hg), ?_, ?_,
    innerSecondOrder_combination hf hg hfEq hgEq 1 c⟩
  · change 1 * f a + c * g a = α
    rw [hfa, hga, mul_zero, add_zero, one_mul]
  · dsimp only [c]
    rw [div_mul_cancel₀ _ hgb, one_mul]
    ring

theorem innerPositiveODE_boundary_unique {a b : ℝ} (hab : a < b)
    {V u v : ℝ → ℝ} (hV : Continuous V)
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (hVpos : ∀ x ∈ Icc a b, 0 ≤ V x)
    (huEq : ∀ x ∈ Icc a b, deriv (deriv u) x = V x * u x)
    (hvEq : ∀ x ∈ Icc a b, deriv (deriv v) x = V x * v x)
    (ha : u a = v a) (hb : u b = v b) : EqOn u v (Icc a b) := by
  have hz := innerPositiveODE_zero hab hV
    ((contDiff_const.mul hu).add (contDiff_const.mul hv)) hVpos
    (innerSecondOrder_combination hu hv huEq hvEq 1 (-1))
    (by rw [ha]; ring) (by rw [hb]; ring)
  intro x hx
  have h := hz x hx
  linarith

end ContinuousFlexibility.Radial
