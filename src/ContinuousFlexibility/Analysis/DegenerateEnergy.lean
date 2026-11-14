module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# The degenerate weighted energy estimate on `[0, 1]`

This file formalizes the calculation of
`paper/flexible-surface-rewrite/08-stable-inverse.tex`, "The estimate that
explains cubic matching" (`eq:vol-arbitrary-boundary-graph-bound`), for the
real-valued model `P u = -(a u')' + j² c u + V u = F` on `[0, 1]` with
`d(y) = y (1 - y)` and arbitrary boundary values of `u`.

* `degenerate_energy_identity`: testing against `d² u` (no boundary terms,
  because `d` vanishes at both ends).
* `degenerate_energy_bound`, `degenerate_gradient_bound`: the resulting
  weighted bounds for `(d u)'`, `j d^{3/2} u` and `d u'`.
* `dirichlet_square_identity`: the second-stage squaring identity for a
  zero-trace function `v`.
* `conjugated_degenerate_equation`: the equation satisfied by `v = d² u`.

The forcing term `F` is a variable together with its defining pointwise
equation, so no definition is unfolded in the statements.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set intervalIntegral

/-- The weight `d(y) = y (1 - y)` vanishing at both endpoints of `[0, 1]`. -/
def cylinderWeight (y : ℝ) : ℝ := y * (1 - y)

theorem cylinderWeight_continuous : Continuous cylinderWeight := by
  show Continuous fun y : ℝ => y * (1 - y)
  fun_prop

@[simp] theorem cylinderWeight_zero : cylinderWeight 0 = 0 := by simp [cylinderWeight]

@[simp] theorem cylinderWeight_one : cylinderWeight 1 = 0 := by simp [cylinderWeight]

theorem cylinderWeight_nonneg {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) : 0 ≤ cylinderWeight y :=
  mul_nonneg hy.1 (sub_nonneg.2 hy.2)

theorem cylinderWeight_le_one {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) : cylinderWeight y ≤ 1 := by
  have h := hy.2
  unfold cylinderWeight
  nlinarith [sq_nonneg y]

theorem one_sub_two_mul_sq_le_one {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) : (1 - 2 * y) ^ 2 ≤ 1 := by
  nlinarith [mul_nonneg hy.1 (sub_nonneg.2 hy.2)]

theorem cylinderWeight_hasDerivAt (y : ℝ) : HasDerivAt cylinderWeight (1 - 2 * y) y := by
  have h := (hasDerivAt_id' y).fun_mul ((hasDerivAt_id' y).const_sub 1)
  exact h.congr_deriv (by ring)

theorem cylinderWeight_sq_hasDerivAt (y : ℝ) :
    HasDerivAt (fun t => cylinderWeight t ^ 2) (2 * cylinderWeight y * (1 - 2 * y)) y := by
  have h := (cylinderWeight_hasDerivAt y).fun_pow 2
  exact h.congr_deriv (by norm_num)

theorem contDiff_deriv_of_two {u : ℝ → ℝ} (hu : ContDiff ℝ 2 u) : ContDiff ℝ 1 (deriv u) := by
  have h2 : ContDiff ℝ (1 + 1) u := by rw [one_add_one_eq_two]; exact hu
  exact (contDiff_succ_iff_deriv.mp h2).2.2

theorem hasDerivAt_of_contDiff_two {u : ℝ → ℝ} (hu : ContDiff ℝ 2 u) (y : ℝ) :
    HasDerivAt u (deriv u y) y :=
  (hu.differentiable (by norm_num) y).hasDerivAt

theorem hasDerivAt_deriv_of_contDiff_two {u : ℝ → ℝ} (hu : ContDiff ℝ 2 u) (y : ℝ) :
    HasDerivAt (deriv u) (deriv (deriv u) y) y :=
  ((contDiff_deriv_of_two hu).differentiable (by norm_num) y).hasDerivAt

theorem hasDerivAt_of_contDiff_one {a : ℝ → ℝ} (ha : ContDiff ℝ 1 a) (y : ℝ) :
    HasDerivAt a (deriv a y) y :=
  (ha.differentiable (by norm_num) y).hasDerivAt

theorem hasDerivAt_mul_deriv {a u : ℝ → ℝ} (ha : ContDiff ℝ 1 a) (hu : ContDiff ℝ 2 u)
    (y : ℝ) :
    HasDerivAt (fun t => a t * deriv u t) (deriv (fun t => a t * deriv u t) y) y :=
  ((hasDerivAt_of_contDiff_one ha y).fun_mul
    (hasDerivAt_deriv_of_contDiff_two hu y)).differentiableAt.hasDerivAt

theorem continuous_deriv_mul_deriv {a u : ℝ → ℝ} (ha : ContDiff ℝ 1 a)
    (hu : ContDiff ℝ 2 u) : Continuous (deriv (fun t => a t * deriv u t)) :=
  (ContDiff.mul ha (contDiff_deriv_of_two hu)).continuous_deriv le_rfl

theorem hasDerivAt_cw_mul {u : ℝ → ℝ} (hu : ContDiff ℝ 2 u) (y : ℝ) :
    HasDerivAt (fun t => cylinderWeight t * u t)
      ((1 - 2 * y) * u y + cylinderWeight y * deriv u y) y :=
  (cylinderWeight_hasDerivAt y).fun_mul (hasDerivAt_of_contDiff_two hu y)

theorem hasDerivAt_cw_sq_mul {u : ℝ → ℝ} (hu : ContDiff ℝ 2 u) (y : ℝ) :
    HasDerivAt (fun t => cylinderWeight t ^ 2 * u t)
      (2 * cylinderWeight y * (1 - 2 * y) * u y + cylinderWeight y ^ 2 * deriv u y) y :=
  (cylinderWeight_sq_hasDerivAt y).fun_mul (hasDerivAt_of_contDiff_two hu y)

theorem continuous_deriv_cw_mul {u : ℝ → ℝ} (hu : ContDiff ℝ 2 u) :
    Continuous (deriv fun t => cylinderWeight t * u t) := by
  have hD : (deriv fun t => cylinderWeight t * u t)
      = fun y => (1 - 2 * y) * u y + cylinderWeight y * deriv u y :=
    funext fun y => (hasDerivAt_cw_mul hu y).deriv
  have hd := cylinderWeight_continuous
  have hu0 := hu.continuous
  have hu1 : Continuous (deriv u) := (contDiff_deriv_of_two hu).continuous
  rw [hD]
  fun_prop

theorem continuous_forcing {a u c V F : ℝ → ℝ} {j : ℝ} (ha : ContDiff ℝ 1 a)
    (hu : ContDiff ℝ 2 u) (hc : Continuous c) (hV : Continuous V)
    (hF : ∀ y, F y = -(deriv (fun t => a t * deriv u t) y) + j ^ 2 * c y * u y + V y * u y) :
    Continuous F := by
  have hG' := continuous_deriv_mul_deriv ha hu
  have hu0 := hu.continuous
  have hFe : F = fun y => -(deriv (fun t => a t * deriv u t) y) + j ^ 2 * c y * u y
      + V y * u y := funext hF
  rw [hFe]
  fun_prop

theorem integral_eq_zero_of_hasDerivAt {g g' : ℝ → ℝ} (h : ∀ y, HasDerivAt g (g' y) y)
    (hc : Continuous g') (h0 : g 0 = 0) (h1 : g 1 = 0) :
    ∫ y in (0 : ℝ)..1, g' y = 0 := by
  rw [integral_eq_sub_of_hasDerivAt (fun y _ => h y) (hc.intervalIntegrable 0 1)]
  simp [h0, h1]

theorem integral_lin3 {f₁ f₂ f₃ : ℝ → ℝ} (h₁ : Continuous f₁) (h₂ : Continuous f₂)
    (h₃ : Continuous f₃) :
    ∫ y in (0 : ℝ)..1, (f₁ y + f₂ y - f₃ y)
      = (∫ y in (0 : ℝ)..1, f₁ y) + (∫ y in (0 : ℝ)..1, f₂ y) - ∫ y in (0 : ℝ)..1, f₃ y := by
  rw [intervalIntegral.integral_sub, intervalIntegral.integral_add]
  all_goals exact Continuous.intervalIntegrable (by fun_prop) _ _

theorem integral_lin2 (c₁ c₂ : ℝ) {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    ∫ y in (0 : ℝ)..1, (c₁ * f y + c₂ * g y)
      = c₁ * (∫ y in (0 : ℝ)..1, f y) + c₂ * ∫ y in (0 : ℝ)..1, g y := by
  rw [intervalIntegral.integral_add, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  all_goals exact Continuous.intervalIntegrable (by fun_prop) _ _

theorem integral_lin5a (c : ℝ) {f₁ f₂ f₃ f₄ f₅ g : ℝ → ℝ}
    (h₁ : Continuous f₁) (h₂ : Continuous f₂) (h₃ : Continuous f₃) (h₄ : Continuous f₄)
    (h₅ : Continuous f₅)
    (hg : ∀ y, f₁ y + c * f₂ y - f₃ y - f₄ y + f₅ y = g y)
    (h0 : ∫ y in (0 : ℝ)..1, g y = 0) :
    (∫ y in (0 : ℝ)..1, f₁ y) + c * (∫ y in (0 : ℝ)..1, f₂ y) - (∫ y in (0 : ℝ)..1, f₃ y)
      - (∫ y in (0 : ℝ)..1, f₄ y) + ∫ y in (0 : ℝ)..1, f₅ y = 0 := by
  have hz : ∫ y in (0 : ℝ)..1, (f₁ y + c * f₂ y - f₃ y - f₄ y + f₅ y) = 0 := by
    exact (intervalIntegral.integral_congr (fun y _ => hg y)).trans h0
  have hexp : ∫ y in (0 : ℝ)..1, (f₁ y + c * f₂ y - f₃ y - f₄ y + f₅ y)
      = (∫ y in (0 : ℝ)..1, f₁ y) + c * (∫ y in (0 : ℝ)..1, f₂ y) - (∫ y in (0 : ℝ)..1, f₃ y)
        - (∫ y in (0 : ℝ)..1, f₄ y) + ∫ y in (0 : ℝ)..1, f₅ y := by
    rw [intervalIntegral.integral_add, intervalIntegral.integral_sub,
      intervalIntegral.integral_sub, intervalIntegral.integral_add,
      intervalIntegral.integral_const_mul]
    all_goals exact Continuous.intervalIntegrable (by fun_prop) _ _
  linarith

theorem integral_lin5b (c₁ c₂ c₃ : ℝ) {f₁ f₂ f₃ f₄ f₅ g : ℝ → ℝ}
    (h₁ : Continuous f₁) (h₂ : Continuous f₂) (h₃ : Continuous f₃) (h₄ : Continuous f₄)
    (h₅ : Continuous f₅)
    (hg : ∀ y, f₁ y + c₁ * f₂ y + c₂ * f₃ y - f₄ y - c₃ * f₅ y = g y)
    (h0 : ∫ y in (0 : ℝ)..1, g y = 0) :
    (∫ y in (0 : ℝ)..1, f₁ y) + c₁ * (∫ y in (0 : ℝ)..1, f₂ y)
      + c₂ * (∫ y in (0 : ℝ)..1, f₃ y) - (∫ y in (0 : ℝ)..1, f₄ y)
      - c₃ * ∫ y in (0 : ℝ)..1, f₅ y = 0 := by
  have hz : ∫ y in (0 : ℝ)..1, (f₁ y + c₁ * f₂ y + c₂ * f₃ y - f₄ y - c₃ * f₅ y) = 0 := by
    exact (intervalIntegral.integral_congr (fun y _ => hg y)).trans h0
  have hexp : ∫ y in (0 : ℝ)..1, (f₁ y + c₁ * f₂ y + c₂ * f₃ y - f₄ y - c₃ * f₅ y)
      = (∫ y in (0 : ℝ)..1, f₁ y) + c₁ * (∫ y in (0 : ℝ)..1, f₂ y)
        + c₂ * (∫ y in (0 : ℝ)..1, f₃ y) - (∫ y in (0 : ℝ)..1, f₄ y)
        - c₃ * ∫ y in (0 : ℝ)..1, f₅ y := by
    rw [intervalIntegral.integral_sub, intervalIntegral.integral_sub,
      intervalIntegral.integral_add, intervalIntegral.integral_add,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
    all_goals exact Continuous.intervalIntegrable (by fun_prop) _ _
  linarith

/-- Item 1: the weighted energy identity obtained by testing against `d² u`.
Manuscript: the displayed identity after "Multiply by `d²ū` and integrate".
`F` is any function satisfying the pointwise equation `hF`. -/
theorem degenerate_energy_identity {a u c V F : ℝ → ℝ} {j : ℝ}
    (ha : ContDiff ℝ 1 a) (hu : ContDiff ℝ 2 u) (hc : Continuous c) (hV : Continuous V)
    (hF : ∀ y, F y = -(deriv (fun t => a t * deriv u t) y) + j ^ 2 * c y * u y + V y * u y) :
    (∫ y in (0 : ℝ)..1, a y * (deriv (fun t => cylinderWeight t * u t) y) ^ 2)
      + j ^ 2 * ∫ y in (0 : ℝ)..1, c y * cylinderWeight y ^ 2 * u y ^ 2
    = (∫ y in (0 : ℝ)..1, F y * (cylinderWeight y ^ 2 * u y))
      + (∫ y in (0 : ℝ)..1, a y * (1 - 2 * y) ^ 2 * u y ^ 2)
      - ∫ y in (0 : ℝ)..1, V y * cylinderWeight y ^ 2 * u y ^ 2 := by
  have hac : Continuous a := ha.continuous
  have hu0 : Continuous u := hu.continuous
  have hu1 : Continuous (deriv u) := (contDiff_deriv_of_two hu).continuous
  have hG' := continuous_deriv_mul_deriv ha hu
  have hd := cylinderWeight_continuous
  have hD : ∀ y, deriv (fun t => cylinderWeight t * u t) y
      = (1 - 2 * y) * u y + cylinderWeight y * deriv u y :=
    fun y => (hasDerivAt_cw_mul hu y).deriv
  have hDc := continuous_deriv_cw_mul hu
  have hFc := continuous_forcing ha hu hc hV hF
  have hg : ∀ y, HasDerivAt (fun t => a t * deriv u t * (cylinderWeight t ^ 2 * u t))
      (deriv (fun t => a t * deriv u t) y * (cylinderWeight y ^ 2 * u y)
        + a y * deriv u y
          * (2 * cylinderWeight y * (1 - 2 * y) * u y + cylinderWeight y ^ 2 * deriv u y)) y :=
    fun y => (hasDerivAt_mul_deriv ha hu y).fun_mul (hasDerivAt_cw_sq_mul hu y)
  have hzero : ∫ y in (0 : ℝ)..1, (deriv (fun t => a t * deriv u t) y * (cylinderWeight y ^ 2 * u y)
        + a y * deriv u y
          * (2 * cylinderWeight y * (1 - 2 * y) * u y + cylinderWeight y ^ 2 * deriv u y)) = 0 :=
    integral_eq_zero_of_hasDerivAt hg (by fun_prop) (by simp) (by simp)
  have key := integral_lin5a (j ^ 2)
    (f₁ := fun y => a y * (deriv (fun t => cylinderWeight t * u t) y) ^ 2)
    (f₂ := fun y => c y * cylinderWeight y ^ 2 * u y ^ 2)
    (f₃ := fun y => F y * (cylinderWeight y ^ 2 * u y))
    (f₄ := fun y => a y * (1 - 2 * y) ^ 2 * u y ^ 2)
    (f₅ := fun y => V y * cylinderWeight y ^ 2 * u y ^ 2)
    (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
    (fun y => by
      try beta_reduce
      rw [hD y, hF y]
      ring) hzero
  linarith

/-- Item 2: the weighted energy bound for `(d u)'` and `j d^{3/2} u`
(constant `3 K²`). -/
theorem degenerate_energy_bound {a u c V F : ℝ → ℝ} {j K : ℝ}
    (ha : ContDiff ℝ 1 a) (hu : ContDiff ℝ 2 u) (hc : Continuous c) (hV : Continuous V)
    (hF : ∀ y, F y = -(deriv (fun t => a t * deriv u t) y) + j ^ 2 * c y * u y + V y * u y)
    (hK : 1 ≤ K)
    (ha₁ : ∀ y ∈ Icc (0 : ℝ) 1, 1 / K ≤ a y) (ha₂ : ∀ y ∈ Icc (0 : ℝ) 1, a y ≤ K)
    (hc₁ : ∀ y ∈ Icc (0 : ℝ) 1, cylinderWeight y / K ≤ c y)
    (hV₁ : ∀ y ∈ Icc (0 : ℝ) 1, |V y| ≤ K) :
    (∫ y in (0 : ℝ)..1, (deriv (fun t => cylinderWeight t * u t) y) ^ 2)
      + j ^ 2 * ∫ y in (0 : ℝ)..1, cylinderWeight y ^ 3 * u y ^ 2
      ≤ 3 * K ^ 2 * ((∫ y in (0 : ℝ)..1, F y ^ 2) + ∫ y in (0 : ℝ)..1, u y ^ 2) := by
  have hK0 : 0 < K := by linarith
  have hac : Continuous a := ha.continuous
  have hu0 : Continuous u := hu.continuous
  have hDc := continuous_deriv_cw_mul hu
  have hFc := continuous_forcing ha hu hc hV hF
  have hd := cylinderWeight_continuous
  have hid := degenerate_energy_identity ha hu hc hV hF
  have h1 : (∫ y in (0 : ℝ)..1, (deriv (fun t => cylinderWeight t * u t) y) ^ 2)
      ≤ K * ∫ y in (0 : ℝ)..1, a y * (deriv (fun t => cylinderWeight t * u t) y) ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on zero_le_one
      (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _) ?_
    intro y hy
    have h := (div_le_iff₀ hK0).1 (ha₁ y hy)
    nlinarith [mul_nonneg (sq_nonneg (deriv (fun t => cylinderWeight t * u t) y))
      (sub_nonneg.2 h)]
  have h2 : (∫ y in (0 : ℝ)..1, cylinderWeight y ^ 3 * u y ^ 2)
      ≤ K * ∫ y in (0 : ℝ)..1, c y * cylinderWeight y ^ 2 * u y ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on zero_le_one
      (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _) ?_
    intro y hy
    have h := (div_le_iff₀ hK0).1 (hc₁ y hy)
    nlinarith [mul_nonneg (mul_nonneg (sq_nonneg (cylinderWeight y)) (sq_nonneg (u y)))
      (sub_nonneg.2 h)]
  have hlin := integral_lin3 (f₁ := fun y => F y * (cylinderWeight y ^ 2 * u y))
    (f₂ := fun y => a y * (1 - 2 * y) ^ 2 * u y ^ 2)
    (f₃ := fun y => V y * cylinderWeight y ^ 2 * u y ^ 2)
    (by fun_prop) (by fun_prop) (by fun_prop)
  have hlin2 := integral_lin2 (1 / 2) (1 / 2 + 2 * K) (f := fun y => F y ^ 2)
    (g := fun y => u y ^ 2) (by fun_prop) (by fun_prop)
  have hmono : ∫ y in (0 : ℝ)..1, (F y * (cylinderWeight y ^ 2 * u y)
        + a y * (1 - 2 * y) ^ 2 * u y ^ 2 - V y * cylinderWeight y ^ 2 * u y ^ 2)
      ≤ ∫ y in (0 : ℝ)..1, (1 / 2 * F y ^ 2 + (1 / 2 + 2 * K) * u y ^ 2) := by
    refine intervalIntegral.integral_mono_on zero_le_one
      (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _) ?_
    intro y hy
    have hd0 := cylinderWeight_nonneg hy
    have hd1 := cylinderWeight_le_one hy
    have hs := one_sub_two_mul_sq_le_one hy
    have ha0 : 0 ≤ a y := le_trans (one_div_pos.2 hK0).le (ha₁ y hy)
    have haK := ha₂ y hy
    have hVa := abs_le.1 (hV₁ y hy)
    have ht1 : cylinderWeight y ^ 2 ≤ 1 := pow_le_one₀ hd0 hd1
    have ht2 : (cylinderWeight y ^ 2) ^ 2 ≤ 1 := pow_le_one₀ (sq_nonneg _) ht1
    have p1 : F y * (cylinderWeight y ^ 2 * u y) ≤ 1 / 2 * F y ^ 2 + 1 / 2 * u y ^ 2 := by
      nlinarith [sq_nonneg (F y - cylinderWeight y ^ 2 * u y),
        mul_nonneg (sq_nonneg (u y)) (sub_nonneg.2 ht2)]
    have p2 : a y * (1 - 2 * y) ^ 2 * u y ^ 2 ≤ K * u y ^ 2 := by
      nlinarith [mul_nonneg (mul_nonneg ha0 (sq_nonneg (u y))) (sub_nonneg.2 hs),
        mul_nonneg (sq_nonneg (u y)) (sub_nonneg.2 haK)]
    have hKV : 0 ≤ K + V y := by linarith [hVa.1]
    have p3 : -(V y * cylinderWeight y ^ 2 * u y ^ 2) ≤ K * u y ^ 2 := by
      nlinarith [mul_nonneg hKV (mul_nonneg (sq_nonneg (cylinderWeight y)) (sq_nonneg (u y))),
        mul_nonneg hK0.le (mul_nonneg (sq_nonneg (u y)) (sub_nonneg.2 ht1))]
    linarith
  have hS : (∫ y in (0 : ℝ)..1, F y * (cylinderWeight y ^ 2 * u y))
        + (∫ y in (0 : ℝ)..1, a y * (1 - 2 * y) ^ 2 * u y ^ 2)
        - (∫ y in (0 : ℝ)..1, V y * cylinderWeight y ^ 2 * u y ^ 2)
      ≤ 1 / 2 * (∫ y in (0 : ℝ)..1, F y ^ 2)
        + (1 / 2 + 2 * K) * ∫ y in (0 : ℝ)..1, u y ^ 2 := by
    linarith [hlin, hmono, hlin2]
  have hKS := mul_le_mul_of_nonneg_left hS hK0.le
  have hF0 : 0 ≤ ∫ y in (0 : ℝ)..1, F y ^ 2 :=
    intervalIntegral.integral_nonneg zero_le_one (fun y _ => sq_nonneg _)
  have hu_0 : 0 ≤ ∫ y in (0 : ℝ)..1, u y ^ 2 :=
    intervalIntegral.integral_nonneg zero_le_one (fun y _ => sq_nonneg _)
  have h2' := mul_le_mul_of_nonneg_left h2 (sq_nonneg j)
  have hmul : K * ((∫ y in (0 : ℝ)..1, a y * (deriv (fun t => cylinderWeight t * u t) y) ^ 2)
      + j ^ 2 * ∫ y in (0 : ℝ)..1, c y * cylinderWeight y ^ 2 * u y ^ 2)
      = K * ((∫ y in (0 : ℝ)..1, F y * (cylinderWeight y ^ 2 * u y))
        + (∫ y in (0 : ℝ)..1, a y * (1 - 2 * y) ^ 2 * u y ^ 2)
        - ∫ y in (0 : ℝ)..1, V y * cylinderWeight y ^ 2 * u y ^ 2) := by
    rw [hid]
  have e1 : 0 ≤ (∫ y in (0 : ℝ)..1, F y ^ 2) * (3 * K ^ 2 - K / 2) :=
    mul_nonneg hF0 (by nlinarith)
  have e2 : 0 ≤ (∫ y in (0 : ℝ)..1, u y ^ 2) * (K ^ 2 - K / 2) :=
    mul_nonneg hu_0 (by nlinarith)
  nlinarith [h1, h2', hmul, hKS, e1, e2]

/-- Item 2 (consequence): the bound for `d u'` (constant `8 K²`). -/
theorem degenerate_gradient_bound {a u c V F : ℝ → ℝ} {j K : ℝ}
    (ha : ContDiff ℝ 1 a) (hu : ContDiff ℝ 2 u) (hc : Continuous c) (hV : Continuous V)
    (hF : ∀ y, F y = -(deriv (fun t => a t * deriv u t) y) + j ^ 2 * c y * u y + V y * u y)
    (hK : 1 ≤ K)
    (ha₁ : ∀ y ∈ Icc (0 : ℝ) 1, 1 / K ≤ a y) (ha₂ : ∀ y ∈ Icc (0 : ℝ) 1, a y ≤ K)
    (hc₁ : ∀ y ∈ Icc (0 : ℝ) 1, cylinderWeight y / K ≤ c y)
    (hV₁ : ∀ y ∈ Icc (0 : ℝ) 1, |V y| ≤ K) :
    ∫ y in (0 : ℝ)..1, (cylinderWeight y * deriv u y) ^ 2
      ≤ 8 * K ^ 2 * ((∫ y in (0 : ℝ)..1, F y ^ 2) + ∫ y in (0 : ℝ)..1, u y ^ 2) := by
  have hb := degenerate_energy_bound ha hu hc hV hF hK ha₁ ha₂ hc₁ hV₁
  have hac : Continuous a := ha.continuous
  have hu0 : Continuous u := hu.continuous
  have hu1 : Continuous (deriv u) := (contDiff_deriv_of_two hu).continuous
  have hDc := continuous_deriv_cw_mul hu
  have hFc := continuous_forcing ha hu hc hV hF
  have hd := cylinderWeight_continuous
  have hB0 : 0 ≤ ∫ y in (0 : ℝ)..1, cylinderWeight y ^ 3 * u y ^ 2 :=
    intervalIntegral.integral_nonneg zero_le_one
      (fun y hy => mul_nonneg (pow_nonneg (cylinderWeight_nonneg hy) 3) (sq_nonneg _))
  have hjB := mul_nonneg (sq_nonneg j) hB0
  have hlin2 := integral_lin2 2 2
    (f := fun y => (deriv (fun t => cylinderWeight t * u t) y) ^ 2)
    (g := fun y => u y ^ 2) (by fun_prop) (by fun_prop)
  have hmono : ∫ y in (0 : ℝ)..1, (cylinderWeight y * deriv u y) ^ 2
      ≤ ∫ y in (0 : ℝ)..1, (2 * (deriv (fun t => cylinderWeight t * u t) y) ^ 2
        + 2 * u y ^ 2) := by
    refine intervalIntegral.integral_mono_on zero_le_one
      (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _) ?_
    intro y hy
    have hs := one_sub_two_mul_sq_le_one hy
    rw [(hasDerivAt_cw_mul hu y).deriv]
    nlinarith [sq_nonneg (2 * (1 - 2 * y) * u y + cylinderWeight y * deriv u y),
      mul_nonneg (sq_nonneg (u y)) (sub_nonneg.2 hs)]
  have hF0 : 0 ≤ ∫ y in (0 : ℝ)..1, F y ^ 2 :=
    intervalIntegral.integral_nonneg zero_le_one (fun y _ => sq_nonneg _)
  have hu_0 : 0 ≤ ∫ y in (0 : ℝ)..1, u y ^ 2 :=
    intervalIntegral.integral_nonneg zero_le_one (fun y _ => sq_nonneg _)
  have hK2 : 1 ≤ K ^ 2 := by nlinarith
  nlinarith [hb, hjB, hlin2, hmono, mul_nonneg hu_0 (sub_nonneg.2 hK2),
    mul_nonneg hF0 (sq_nonneg K)]

/-- Item 3: the squaring identity of the second stage (zero trace for `v`). -/
theorem dirichlet_square_identity {v q F₁ : ℝ → ℝ} {j : ℝ}
    (hv : ContDiff ℝ 2 v) (hv0 : v 0 = 0) (hv1 : v 1 = 0) (hq : ContDiff ℝ 2 q)
    (hF₁ : ∀ y, F₁ y = -(deriv (deriv v) y) + j ^ 2 * q y * v y) :
    (∫ y in (0 : ℝ)..1, deriv (deriv v) y ^ 2)
      + j ^ 4 * (∫ y in (0 : ℝ)..1, (q y * v y) ^ 2)
      + 2 * j ^ 2 * ∫ y in (0 : ℝ)..1, q y * deriv v y ^ 2
    = (∫ y in (0 : ℝ)..1, F₁ y ^ 2)
      + j ^ 2 * ∫ y in (0 : ℝ)..1, deriv (deriv q) y * v y ^ 2 := by
  have hvc : Continuous v := hv.continuous
  have hv1c : Continuous (deriv v) := (contDiff_deriv_of_two hv).continuous
  have hv2c : Continuous (deriv (deriv v)) :=
    (contDiff_deriv_of_two hv).continuous_deriv le_rfl
  have hqc : Continuous q := hq.continuous
  have hq1c : Continuous (deriv q) := (contDiff_deriv_of_two hq).continuous
  have hq2c : Continuous (deriv (deriv q)) :=
    (contDiff_deriv_of_two hq).continuous_deriv le_rfl
  have hF₁c : Continuous F₁ := by
    have hFe : F₁ = fun y => -(deriv (deriv v) y) + j ^ 2 * q y * v y := funext hF₁
    rw [hFe]
    fun_prop
  have hg : ∀ y, HasDerivAt
      (fun t => 2 * j ^ 2 * (q t * v t * deriv v t) - j ^ 2 * (deriv q t * (v t * v t)))
      (2 * j ^ 2 * ((deriv q y * v y + q y * deriv v y) * deriv v y
          + q y * v y * deriv (deriv v) y)
        - j ^ 2 * (deriv (deriv q) y * (v y * v y)
          + deriv q y * (deriv v y * v y + v y * deriv v y))) y := by
    intro y
    have e1 := ((hasDerivAt_of_contDiff_two hq y).fun_mul
      (hasDerivAt_of_contDiff_two hv y)).fun_mul (hasDerivAt_deriv_of_contDiff_two hv y)
    have e2 := (hasDerivAt_deriv_of_contDiff_two hq y).fun_mul
      ((hasDerivAt_of_contDiff_two hv y).fun_mul (hasDerivAt_of_contDiff_two hv y))
    exact (e1.const_mul (2 * j ^ 2)).fun_sub (e2.const_mul (j ^ 2))
  have hzero : ∫ y in (0 : ℝ)..1,
      (2 * j ^ 2 * ((deriv q y * v y + q y * deriv v y) * deriv v y
          + q y * v y * deriv (deriv v) y)
        - j ^ 2 * (deriv (deriv q) y * (v y * v y)
          + deriv q y * (deriv v y * v y + v y * deriv v y))) = 0 :=
    integral_eq_zero_of_hasDerivAt hg (by fun_prop) (by simp [hv0]) (by simp [hv1])
  have key := integral_lin5b (j ^ 4) (2 * j ^ 2) (j ^ 2)
    (f₁ := fun y => deriv (deriv v) y ^ 2)
    (f₂ := fun y => (q y * v y) ^ 2)
    (f₃ := fun y => q y * deriv v y ^ 2)
    (f₄ := fun y => F₁ y ^ 2)
    (f₅ := fun y => deriv (deriv q) y * v y ^ 2)
    (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
    (fun y => by
      try beta_reduce
      rw [hF₁ y]
      ring) hzero
  linarith

/-- Item 4: the equation for `v = d² u` (manuscript line 226). -/
theorem conjugated_degenerate_equation {a u c V F : ℝ → ℝ} {j : ℝ}
    (ha : ContDiff ℝ 1 a) (hu : ContDiff ℝ 2 u)
    (hF : ∀ y, F y = -(deriv (fun t => a t * deriv u t) y) + j ^ 2 * c y * u y + V y * u y)
    (y : ℝ) :
    -(deriv (fun t => a t * deriv (fun s => cylinderWeight s ^ 2 * u s) t) y)
      + j ^ 2 * c y * (cylinderWeight y ^ 2 * u y) + V y * (cylinderWeight y ^ 2 * u y)
    = cylinderWeight y ^ 2 * F y
      - 2 * a y * (2 * cylinderWeight y * (1 - 2 * y)) * deriv u y
      - deriv (fun t => a t * (2 * cylinderWeight t * (1 - 2 * t))) y * u y := by
  have hw : ∀ t, deriv (fun s => cylinderWeight s ^ 2 * u s) t
      = 2 * cylinderWeight t * (1 - 2 * t) * u t + cylinderWeight t ^ 2 * deriv u t :=
    fun t => (hasDerivAt_cw_sq_mul hu t).deriv
  have hfun : (fun t => a t * deriv (fun s => cylinderWeight s ^ 2 * u s) t)
      = fun t => a t * (2 * cylinderWeight t * (1 - 2 * t)) * u t
        + a t * deriv u t * cylinderWeight t ^ 2 := by
    funext t
    rw [hw t]
    ring
  have hHd0 : DifferentiableAt ℝ (fun t => a t * (2 * cylinderWeight t * (1 - 2 * t))) y :=
    ((hasDerivAt_of_contDiff_one ha y).fun_mul
      (((cylinderWeight_hasDerivAt y).const_mul 2).fun_mul
        (((hasDerivAt_id' y).const_mul 2).const_sub 1))).differentiableAt
  have hHd := hHd0.hasDerivAt
  have hT : HasDerivAt (fun t => a t * (2 * cylinderWeight t * (1 - 2 * t)) * u t
        + a t * deriv u t * cylinderWeight t ^ 2)
      (deriv (fun t => a t * (2 * cylinderWeight t * (1 - 2 * t))) y * u y
        + a y * (2 * cylinderWeight y * (1 - 2 * y)) * deriv u y
        + (deriv (fun t => a t * deriv u t) y * cylinderWeight y ^ 2
          + a y * deriv u y * (2 * cylinderWeight y * (1 - 2 * y)))) y :=
    (hHd.fun_mul (hasDerivAt_of_contDiff_two hu y)).fun_add
      ((hasDerivAt_mul_deriv ha hu y).fun_mul (cylinderWeight_sq_hasDerivAt y))
  rw [hfun, hT.deriv, hF y]
  ring

end ContinuousFlexibility.Analysis
