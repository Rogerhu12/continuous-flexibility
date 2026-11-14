module

public import ContinuousFlexibility.Scalar.HeightDerivatives
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff

/-!
# The explicit elliptic marker bump

This is the actual integral height used in `lem:fixed-cap`, Section 2.
The smooth zero extension is built from `expNegInvGlue`; no endpoint
regularity is assumed. Identification with surface curvature is separate.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility

open Set MeasureTheory
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

def markerKernel (ρ s : ℝ) : ℝ :=
  Real.exp 1 * expNegInvGlue (1 - s / ρ ^ 2)

def markerPrimitive (k ρ s : ℝ) : ℝ :=
  k / 2 * ∫ t in s..ρ ^ 2, markerKernel ρ t

def markerQuadratic (A B : ℝ) (x : PolarPoint) : ℝ :=
  A * x.1 ^ 2 + B * x.2 ^ 2

def markerBump (A B k ρ : ℝ) (x : PolarPoint) : ℝ :=
  markerPrimitive k ρ (markerQuadratic A B x)

theorem contDiff_markerKernel (ρ : ℝ) : ContDiff ℝ ∞ (markerKernel ρ) := by
  exact contDiff_const.mul (expNegInvGlue.contDiff.comp
    (contDiff_const.sub (contDiff_id.div_const _)))

theorem markerKernel_nonneg (ρ s : ℝ) : 0 ≤ markerKernel ρ s :=
  mul_nonneg (Real.exp_pos _).le (expNegInvGlue.nonneg _)

theorem markerKernel_eq_zero {ρ s : ℝ} (hρ : ρ ≠ 0) (hs : ρ ^ 2 ≤ s) :
    markerKernel ρ s = 0 := by
  have hr : 0 < ρ ^ 2 := sq_pos_of_ne_zero hρ
  unfold markerKernel
  rw [expNegInvGlue.zero_of_nonpos (by
    have := (one_le_div hr).2 hs
    linarith)]
  simp

theorem markerKernel_eq_exp {ρ s : ℝ} (hρ : ρ ≠ 0) (hs : s < ρ ^ 2) :
    markerKernel ρ s = Real.exp (-s / (ρ ^ 2 - s)) := by
  have hr : 0 < ρ ^ 2 := sq_pos_of_ne_zero hρ
  have hd : 0 < 1 - s / ρ ^ 2 := by
    have := (div_lt_one hr).2 hs
    linarith
  unfold markerKernel expNegInvGlue
  rw [ite_eq_right (not_le.mpr hd), ← Real.exp_add]
  congr 1
  field_simp [hρ, ne_of_gt (sub_pos.mpr hs)]
  ring

@[simp] theorem markerKernel_zero (ρ : ℝ) : markerKernel ρ 0 = 1 := by
  simp [markerKernel, expNegInvGlue, ← Real.exp_add]

theorem markerKernel_le_one {ρ s : ℝ} (hs : 0 ≤ s) : markerKernel ρ s ≤ 1 := by
  have harg : 1 - s / ρ ^ 2 ≤ 1 := by
    linarith [div_nonneg hs (sq_nonneg ρ)]
  calc
    markerKernel ρ s ≤ Real.exp 1 * expNegInvGlue 1 :=
      mul_le_mul_of_nonneg_left (expNegInvGlue.monotone harg) (Real.exp_pos _).le
    _ = 1 := by simpa only [markerKernel, zero_div, sub_zero] using markerKernel_zero ρ

theorem hasDerivAt_markerPrimitive (k ρ s : ℝ) :
    HasDerivAt (markerPrimitive k ρ) (-k / 2 * markerKernel ρ s) s := by
  have hc := (contDiff_markerKernel ρ).continuous
  change HasDerivAt (fun y : ℝ => k / 2 * ∫ t in y..ρ ^ 2, markerKernel ρ t) _ s
  convert! (intervalIntegral.integral_hasDerivAt_left (hc.intervalIntegrable _ _)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).const_mul (k / 2)
    using 1
  ring

theorem deriv_markerPrimitive (k ρ : ℝ) :
    deriv (markerPrimitive k ρ) = fun s => -k / 2 * markerKernel ρ s :=
  funext (fun s => (hasDerivAt_markerPrimitive k ρ s).deriv)

theorem contDiff_markerPrimitive (k ρ : ℝ) : ContDiff ℝ ∞ (markerPrimitive k ρ) := by
  apply contDiff_infty_iff_deriv.mpr
  constructor
  · exact fun s => (hasDerivAt_markerPrimitive k ρ s).differentiableAt
  · rw [deriv_markerPrimitive]
    exact contDiff_const.mul (contDiff_markerKernel ρ)

theorem markerPrimitive_eq_zero {k ρ s : ℝ} (hρ : ρ ≠ 0) (hs : ρ ^ 2 ≤ s) :
    markerPrimitive k ρ s = 0 := by
  have heq : (∫ t in s..ρ ^ 2, markerKernel ρ t) = ∫ t in s..ρ ^ 2, (0 : ℝ) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Icc (ρ ^ 2) s := by simpa only [uIcc_of_ge hs] using ht
    exact markerKernel_eq_zero hρ ht'.1
  simp [markerPrimitive, heq]

theorem markerPrimitive_nonneg {k ρ s : ℝ} (hk : 0 ≤ k) (hρ : ρ ≠ 0) :
    0 ≤ markerPrimitive k ρ s := by
  by_cases hs : s ≤ ρ ^ 2
  · exact mul_nonneg (by positivity)
      (intervalIntegral.integral_nonneg_of_forall hs (markerKernel_nonneg ρ))
  · rw [markerPrimitive_eq_zero hρ (le_of_not_ge hs)]

theorem markerPrimitive_le {k ρ s : ℝ} (hk : 0 ≤ k) (hρ : ρ ≠ 0) (hs : 0 ≤ s) :
    markerPrimitive k ρ s ≤ k * ρ ^ 2 / 2 := by
  by_cases hsr : s ≤ ρ ^ 2
  · have hi := intervalIntegral.integral_mono_on hsr
      ((contDiff_markerKernel ρ).continuous.intervalIntegrable s (ρ ^ 2))
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume s (ρ ^ 2))
      (fun t ht => markerKernel_le_one (hs.trans ht.1))
    simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one] at hi
    unfold markerPrimitive
    have := mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ k / 2)
    nlinarith [mul_nonneg hk hs]
  · rw [markerPrimitive_eq_zero hρ (le_of_not_ge hsr)]
    positivity

theorem contDiff_markerQuadratic (A B : ℝ) : ContDiff ℝ ∞ (markerQuadratic A B) := by
  exact (contDiff_const.mul (contDiff_fst.pow 2)).add
    (contDiff_const.mul (contDiff_snd.pow 2))

theorem contDiff_markerBump (A B k ρ : ℝ) : ContDiff ℝ ∞ (markerBump A B k ρ) :=
  (contDiff_markerPrimitive k ρ).comp (contDiff_markerQuadratic A B)

theorem markerBump_eq_zero {A B k ρ : ℝ} {x : PolarPoint}
    (hρ : ρ ≠ 0) (hx : ρ ^ 2 ≤ markerQuadratic A B x) :
    markerBump A B k ρ x = 0 :=
  markerPrimitive_eq_zero hρ hx

theorem markerBump_bounds {A B k ρ : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hk : 0 ≤ k) (hρ : ρ ≠ 0) (x : PolarPoint) :
    0 ≤ markerBump A B k ρ x ∧ markerBump A B k ρ x ≤ k * ρ ^ 2 / 2 := by
  constructor
  · exact markerPrimitive_nonneg hk hρ
  · exact markerPrimitive_le hk hρ (by unfold markerQuadratic; positivity)

theorem hasCompactSupport_markerBump {A B k ρ : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hρ : ρ ≠ 0) :
    HasCompactSupport (markerBump A B k ρ) := by
  let rA := ρ ^ 2 / A + 1
  let rB := ρ ^ 2 / B + 1
  apply HasCompactSupport.intro (K := Icc (-rA, -rB) (rA, rB)) isCompact_Icc
  intro x hx
  apply markerBump_eq_zero hρ
  by_contra h
  have hq : markerQuadratic A B x < ρ ^ 2 := lt_of_not_ge h
  have hx1 : x.1 ^ 2 ≤ ρ ^ 2 / A := (le_div_iff₀ hA).2 (by
    dsimp [markerQuadratic] at hq
    nlinarith [mul_nonneg hB.le (sq_nonneg x.2)])
  have hx2 : x.2 ^ 2 ≤ ρ ^ 2 / B := (le_div_iff₀ hB).2 (by
    dsimp [markerQuadratic] at hq
    nlinarith [mul_nonneg hA.le (sq_nonneg x.1)])
  have hA0 : 0 ≤ ρ ^ 2 / A := div_nonneg (sq_nonneg _) hA.le
  have hB0 : 0 ≤ ρ ^ 2 / B := div_nonneg (sq_nonneg _) hB.le
  apply hx
  constructor <;> constructor <;> dsimp [rA, rB]
  · nlinarith [sq_nonneg (x.1 + 1)]
  · nlinarith [sq_nonneg (x.2 + 1)]
  · nlinarith [sq_nonneg (x.1 - 1)]
  · nlinarith [sq_nonneg (x.2 - 1)]

def markerQuadraticDifferential (A B : ℝ) (x : PolarPoint) : PolarPoint →L[ℝ] ℝ :=
  (2 * A * x.1) • ContinuousLinearMap.fst ℝ ℝ ℝ +
    (2 * B * x.2) • ContinuousLinearMap.snd ℝ ℝ ℝ

theorem hasFDerivAt_markerQuadratic (A B : ℝ) (x : PolarPoint) :
    HasFDerivAt (markerQuadratic A B) (markerQuadraticDifferential A B x) x := by
  have hfst : HasFDerivAt (fun y : PolarPoint => y.1)
      (ContinuousLinearMap.fst ℝ ℝ ℝ) x := hasFDerivAt_fst
  have hsnd : HasFDerivAt (fun y : PolarPoint => y.2)
      (ContinuousLinearMap.snd ℝ ℝ ℝ) x := hasFDerivAt_snd
  convert! ((hfst.pow 2).const_mul A).add ((hsnd.pow 2).const_mul B) using 1
  apply ContinuousLinearMap.ext
  intro v
  simp [markerQuadraticDifferential]
  ring

theorem hasFDerivAt_markerBump (A B k ρ : ℝ) (x : PolarPoint) :
    HasFDerivAt (markerBump A B k ρ)
      ((-k / 2 * markerKernel ρ (markerQuadratic A B x)) •
        markerQuadraticDifferential A B x) x :=
  (hasDerivAt_markerPrimitive k ρ _).comp_hasFDerivAt x (hasFDerivAt_markerQuadratic A B x)

theorem fderiv_markerBump_apply (A B k ρ : ℝ) (x v : PolarPoint) :
    fderiv ℝ (markerBump A B k ρ) x v =
      -k * markerKernel ρ (markerQuadratic A B x) * (A * x.1 * v.1 + B * x.2 * v.2) := by
  rw [(hasFDerivAt_markerBump A B k ρ x).fderiv]
  simp [markerQuadraticDifferential]
  ring

@[simp] theorem fderiv_markerBump_zero (A B k ρ : ℝ) :
    fderiv ℝ (markerBump A B k ρ) 0 = 0 := by
  apply ContinuousLinearMap.ext
  intro v
  simp [fderiv_markerBump_apply]

theorem markerBump_secondDerivative_zero (A B k ρ : ℝ) (u v : PolarPoint) :
    fderiv ℝ (fun y => fderiv ℝ (markerBump A B k ρ) y u) 0 v =
      -k * (A * u.1 * v.1 + B * u.2 * v.2) := by
  have hf : (fun y => fderiv ℝ (markerBump A B k ρ) y u) =
      fun y => (-k * markerKernel ρ (markerQuadratic A B y)) *
        (A * y.1 * u.1 + B * y.2 * u.2) := by
    funext y
    exact fderiv_markerBump_apply A B k ρ y u
  have hk : DifferentiableAt ℝ (fun y => -k * markerKernel ρ (markerQuadratic A B y)) 0 :=
    ((contDiff_const.mul ((contDiff_markerKernel ρ).comp
      (contDiff_markerQuadratic A B))).differentiable (by simp)) 0
  have hfst : HasFDerivAt (fun y : PolarPoint => y.1)
      (ContinuousLinearMap.fst ℝ ℝ ℝ) (0 : PolarPoint) := hasFDerivAt_fst
  have hsnd : HasFDerivAt (fun y : PolarPoint => y.2)
      (ContinuousLinearMap.snd ℝ ℝ ℝ) (0 : PolarPoint) := hasFDerivAt_snd
  have hl := ((hfst.const_mul A).mul_const u.1).add ((hsnd.const_mul B).mul_const u.2)
  have hd := (hk.hasFDerivAt.mul hl).fderiv
  change fderiv ℝ (fun y : PolarPoint => (-k * markerKernel ρ (markerQuadratic A B y)) *
    (A * y.1 * u.1 + B * y.2 * u.2)) 0 = _ at hd
  rw [hf, hd]
  simp [markerQuadratic]
  ring

theorem hasDerivAt_markerKernel (ρ s : ℝ) :
    HasDerivAt (markerKernel ρ)
      (-(ρ ^ 2)⁻¹ * (1 - s / ρ ^ 2)⁻¹ ^ 2 * markerKernel ρ s) s := by
  have hg (t : ℝ) : HasDerivAt expNegInvGlue (t⁻¹ ^ 2 * expNegInvGlue t) t := by
    simpa using expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul (1 : Polynomial ℝ) t
  have ha := (hasDerivAt_const s (1 : ℝ)).sub ((hasDerivAt_id s).div_const (ρ ^ 2))
  convert! ((hg (1 - s / ρ ^ 2)).comp s ha).const_mul (Real.exp 1) using 1
  dsimp [markerKernel]
  ring

theorem deriv_markerKernel (ρ s : ℝ) :
    deriv (markerKernel ρ) s =
      -(ρ ^ 2)⁻¹ * (1 - s / ρ ^ 2)⁻¹ ^ 2 * markerKernel ρ s :=
  (hasDerivAt_markerKernel ρ s).deriv

theorem deriv_markerKernel_eq_zero {ρ s : ℝ} (hρ : ρ ≠ 0) (hs : ρ ^ 2 ≤ s) :
    deriv (markerKernel ρ) s = 0 := by
  rw [deriv_markerKernel, markerKernel_eq_zero hρ hs, mul_zero]

theorem deriv_markerKernel_of_lt {ρ s : ℝ} (hρ : ρ ≠ 0) (hs : s < ρ ^ 2) :
    deriv (markerKernel ρ) s = -ρ ^ 2 / (ρ ^ 2 - s) ^ 2 * markerKernel ρ s := by
  rw [deriv_markerKernel]
  congr 1
  field_simp [hρ, ne_of_gt (sub_pos.mpr hs)]

/-- The actual Hessian, evaluated on arbitrary coordinate directions. -/
theorem markerBump_secondDerivative (A B k ρ : ℝ) (x u v : PolarPoint) :
    fderiv ℝ (fun y => fderiv ℝ (markerBump A B k ρ) y u) x v =
      -k * markerKernel ρ (markerQuadratic A B x) * (A * u.1 * v.1 + B * u.2 * v.2) -
      2 * k * deriv (markerKernel ρ) (markerQuadratic A B x) *
        (A * x.1 * u.1 + B * x.2 * u.2) * (A * x.1 * v.1 + B * x.2 * v.2) := by
  have hf : (fun y => fderiv ℝ (markerBump A B k ρ) y u) =
      fun y => (-k * markerKernel ρ (markerQuadratic A B y)) *
        (A * y.1 * u.1 + B * y.2 * u.2) := by
    funext y
    exact fderiv_markerBump_apply A B k ρ y u
  have hk := (((contDiff_markerKernel ρ).differentiable (by simp)
    (markerQuadratic A B x)).hasDerivAt.comp_hasFDerivAt x
      (hasFDerivAt_markerQuadratic A B x)).const_mul (-k)
  have hfst : HasFDerivAt (fun y : PolarPoint => y.1)
      (ContinuousLinearMap.fst ℝ ℝ ℝ) x := hasFDerivAt_fst
  have hsnd : HasFDerivAt (fun y : PolarPoint => y.2)
      (ContinuousLinearMap.snd ℝ ℝ ℝ) x := hasFDerivAt_snd
  have hl := ((hfst.const_mul A).mul_const u.1).add ((hsnd.const_mul B).mul_const u.2)
  have hd := (hk.mul hl).fderiv
  change fderiv ℝ (fun y : PolarPoint => (-k * markerKernel ρ (markerQuadratic A B y)) *
    (A * y.1 * u.1 + B * y.2 * u.2)) x = _ at hd
  rw [hf, hd]
  simp [markerQuadraticDifferential]
  ring

theorem markerBump_secondDerivative_of_lt {A B k ρ : ℝ} {x : PolarPoint}
    (hρ : ρ ≠ 0) (hx : markerQuadratic A B x < ρ ^ 2) (u v : PolarPoint) :
    fderiv ℝ (fun y => fderiv ℝ (markerBump A B k ρ) y u) x v =
      -k * markerKernel ρ (markerQuadratic A B x) * (A * u.1 * v.1 + B * u.2 * v.2) +
      2 * k * markerKernel ρ (markerQuadratic A B x) *
        (ρ ^ 2 / (ρ ^ 2 - markerQuadratic A B x) ^ 2) *
        (A * x.1 * u.1 + B * x.2 * u.2) * (A * x.1 * v.1 + B * x.2 * v.2) := by
  rw [markerBump_secondDerivative, deriv_markerKernel_of_lt hρ hx]
  ring

theorem markerBump_secondDerivative_eq_zero {A B k ρ : ℝ} {x : PolarPoint}
    (hρ : ρ ≠ 0) (hx : ρ ^ 2 ≤ markerQuadratic A B x) (u v : PolarPoint) :
    fderiv ℝ (fun y => fderiv ℝ (markerBump A B k ρ) y u) x v = 0 := by
  rw [markerBump_secondDerivative, markerKernel_eq_zero hρ hx,
    deriv_markerKernel_eq_zero hρ hx]
  ring

end ContinuousFlexibility
