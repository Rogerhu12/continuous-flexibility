module

public import ContinuousFlexibility.Radial.CentralRadiusGrowth
public import ContinuousFlexibility.Radial.RadialDampedBounds
public import ContinuousFlexibility.Radial.RadialSymbolBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Fixed-order right-end estimates for the actual central radius

The logarithmic derivative is that of the actual positive Laplace--Gaussian
radius. Its proved differential equation gives a damped Riccati error
equation. The power comparison is applied to actual derivatives, keeping
one threshold for all orders.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

private def centralPsiLogDerivative (x : ℝ) : ℝ :=
  deriv centralRadiusPsi x / centralRadiusPsi x

private theorem hasDerivAt_centralPsiLogDerivative (x : ℝ) :
    HasDerivAt centralPsiLogDerivative
      (x ^ 2 + centralRadiusC - centralPsiLogDerivative x ^ 2) x := by
  have h0 : 0 < centralRadiusAlpha := by linarith [centralRadiusAlpha_gt_half]
  have h1 := ((contDiff_centralRadiusPsi.differentiable (by simp)) x).hasDerivAt
  have h2 := hasDerivAt_deriv_gaussianLaplacePsi h0 x
  change HasDerivAt (deriv centralRadiusPsi)
    ((x ^ 2 + (2 * centralRadiusAlpha - 1)) * centralRadiusPsi x) x at h2
  rw [show 2 * centralRadiusAlpha - 1 = centralRadiusC by
    unfold centralRadiusAlpha
    ring] at h2
  have h := h2.div h1 (centralRadiusPsi_pos x).ne'
  convert h using 1
  · funext y
    rfl
  · change x ^ 2 + centralRadiusC - (deriv centralRadiusPsi x / centralRadiusPsi x) ^ 2 =
      ((x ^ 2 + centralRadiusC) * centralRadiusPsi x * centralRadiusPsi x -
        deriv centralRadiusPsi x * deriv centralRadiusPsi x) / centralRadiusPsi x ^ 2
    field_simp [(centralRadiusPsi_pos x).ne']

private theorem centralPsiLogDerivative_eq (x : ℝ) :
    centralPsiLogDerivative x = centralRadiusLogDerivative x - centralRadiusA := by
  rw [centralRadiusLogDerivative_eq]
  have h0 : 0 < centralRadiusAlpha := by linarith [centralRadiusAlpha_gt_half]
  change deriv (gaussianLaplacePsi centralRadiusAlpha) x /
    gaussianLaplacePsi centralRadiusAlpha x = _
  rw [gaussianLaplacePsi_log_deriv h0]
  ring

/-- The Riccati equation follows from the actual integral solution's ODE. -/
theorem hasDerivAt_centralRadiusLogDerivative (x : ℝ) :
    HasDerivAt centralRadiusLogDerivative
      (x ^ 2 + centralRadiusC - (centralRadiusLogDerivative x - centralRadiusA) ^ 2) x := by
  have h := (hasDerivAt_centralPsiLogDerivative x).add_const centralRadiusA
  have heq : (fun y => centralPsiLogDerivative y + centralRadiusA) =
      centralRadiusLogDerivative := by
    funext y
    rw [centralPsiLogDerivative_eq]
    ring
  rw [heq, centralPsiLogDerivative_eq] at h
  exact h

theorem centralRadiusLogDerivative_riccati (x : ℝ) :
    deriv centralRadiusLogDerivative x =
      x ^ 2 + centralRadiusC - (centralRadiusLogDerivative x - centralRadiusA) ^ 2 :=
  (hasDerivAt_centralRadiusLogDerivative x).deriv

def centralRightLogDerivativeModel (L : ℝ) : ℝ :=
  L + (centralRadiusAlpha - 1) / L

def centralRightLogDerivativeError (L : ℝ) : ℝ :=
  centralRadiusLogDerivative L - centralRadiusA - centralRightLogDerivativeModel L

def centralRightRiccatiResidual (L : ℝ) : ℝ :=
  (centralRadiusAlpha - 1) * (centralRadiusAlpha - 2) * L ^ (-2 : ℝ)

private theorem centralRightLogDerivativeModel_contDiffOn :
    ContDiffOn ℝ ∞ centralRightLogDerivativeModel (Ioi 0) :=
  contDiffOn_id.add (contDiffOn_const.div contDiffOn_id (fun _L hL => ne_of_gt hL))

theorem centralRightLogDerivativeError_contDiffOn :
    ContDiffOn ℝ ∞ centralRightLogDerivativeError (Ioi 0) :=
  (contDiff_centralRadiusLogDerivative.contDiffOn.sub contDiffOn_const).sub
    centralRightLogDerivativeModel_contDiffOn

private theorem centralRightRiccatiResidual_contDiffOn :
    ContDiffOn ℝ ∞ centralRightRiccatiResidual (Ioi 0) :=
  contDiffOn_const.mul (contDiffOn_id.rpow_const_of_ne (fun _L hL => ne_of_gt hL))

private theorem hasDerivAt_centralRightLogDerivativeModel {L : ℝ} (hL : 0 < L) :
    HasDerivAt centralRightLogDerivativeModel (1 - (centralRadiusAlpha - 1) / L ^ 2) L := by
  convert (hasDerivAt_id L).add
    ((hasDerivAt_const L (centralRadiusAlpha - 1)).div (hasDerivAt_id L) hL.ne') using 1
  · funext y
    rfl
  · change 1 - (centralRadiusAlpha - 1) / L ^ 2 =
      1 + (0 * L - (centralRadiusAlpha - 1) * 1) / L ^ 2
    ring

/-- The cubic error has a real damped differential equation; no
right-end asymptotic is assumed in deriving it. -/
theorem hasDerivAt_centralRightLogDerivativeError {L : ℝ} (hL : 0 < L) :
    HasDerivAt centralRightLogDerivativeError
      (-(centralRadiusLogDerivative L - centralRadiusA + centralRightLogDerivativeModel L) *
          centralRightLogDerivativeError L - centralRightRiccatiResidual L) L := by
  have h := ((hasDerivAt_centralRadiusLogDerivative L).sub_const centralRadiusA).sub
    (hasDerivAt_centralRightLogDerivativeModel hL)
  convert h using 1
  · funext y
    rfl
  · change -(centralRadiusLogDerivative L - centralRadiusA + (L + (centralRadiusAlpha - 1) / L)) *
        (centralRadiusLogDerivative L - centralRadiusA - (L + (centralRadiusAlpha - 1) / L)) -
        (centralRadiusAlpha - 1) * (centralRadiusAlpha - 2) * L ^ (-2 : ℝ) =
      (L ^ 2 + centralRadiusC - (centralRadiusLogDerivative L - centralRadiusA) ^ 2) -
        (1 - (centralRadiusAlpha - 1) / L ^ 2)
    rw [rpow_neg hL.le, rpow_two]
    have hc : centralRadiusC = 2 * centralRadiusAlpha - 1 := by
      unfold centralRadiusAlpha
      ring
    rw [hc]
    field_simp [hL.ne']
    ring

private theorem radial_rpow_symbol (L0 s : ℝ) :
    RadialSymbolBounds L0 s (fun L : ℝ => L ^ s) := by
  refine ⟨contDiffOn_id.rpow_const_of_ne (fun L hL => ne_of_gt hL), ?_⟩
  intro r
  refine ⟨‖(descPochhammer ℝ r).eval s‖, norm_nonneg _, ?_⟩
  intro L _ hL
  rw [iteratedDeriv_eq_iterate, iter_deriv_rpow_const, norm_mul,
    Real.norm_of_nonneg (rpow_nonneg hL.le _)]

private theorem radial_symbol_order_mono {L0 s t : ℝ} {f : ℝ → ℝ}
    (hL0 : 1 ≤ L0) (hst : s ≤ t) (hf : RadialSymbolBounds L0 s f) :
    RadialSymbolBounds L0 t f := by
  refine ⟨hf.1, ?_⟩
  intro r
  obtain ⟨C, hC, hCf⟩ := hf.2 r
  refine ⟨C, hC, ?_⟩
  intro L hL hLp
  exact (hCf L hL hLp).trans
    (mul_le_mul_of_nonneg_left
      (rpow_le_rpow_of_exponent_le (hL0.trans hL) (sub_le_sub_right hst _)) hC)

private theorem centralRightLogDerivativeModel_symbol {L0 : ℝ} (hL0 : 1 ≤ L0) :
    RadialSymbolBounds L0 1 centralRightLogDerivativeModel := by
  have hid := radial_rpow_symbol L0 1
  have hinv := (radial_rpow_symbol L0 (-1)).const_mul (centralRadiusAlpha - 1)
  have hh := hid.add (radial_symbol_order_mono hL0 (by norm_num : (-1 : ℝ) ≤ 1) hinv)
  convert hh using 1
  funext L
  change L + (centralRadiusAlpha - 1) / L =
    L ^ (1 : ℝ) + (centralRadiusAlpha - 1) * L ^ (-1 : ℝ)
  rw [rpow_one, rpow_neg_one, div_eq_mul_inv]

private theorem centralRightRiccatiResidual_symbol (L0 : ℝ) :
    RadialSymbolBounds L0 (-2) centralRightRiccatiResidual :=
  (radial_rpow_symbol L0 (-2)).const_mul ((centralRadiusAlpha - 1) * (centralRadiusAlpha - 2))

private theorem centralRightLogDerivativeModel_lower {L : ℝ} (hL : 1 ≤ L) :
    L / 2 ≤ centralRightLogDerivativeModel L := by
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hβ := centralRadiusAlpha_gt_half
  have hh : -(1 / 2 : ℝ) ≤ (centralRadiusAlpha - 1) / L := by
    apply (le_div_iff₀ hLp).mpr
    nlinarith only [hβ, hL]
  unfold centralRightLogDerivativeModel
  linarith only [hL, hh]

/-- The leading cubic estimate is obtained by damping, not by
differentiating a scalar big-O assertion. -/
theorem centralRightLogDerivativeError_zero_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℝ, 1 ≤ L → ‖centralRightLogDerivativeError L‖ ≤ C * L ^ (-3 : ℝ) := by
  obtain ⟨B, hB, hb⟩ := (centralRightRiccatiResidual_symbol 1).2 0
  have h := exists_norm_power_bound_of_damped_deriv (L0 := 1) (c := 1 / 2) (m := 2)
    (u := centralRightLogDerivativeError)
    (a := fun L => centralRadiusLogDerivative L - centralRadiusA + centralRightLogDerivativeModel L)
    (b := fun L => -centralRightRiccatiResidual L)
    (by norm_num) (by norm_num) hB (by norm_num)
    (centralRightLogDerivativeError_contDiffOn.continuousOn.mono (by
      intro L hL
      change 1 ≤ L at hL
      change 0 < L
      exact lt_of_lt_of_le zero_lt_one hL))
    (fun L hL => by
      simpa only [sub_eq_add_neg] using
        hasDerivAt_centralRightLogDerivativeError (lt_of_lt_of_le zero_lt_one hL))
    (fun L hL => by
      have hq := centralRadiusLogDerivative_gt L
      have hv := centralRightLogDerivativeModel_lower hL
      linarith)
    (fun L hL => by
      simpa only [norm_neg, iteratedDeriv_zero, Nat.cast_zero, sub_zero] using
        hb L hL (lt_of_lt_of_le zero_lt_one hL))
  simpa only [show (- (2 : ℝ) - 1) = -3 by norm_num] using h

private def RightTailPowerBound (L0 s : ℝ) (f : ℝ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℝ, L0 ≤ L → ‖f L‖ ≤ C * L ^ s

private theorem RightTailPowerBound.add {L0 s : ℝ} {f g : ℝ → ℝ}
    (hf : RightTailPowerBound L0 s f) (hg : RightTailPowerBound L0 s g) :
    RightTailPowerBound L0 s (f + g) := by
  obtain ⟨A, hA, hAf⟩ := hf
  obtain ⟨B, hB, hBg⟩ := hg
  refine ⟨A + B, add_nonneg hA hB, ?_⟩
  intro L hL
  calc
    _ ≤ ‖f L‖ + ‖g L‖ := norm_add_le _ _
    _ ≤ A * L ^ s + B * L ^ s := add_le_add (hAf L hL) (hBg L hL)
    _ = _ := by ring

private theorem RightTailPowerBound.const_mul {L0 s : ℝ} {f : ℝ → ℝ}
    (hf : RightTailPowerBound L0 s f) (a : ℝ) :
    RightTailPowerBound L0 s (fun L => a * f L) := by
  obtain ⟨A, hA, hAf⟩ := hf
  refine ⟨‖a‖ * A, mul_nonneg (norm_nonneg _) hA, ?_⟩
  intro L hL
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_left (hAf L hL) (norm_nonneg _)).trans_eq (by ring)

private theorem RightTailPowerBound.mul {L0 s t : ℝ} {f g : ℝ → ℝ}
    (hf : RightTailPowerBound L0 s f) (hL0 : 0 < L0) (hg : RightTailPowerBound L0 t g) :
    RightTailPowerBound L0 (s + t) (f * g) := by
  obtain ⟨A, hA, hAf⟩ := hf
  obtain ⟨B, hB, hBg⟩ := hg
  refine ⟨A * B, mul_nonneg hA hB, ?_⟩
  intro L hL
  have hLp := hL0.trans_le hL
  rw [Pi.mul_apply, norm_mul]
  calc
    _ ≤ (A * L ^ s) * (B * L ^ t) :=
      mul_le_mul (hAf L hL) (hBg L hL) (norm_nonneg _)
        (mul_nonneg hA (rpow_nonneg hLp.le _))
    _ = (A * B) * (L ^ s * L ^ t) := by ring
    _ = _ := by rw [← rpow_add hLp]

private theorem RightTailPowerBound.mono_order {L0 s t : ℝ} {f : ℝ → ℝ}
    (hf : RightTailPowerBound L0 s f) (hL0 : 1 ≤ L0) (hst : s ≤ t) :
    RightTailPowerBound L0 t f := by
  obtain ⟨C, hC, hCf⟩ := hf
  refine ⟨C, hC, ?_⟩
  intro L hL
  exact (hCf L hL).trans (mul_le_mul_of_nonneg_left
    (rpow_le_rpow_of_exponent_le (hL0.trans hL) hst) hC)

private theorem rightTailPowerBound_sum {ι : Type*} (s : Finset ι)
    {L0 t : ℝ} {f : ι → ℝ → ℝ}
    (hf : ∀ i ∈ s, RightTailPowerBound L0 t (f i)) :
    RightTailPowerBound L0 t (fun L => ∑ i ∈ s, f i L) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, le_rfl, by simp⟩
  | @insert i s hi ih =>
    have hh := (hf i (Finset.mem_insert_self _ _)).add
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))
    convert hh using 1
    funext L
    change (∑ j ∈ (insert i s : Finset ι), f j L) = f i L + ∑ j ∈ s, f j L
    rw [Finset.sum_insert hi]

private theorem symbol_derivative_tail {L0 s : ℝ} {f : ℝ → ℝ}
    (hL0 : 0 < L0) (hf : RadialSymbolBounds L0 s f) (r : ℕ) :
    RightTailPowerBound L0 (s - (r : ℝ)) (iteratedDeriv r f) := by
  obtain ⟨C, hC, hCf⟩ := hf.2 r
  exact ⟨C, hC, fun L hL => hCf L hL (hL0.trans_le hL)⟩

private def centralRightDerivativeForcing (n : ℕ) (L : ℝ) : ℝ :=
  -iteratedDeriv (n + 1) centralRightRiccatiResidual L -
    2 * (∑ i ∈ Finset.range (n + 1), ((n + 1).choose (i + 1) : ℝ) *
      iteratedDeriv (i + 1) centralRightLogDerivativeModel L *
      iteratedDeriv (n - i) centralRightLogDerivativeError L) -
    (∑ i ∈ Finset.range n, ((n + 1).choose (i + 1) : ℝ) *
      iteratedDeriv (i + 1) centralRightLogDerivativeError L *
      iteratedDeriv (n - i) centralRightLogDerivativeError L)

private theorem centralRightDerivativeForcing_bound {L0 : ℝ} (hL0 : 1 ≤ L0) (n : ℕ)
    (hprev : ∀ k : ℕ, k < n + 1 →
      RightTailPowerBound L0 (-3 - (k : ℝ)) (iteratedDeriv k centralRightLogDerivativeError)) :
    RightTailPowerBound L0 (-2 - ((n + 1 : ℕ) : ℝ)) (centralRightDerivativeForcing n) := by
  have hLp : 0 < L0 := zero_lt_one.trans_le hL0
  have hR := (symbol_derivative_tail hLp (centralRightRiccatiResidual_symbol L0) (n + 1)).const_mul (-1)
  have hV := rightTailPowerBound_sum (Finset.range (n + 1)) (fun i hi => by
    have hin : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    have hki : n - i < n + 1 := (Nat.sub_le n i).trans_lt (Nat.lt_succ_self n)
    have hh := (symbol_derivative_tail hLp (centralRightLogDerivativeModel_symbol hL0) (i + 1)).mul
      hLp (hprev (n - i) hki)
    have he : (1 - ((i + 1 : ℕ) : ℝ)) + (-3 - ((n - i : ℕ) : ℝ)) =
        -2 - ((n + 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub hin]
      push_cast
      ring
    rw [he] at hh
    simpa only [Pi.mul_apply, ← mul_assoc] using
      hh.const_mul ((n + 1).choose (i + 1) : ℝ))
  have hE := rightTailPowerBound_sum (Finset.range n) (fun i hi => by
    have hin : i < n := Finset.mem_range.mp hi
    have hki : n - i < n + 1 := (Nat.sub_le n i).trans_lt (Nat.lt_succ_self n)
    have hh := (hprev (i + 1) (Nat.succ_lt_succ hin)).mul hLp (hprev (n - i) hki)
    have he : (-3 - ((i + 1 : ℕ) : ℝ)) + (-3 - ((n - i : ℕ) : ℝ)) =
        -6 - ((n + 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub hin.le]
      push_cast
      ring
    rw [he] at hh
    simpa only [Pi.mul_apply, ← mul_assoc] using
      (hh.mono_order hL0 (by linarith : -6 - ((n + 1 : ℕ) : ℝ) ≤
        -2 - ((n + 1 : ℕ) : ℝ))).const_mul ((n + 1).choose (i + 1) : ℝ))
  have hh := (hR.add (hV.const_mul (-2))).add (hE.const_mul (-1))
  convert hh using 1
  funext L
  simp only [centralRightDerivativeForcing, Pi.add_apply]
  ring

private theorem centralRight_error_ode {L : ℝ} (hL : 0 < L) :
    deriv centralRightLogDerivativeError L =
      -2 * (centralRightLogDerivativeModel L * centralRightLogDerivativeError L) -
        centralRightLogDerivativeError L * centralRightLogDerivativeError L -
        centralRightRiccatiResidual L := by
  rw [(hasDerivAt_centralRightLogDerivativeError hL).deriv]
  unfold centralRightLogDerivativeError
  ring

private theorem iteratedDeriv_product_split {f g : ℝ → ℝ} {L : ℝ} (n : ℕ)
    (hf : ContDiffAt ℝ ((n + 1 : ℕ) : ℕ∞ω) f L)
    (hg : ContDiffAt ℝ ((n + 1 : ℕ) : ℕ∞ω) g L) :
    iteratedDeriv (n + 1) (f * g) L = f L * iteratedDeriv (n + 1) g L +
      ∑ i ∈ Finset.range (n + 1), ((n + 1).choose (i + 1) : ℝ) *
        iteratedDeriv (i + 1) f L * iteratedDeriv (n - i) g L := by
  rw [iteratedDeriv_mul hf hg, Finset.sum_range_succ']
  simp only [Nat.choose_zero_right, Nat.cast_one, iteratedDeriv_zero, Nat.sub_zero,
    one_mul, Nat.add_sub_add_right]
  ring

private theorem centralRightDerivativeForcing_identity {L : ℝ} (hL : 0 < L) (n : ℕ) :
    iteratedDeriv (n + 1 + 1) centralRightLogDerivativeError L =
      -(2 * (centralRadiusLogDerivative L - centralRadiusA)) *
        iteratedDeriv (n + 1) centralRightLogDerivativeError L +
        centralRightDerivativeForcing n L := by
  have he : ContDiffAt ℝ ∞ centralRightLogDerivativeError L :=
    centralRightLogDerivativeError_contDiffOn.contDiffAt (isOpen_Ioi.mem_nhds hL)
  have hv : ContDiffAt ℝ ∞ centralRightLogDerivativeModel L :=
    centralRightLogDerivativeModel_contDiffOn.contDiffAt (isOpen_Ioi.mem_nhds hL)
  have hR : ContDiffAt ℝ ∞ centralRightRiccatiResidual L :=
    centralRightRiccatiResidual_contDiffOn.contDiffAt (isOpen_Ioi.mem_nhds hL)
  have heq : deriv centralRightLogDerivativeError =ᶠ[𝓝 L]
      (-2 : ℝ) • (centralRightLogDerivativeModel * centralRightLogDerivativeError) -
        (centralRightLogDerivativeError * centralRightLogDerivativeError) - centralRightRiccatiResidual :=
    (eventually_gt_nhds hL).mono (fun x hx => centralRight_error_ode hx)
  have hsm : ContDiffAt ℝ ((n + 1 : ℕ) : ℕ∞ω)
      ((-2 : ℝ) • (centralRightLogDerivativeModel * centralRightLogDerivativeError)) L :=
    (ContDiffAt.const_smul (-2 : ℝ) (hv.mul he)).of_le (by simp)
  have hsq : ContDiffAt ℝ ((n + 1 : ℕ) : ℕ∞ω)
      (centralRightLogDerivativeError * centralRightLogDerivativeError) L :=
    (he.mul he).of_le (by simp)
  have hd := heq.iteratedDeriv_eq (n + 1)
  rw [← iteratedDeriv_succ'] at hd
  have hdiff : ContDiffAt ℝ ((n + 1 : ℕ) : ℕ∞ω)
      ((-2 : ℝ) • (centralRightLogDerivativeModel * centralRightLogDerivativeError) -
        centralRightLogDerivativeError * centralRightLogDerivativeError) L := hsm.sub hsq
  have hout := iteratedDeriv_sub (n := n + 1) (x := L)
    (f := (-2 : ℝ) • (centralRightLogDerivativeModel * centralRightLogDerivativeError) -
      centralRightLogDerivativeError * centralRightLogDerivativeError)
    (g := centralRightRiccatiResidual) hdiff (hR.of_le (by simp))
  have hin := iteratedDeriv_sub (n := n + 1) (x := L)
    (f := (-2 : ℝ) • (centralRightLogDerivativeModel * centralRightLogDerivativeError))
    (g := centralRightLogDerivativeError * centralRightLogDerivativeError) hsm hsq
  rw [hout, hin, iteratedDeriv_const_smul_field (n := n + 1)] at hd
  have hVE := iteratedDeriv_product_split n (hv.of_le (by simp)) (he.of_le (by simp))
  have hEE := iteratedDeriv_product_split n (he.of_le (by simp)) (he.of_le (by simp))
  rw [Finset.sum_range_succ] at hEE
  simp only [Nat.choose_self, Nat.cast_one, Nat.sub_self, iteratedDeriv_zero, one_mul] at hEE
  rw [hVE, hEE] at hd
  rw [hd]
  simp only [centralRightDerivativeForcing, smul_eq_mul, centralRightLogDerivativeError]
  ring

private theorem centralRightError_iteratedDeriv_contDiffOn (r : ℕ) :
    ContDiffOn ℝ ∞ (iteratedDeriv r centralRightLogDerivativeError) (Ioi 0) := by
  induction r with
  | zero => simpa only [iteratedDeriv_zero] using centralRightLogDerivativeError_contDiffOn
  | succ r ih =>
    rw [iteratedDeriv_succ]
    exact ih.deriv_of_isOpen isOpen_Ioi (by simp)

private theorem hasDerivAt_centralRightError_iteratedDeriv {L : ℝ} (hL : 0 < L) (n : ℕ) :
    HasDerivAt (iteratedDeriv (n + 1) centralRightLogDerivativeError)
      (-(2 * (centralRadiusLogDerivative L - centralRadiusA)) *
        iteratedDeriv (n + 1) centralRightLogDerivativeError L +
        centralRightDerivativeForcing n L) L := by
  have h := (((centralRightError_iteratedDeriv_contDiffOn (n + 1)).contDiffAt
    (isOpen_Ioi.mem_nhds hL)).differentiableAt (by simp)).hasDerivAt
  rw [← iteratedDeriv_succ, centralRightDerivativeForcing_identity hL n] at h
  exact h

/-- Every fixed derivative of the actual right-end cubic error has its
predicted decay. The final threshold is `1` at every order. -/
theorem centralRightLogDerivativeError_symbol :
    RadialSymbolBounds 1 (-3) centralRightLogDerivativeError := by
  obtain ⟨B0, hB0, hbase⟩ := centralRightLogDerivativeError_zero_bound
  let L0 : ℝ := 2 * B0 + 2
  have hL01 : 1 ≤ L0 := by dsimp [L0]; linarith only [hB0]
  have hL0p : 0 < L0 := zero_lt_one.trans_le hL01
  have hq : ∀ L : ℝ, L0 ≤ L → L / 2 ≤ centralRadiusLogDerivative L - centralRadiusA := by
    intro L hL
    have hL1 : 1 ≤ L := hL01.trans hL
    have hLp : 0 < L := zero_lt_one.trans_le hL1
    have hp : L ^ (-3 : ℝ) ≤ 1 := by
      have hh := rpow_le_rpow_of_exponent_le hL1 (by norm_num : (-3 : ℝ) ≤ 0)
      simpa only [rpow_zero] using hh
    have he : ‖centralRightLogDerivativeError L‖ ≤ B0 :=
      (hbase L hL1).trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hp hB0)
    have helo : -B0 ≤ centralRightLogDerivativeError L :=
      (neg_le_neg he).trans (neg_abs_le _)
    have hv : L - 1 / 2 ≤ centralRightLogDerivativeModel L := by
      have hb : -(1 / 2 : ℝ) ≤ (centralRadiusAlpha - 1) / L := by
        apply (le_div_iff₀ hLp).mpr
        nlinarith only [centralRadiusAlpha_gt_half, hL1]
      unfold centralRightLogDerivativeModel
      linarith only [hb]
    have heq : centralRadiusLogDerivative L - centralRadiusA =
        centralRightLogDerivativeModel L + centralRightLogDerivativeError L := by
      unfold centralRightLogDerivativeError
      ring
    rw [heq]
    dsimp [L0] at hL
    linarith only [hv, helo, hL]
  have hbound : ∀ r : ℕ,
      RightTailPowerBound L0 (-3 - (r : ℝ)) (iteratedDeriv r centralRightLogDerivativeError) := by
    intro r
    induction r using Nat.strong_induction_on with
    | h r ih =>
      rcases r with _ | n
      · exact ⟨B0, hB0, fun L hL => by
          simpa only [iteratedDeriv_zero, Nat.cast_zero, sub_zero] using hbase L (hL01.trans hL)⟩
      · obtain ⟨B, hB, hb⟩ := centralRightDerivativeForcing_bound hL01 n (fun k hk => ih k hk)
        have hd := exists_norm_power_bound_of_damped_deriv
          (L0 := L0) (c := 1) (m := 2 + ((n + 1 : ℕ) : ℝ))
          (u := iteratedDeriv (n + 1) centralRightLogDerivativeError)
          (a := fun L => 2 * (centralRadiusLogDerivative L - centralRadiusA))
          (b := centralRightDerivativeForcing n)
          hL0p zero_lt_one hB (by positivity)
          ((centralRightError_iteratedDeriv_contDiffOn (n + 1)).continuousOn.mono
            (by intro L hL; change L0 ≤ L at hL; change 0 < L; exact hL0p.trans_le hL))
          (fun L hL => hasDerivAt_centralRightError_iteratedDeriv (hL0p.trans_le hL) n)
          (fun L hL => by have hh := hq L hL; linarith only [hh])
          (fun L hL => by
            rw [show -(2 + ((n + 1 : ℕ) : ℝ)) = -2 - ((n + 1 : ℕ) : ℝ) by ring]
            exact hb L hL)
        obtain ⟨C, hC, hCf⟩ := hd
        refine ⟨C, hC, ?_⟩
        intro L hL
        have hh := hCf L hL
        rw [show -(2 + ((n + 1 : ℕ) : ℝ)) - 1 = -3 - ((n + 1 : ℕ) : ℝ) by ring] at hh
        exact hh
  refine ⟨centralRightLogDerivativeError_contDiffOn, ?_⟩
  intro r
  obtain ⟨C, hC, hCr⟩ := hbound r
  obtain ⟨D, hD, hDr⟩ := extend_norm_power_bound_from_tail (L0 := 1) (L1 := L0)
    (s := -3 - (r : ℝ)) (by norm_num) hL01 hC
    ((centralRightError_iteratedDeriv_contDiffOn r).continuousOn.mono
      (by intro L hL; change 1 ≤ L at hL; change 0 < L; exact zero_lt_one.trans_le hL)) hCr
  exact ⟨D, hD, fun L hL _ => hDr L hL⟩

/-- Equation (sc6a), right side, with actual iterated derivatives and a
single numerical threshold for every finite order. -/
theorem centralRadiusLogDerivative_right_derivative_error (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℝ, 1 ≤ L →
      ‖iteratedDeriv r (fun x : ℝ => centralRadiusLogDerivative x -
        (centralRadiusA + x + (centralRadiusAlpha - 1) / x)) L‖ ≤
        C * L ^ (-3 - (r : ℝ)) := by
  obtain ⟨C, hC, hCr⟩ := centralRightLogDerivativeError_symbol.2 r
  refine ⟨C, hC, ?_⟩
  intro L hL
  have heq : (fun x : ℝ => centralRadiusLogDerivative x -
      (centralRadiusA + x + (centralRadiusAlpha - 1) / x)) = centralRightLogDerivativeError := by
    funext x
    unfold centralRightLogDerivativeError centralRightLogDerivativeModel
    ring
  rw [heq]
  exact hCr L hL (zero_lt_one.trans_le hL)

theorem centralRadiusLogDerivative_right_remainder_tendsto :
    Tendsto centralRightLogDerivativeError atTop (𝓝 0) := by
  obtain ⟨C, _, hC⟩ := centralRightLogDerivativeError_zero_bound
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun L => norm_nonneg _))
  · exact (eventually_ge_atTop (1 : ℝ)).mono (fun L hL => hC L hL)
  · simpa only [mul_zero] using
      (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3)).const_mul C

theorem centralRadiusLogDerivative_right_sub_tendsto :
    Tendsto (fun L : ℝ => centralRadiusLogDerivative L - L) atTop (𝓝 centralRadiusA) := by
  have hsmall : Tendsto (fun L : ℝ => (centralRadiusAlpha - 1) / L) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      tendsto_inv_atTop_zero.const_mul (centralRadiusAlpha - 1)
  have ht := centralRadiusLogDerivative_right_remainder_tendsto.add
    ((tendsto_const_nhds (x := centralRadiusA)).add hsmall)
  convert ht using 1
  · funext L
    unfold centralRightLogDerivativeError centralRightLogDerivativeModel
    ring
  · simp only [zero_add, add_zero]

theorem centralRadiusLogDerivative_right_ratio_tendsto :
    Tendsto (fun L : ℝ => centralRadiusLogDerivative L / L) atTop (𝓝 1) := by
  have ht := (tendsto_const_nhds (x := (1 : ℝ))).add
    (centralRadiusLogDerivative_right_sub_tendsto.mul tendsto_inv_atTop_zero)
  have hs : Tendsto (fun L : ℝ => 1 +
      (centralRadiusLogDerivative L - L) * L⁻¹) atTop (𝓝 (1 : ℝ)) := by
    simpa only [mul_zero, add_zero] using ht
  apply hs.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
  field_simp
  ring

private theorem radial_constant_symbol (L0 a : ℝ) :
    RadialSymbolBounds L0 0 (fun _ : ℝ => a) := by
  simpa only [rpow_zero, mul_one] using (radial_rpow_symbol L0 0).const_mul a

/-- The actual weight and all its derivatives have order one on the
same numerical right tail. -/
theorem centralRadiusLogDerivative_right_symbol :
    RadialSymbolBounds 1 1 centralRadiusLogDerivative := by
  have ha := radial_symbol_order_mono (by norm_num : (1 : ℝ) ≤ 1)
    (by norm_num : (0 : ℝ) ≤ 1) (radial_constant_symbol 1 centralRadiusA)
  have he := radial_symbol_order_mono (by norm_num : (1 : ℝ) ≤ 1)
    (by norm_num : (-3 : ℝ) ≤ 1) centralRightLogDerivativeError_symbol
  have hh := (ha.add (centralRightLogDerivativeModel_symbol (by norm_num : (1 : ℝ) ≤ 1))).add he
  convert hh using 1
  funext L
  simp only [Pi.add_apply, centralRightLogDerivativeError]
  ring

/-- A genuine linear lower bound for the same actual weight. Positivity
controls the finite gap before the already proved asymptotic tail. -/
theorem centralRadiusLogDerivative_right_linear_lower :
    ∃ c : ℝ, 0 < c ∧ ∀ L : ℝ, 1 ≤ L → c * L ≤ centralRadiusLogDerivative L := by
  have he : ∀ᶠ L : ℝ in atTop, (1 / 2 : ℝ) < centralRadiusLogDerivative L / L :=
    centralRadiusLogDerivative_right_ratio_tendsto.eventually
      (eventually_gt_nhds (by norm_num : (1 / 2 : ℝ) < 1))
  obtain ⟨N, hN⟩ := eventually_atTop.mp he
  let A : ℝ := max 1 N
  have hA : 0 < A := zero_lt_one.trans_le (le_max_left _ _)
  refine ⟨min (1 / 2) (centralRadiusA / A),
    lt_min (by norm_num) (div_pos centralRadiusA_pos hA), ?_⟩
  intro L hL
  have hLp : 0 < L := zero_lt_one.trans_le hL
  by_cases hAL : A ≤ L
  · have hh : (1 / 2 : ℝ) * L < centralRadiusLogDerivative L :=
      (lt_div_iff₀ hLp).mp (hN L ((le_max_right _ _).trans hAL))
    exact (mul_le_mul_of_nonneg_right (min_le_left _ _) hLp.le).trans hh.le
  · calc
      _ ≤ (centralRadiusA / A) * L :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) hLp.le
      _ ≤ (centralRadiusA / A) * A :=
        mul_le_mul_of_nonneg_left (lt_of_not_ge hAL).le (div_nonneg centralRadiusA_pos.le hA.le)
      _ = centralRadiusA := div_mul_cancel₀ _ hA.ne'
      _ ≤ _ := (centralRadiusLogDerivative_gt L).le

theorem centralRadiusLogDerivative_right_inverse_symbol :
    RadialSymbolBounds 1 (-1) (fun L : ℝ => (centralRadiusLogDerivative L)⁻¹) := by
  obtain ⟨c, hc, hlower⟩ := centralRadiusLogDerivative_right_linear_lower
  have hh := centralRadiusLogDerivative_right_symbol.inv
    (fun L => (centralRadiusLogDerivative_pos L).ne') hc
    (fun L hL _ => by simpa only [rpow_one] using hlower L hL)
  exact hh

/-- This is the real quotient later identified with the height's
logarithmic-coordinate derivative. Its actual derivatives are bounded. -/
theorem centralRightHeightSlope_symbol :
    RadialSymbolBounds 1 0
      (fun L : ℝ => (centralRadiusA - 2 * L) / centralRadiusLogDerivative L) := by
  have ha := radial_symbol_order_mono (by norm_num : (1 : ℝ) ≤ 1)
    (by norm_num : (0 : ℝ) ≤ 1) (radial_constant_symbol 1 centralRadiusA)
  have hn := ha.sub ((radial_rpow_symbol 1 1).const_mul 2)
  have hh := hn.mul centralRadiusLogDerivative_right_inverse_symbol
  have hh' : RadialSymbolBounds 1 0
      (((fun _ : ℝ => centralRadiusA) - (fun L : ℝ => 2 * L ^ (1 : ℝ))) *
        (fun L : ℝ => (centralRadiusLogDerivative L)⁻¹)) := by
    simpa only [show (1 : ℝ) + -1 = 0 by norm_num] using hh
  convert hh' using 1
  funext L
  change (centralRadiusA - 2 * L) / centralRadiusLogDerivative L =
    (centralRadiusA - 2 * L ^ (1 : ℝ)) * (centralRadiusLogDerivative L)⁻¹
  rw [rpow_one, div_eq_mul_inv]

/-- The actual profile slope quotient has uniformly bounded fixed-order
derivatives, with the same threshold as the height slope. -/
theorem centralRightProfileSlope_symbol :
    RadialSymbolBounds 1 0
      (fun L : ℝ => (L ^ 2 - centralOscillatorA) / centralRadiusLogDerivative L ^ 2) := by
  have hA := radial_symbol_order_mono (by norm_num : (1 : ℝ) ≤ 1)
    (by norm_num : (0 : ℝ) ≤ 2) (radial_constant_symbol 1 centralOscillatorA)
  have hn := (radial_rpow_symbol 1 2).sub hA
  have hi := centralRadiusLogDerivative_right_inverse_symbol.mul
    centralRadiusLogDerivative_right_inverse_symbol
  have hh := hn.mul hi
  have hh' : RadialSymbolBounds 1 0
      (((fun L : ℝ => L ^ (2 : ℝ)) - (fun _ : ℝ => centralOscillatorA)) *
        ((fun L : ℝ => (centralRadiusLogDerivative L)⁻¹) *
          (fun L : ℝ => (centralRadiusLogDerivative L)⁻¹))) := by
    simpa only [show (2 : ℝ) + (-1 + -1) = 0 by norm_num] using hh
  convert hh' using 1
  funext L
  change (L ^ 2 - centralOscillatorA) / centralRadiusLogDerivative L ^ 2 =
    (L ^ (2 : ℝ) - centralOscillatorA) *
      ((centralRadiusLogDerivative L)⁻¹ * (centralRadiusLogDerivative L)⁻¹)
  rw [rpow_two, div_eq_mul_inv]
  rw [show (centralRadiusLogDerivative L ^ 2)⁻¹ =
    (centralRadiusLogDerivative L)⁻¹ * (centralRadiusLogDerivative L)⁻¹ by rw [← inv_pow, pow_two]]

theorem centralRightHeightSlope_tendsto :
    Tendsto (fun L : ℝ => (centralRadiusA - 2 * L) / centralRadiusLogDerivative L)
      atTop (𝓝 (-2)) := by
  have hnum : Tendsto (fun L : ℝ => centralRadiusA / L - 2) atTop (𝓝 (-2)) := by
    simpa only [div_eq_mul_inv, mul_zero, zero_sub] using
      (tendsto_inv_atTop_zero.const_mul centralRadiusA).sub_const 2
  have ht := hnum.div centralRadiusLogDerivative_right_ratio_tendsto
    (by norm_num : (1 : ℝ) ≠ 0)
  change Tendsto (fun L : ℝ => (centralRadiusA / L - 2) /
    (centralRadiusLogDerivative L / L)) atTop (𝓝 ((-2 : ℝ) / 1)) at ht
  have hs : Tendsto (fun L : ℝ => (centralRadiusA / L - 2) /
      (centralRadiusLogDerivative L / L)) atTop (𝓝 (-2)) := by
    simpa only [div_one] using ht
  apply hs.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
  field_simp [hL.ne', (centralRadiusLogDerivative_pos L).ne']

theorem centralRightProfileSlope_tendsto :
    Tendsto (fun L : ℝ => (L ^ 2 - centralOscillatorA) / centralRadiusLogDerivative L ^ 2)
      atTop (𝓝 1) := by
  have hnum : Tendsto (fun L : ℝ => 1 - centralOscillatorA * (L⁻¹) ^ 2) atTop (𝓝 1) := by
    simpa only [zero_pow (by decide : 2 ≠ 0), mul_zero, sub_zero] using
      (tendsto_const_nhds (x := (1 : ℝ))).sub
        ((tendsto_inv_atTop_zero.pow 2).const_mul centralOscillatorA)
  have ht := hnum.div (centralRadiusLogDerivative_right_ratio_tendsto.pow 2)
    (by norm_num : (1 : ℝ) ^ 2 ≠ 0)
  change Tendsto (fun L : ℝ => (1 - centralOscillatorA * (L⁻¹) ^ 2) /
    (centralRadiusLogDerivative L / L) ^ 2) atTop (𝓝 (1 / 1 ^ 2 : ℝ)) at ht
  have hs : Tendsto (fun L : ℝ => (1 - centralOscillatorA * (L⁻¹) ^ 2) /
      (centralRadiusLogDerivative L / L) ^ 2) atTop (𝓝 1) := by
    simpa only [one_pow, div_one] using ht
  apply hs.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
  field_simp [hL.ne', (centralRadiusLogDerivative_pos L).ne']

end ContinuousFlexibility.Radial
