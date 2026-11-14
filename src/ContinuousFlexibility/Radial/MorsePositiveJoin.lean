module

public import ContinuousFlexibility.Radial.MorseRadiusODE

/-!
# A smooth positive connector with prescribed endpoint germs

The two one-sided weights are scaled smooth transitions. The intervening
constant is determined by the actual integral of the remaining weight.
Integrating this slope gives the logarithmic height and matches both
endpoint functions on neighborhoods.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

def morseJoinLeftWeight (a h x : ℝ) : ℝ :=
  smoothTransition (2 - 2 * ((x - a) / h))

def morseJoinRightWeight (b h x : ℝ) : ℝ :=
  smoothTransition (2 + 2 * ((x - b) / h))

theorem contDiff_morseJoinLeftWeight (a h : ℝ) :
    ContDiff ℝ ∞ (morseJoinLeftWeight a h) := by
  have harg : ContDiff ℝ ∞ (fun x : ℝ => 2 - 2 * ((x - a) / h)) :=
    contDiff_const.sub (contDiff_const.mul ((contDiff_id.sub contDiff_const).div_const h))
  exact smoothTransition.contDiff.comp harg

theorem contDiff_morseJoinRightWeight (b h : ℝ) :
    ContDiff ℝ ∞ (morseJoinRightWeight b h) := by
  have harg : ContDiff ℝ ∞ (fun x : ℝ => 2 + 2 * ((x - b) / h)) :=
    contDiff_const.add (contDiff_const.mul ((contDiff_id.sub contDiff_const).div_const h))
  exact smoothTransition.contDiff.comp harg

theorem morseJoinLeftWeight_one {a h x : ℝ} (hh : 0 < h) (hx : x ≤ a + h / 2) :
    morseJoinLeftWeight a h x = 1 := by
  unfold morseJoinLeftWeight
  apply smoothTransition.one_of_one_le
  have hq : (x - a) / h ≤ (1 / 2 : ℝ) := (div_le_iff₀ hh).mpr (by linarith only [hx])
  linarith only [hq]

theorem morseJoinLeftWeight_zero {a h x : ℝ} (hh : 0 < h) (hx : a + h ≤ x) :
    morseJoinLeftWeight a h x = 0 := by
  unfold morseJoinLeftWeight
  apply smoothTransition.zero_of_nonpos
  have hq : 1 ≤ (x - a) / h := (le_div_iff₀ hh).mpr (by linarith only [hx])
  linarith only [hq]

theorem morseJoinRightWeight_one {b h x : ℝ} (hh : 0 < h) (hx : b - h / 2 ≤ x) :
    morseJoinRightWeight b h x = 1 := by
  unfold morseJoinRightWeight
  apply smoothTransition.one_of_one_le
  have hq : (-1 / 2 : ℝ) ≤ (x - b) / h := (le_div_iff₀ hh).mpr (by linarith only [hx])
  linarith only [hq]

theorem morseJoinRightWeight_zero {b h x : ℝ} (hh : 0 < h) (hx : x ≤ b - h) :
    morseJoinRightWeight b h x = 0 := by
  unfold morseJoinRightWeight
  apply smoothTransition.zero_of_nonpos
  have hq : (x - b) / h ≤ -1 := (div_le_iff₀ hh).mpr (by linarith only [hx])
  linarith only [hq]

theorem morseJoin_weights_disjoint {a b hL hR : ℝ} (hhL : 0 < hL) (hhR : 0 < hR)
    (hsep : a + hL ≤ b - hR) (x : ℝ) :
    morseJoinLeftWeight a hL x = 0 ∨ morseJoinRightWeight b hR x = 0 := by
  by_cases hx : x ≤ b - hR
  · exact Or.inr (morseJoinRightWeight_zero hhR hx)
  · exact Or.inl (morseJoinLeftWeight_zero hhL (hsep.trans (le_of_lt (lt_of_not_ge hx))))

def morseJoinRemainder (a b hL hR x : ℝ) : ℝ :=
  1 - morseJoinLeftWeight a hL x - morseJoinRightWeight b hR x

def morseJoinDenominator (a b hL hR : ℝ) : ℝ :=
  ∫ x in a..b, morseJoinRemainder a b hL hR x

def morseJoinLeftSlope (a hL : ℝ) (fL : ℝ → ℝ) (x : ℝ) : ℝ :=
  morseJoinLeftWeight a hL x * deriv fL x

def morseJoinRightSlope (b hR : ℝ) (fR : ℝ → ℝ) (x : ℝ) : ℝ :=
  morseJoinRightWeight b hR x * deriv fR x

def morseJoinConstant (a b hL hR : ℝ) (fL fR : ℝ → ℝ) : ℝ :=
  (fR b - fL a - (∫ x in a..b, morseJoinLeftSlope a hL fL x) -
    (∫ x in a..b, morseJoinRightSlope b hR fR x)) / morseJoinDenominator a b hL hR

def morseJoinSlope (a b hL hR : ℝ) (fL fR : ℝ → ℝ) (x : ℝ) : ℝ :=
  morseJoinLeftSlope a hL fL x + morseJoinRightSlope b hR fR x +
    morseJoinConstant a b hL hR fL fR * morseJoinRemainder a b hL hR x

def morseJoinLog (a b hL hR : ℝ) (fL fR : ℝ → ℝ) (x : ℝ) : ℝ :=
  fL a + ∫ t in a..x, morseJoinSlope a b hL hR fL fR t

def morseJoinProfile (a b hL hR : ℝ) (fL fR : ℝ → ℝ) (x : ℝ) : ℝ :=
  exp (morseJoinLog a b hL hR fL fR x)

private theorem contDiff_morseJoinRemainder (a b hL hR : ℝ) :
    ContDiff ℝ ∞ (morseJoinRemainder a b hL hR) :=
  (contDiff_const.sub (contDiff_morseJoinLeftWeight a hL)).sub
    (contDiff_morseJoinRightWeight b hR)

private theorem morseJoinRemainder_bounds {a b hL hR : ℝ} (hhL : 0 < hL) (hhR : 0 < hR)
    (hsep : a + hL ≤ b - hR) (x : ℝ) :
    0 ≤ morseJoinRemainder a b hL hR x ∧ morseJoinRemainder a b hL hR x ≤ 1 := by
  have hL₀ : 0 ≤ morseJoinLeftWeight a hL x := smoothTransition.nonneg _
  have hL₁ : morseJoinLeftWeight a hL x ≤ 1 := smoothTransition.le_one _
  have hR₀ : 0 ≤ morseJoinRightWeight b hR x := smoothTransition.nonneg _
  have hR₁ : morseJoinRightWeight b hR x ≤ 1 := smoothTransition.le_one _
  unfold morseJoinRemainder
  constructor
  · rcases morseJoin_weights_disjoint hhL hhR hsep x with h | h
    · linarith only [h, hR₁]
    · linarith only [h, hL₁]
  · linarith only [hL₀, hR₀]

theorem morseJoinDenominator_bounds {a b hL hR : ℝ} (hhL : 0 < hL) (hhR : 0 < hR)
    (hsep : a + hL ≤ b - hR) :
    b - hR - (a + hL) ≤ morseJoinDenominator a b hL hR ∧
      morseJoinDenominator a b hL hR ≤ b - a := by
  let g := morseJoinRemainder a b hL hR
  have hg : Continuous g := (contDiff_morseJoinRemainder a b hL hR).continuous
  have ha : a ≤ a + hL := le_add_of_nonneg_right hhL.le
  have hb : b - hR ≤ b := sub_le_self _ hhR.le
  have hab : a ≤ b := ha.trans (hsep.trans hb)
  have hmid : (∫ x in a + hL..b - hR, g x) = b - hR - (a + hL) := by
    calc
      _ = ∫ _ in a + hL..b - hR, (1 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le hsep] at hx
        change morseJoinRemainder a b hL hR x = 1
        simp only [morseJoinRemainder, morseJoinLeftWeight_zero hhL hx.1,
          morseJoinRightWeight_zero hhR hx.2, sub_zero]
      _ = _ := by rw [intervalIntegral.integral_const, smul_eq_mul, mul_one]
  change b - hR - (a + hL) ≤ (∫ x in a..b, g x) ∧ (∫ x in a..b, g x) ≤ b - a
  refine ⟨?_, ?_⟩
  · rw [← hmid]
    exact intervalIntegral.integral_mono_interval (μ := volume) ha hsep hb
      (ae_of_all _ fun x => (morseJoinRemainder_bounds hhL hhR hsep x).1)
      (hg.intervalIntegrable a b)
  · calc
      _ ≤ ∫ _ in a..b, (1 : ℝ) :=
        intervalIntegral.integral_mono_on hab (hg.intervalIntegrable a b)
          ((continuous_const : Continuous (fun _ : ℝ => (1 : ℝ))).intervalIntegrable a b)
          (fun x _ => (morseJoinRemainder_bounds hhL hhR hsep x).2)
      _ = _ := by rw [intervalIntegral.integral_const, smul_eq_mul, mul_one]

theorem morseJoinDenominator_pos {a b hL hR : ℝ} (hhL : 0 < hL) (hhR : 0 < hR)
    (hsep : a + hL < b - hR) : 0 < morseJoinDenominator a b hL hR :=
  (sub_pos.mpr hsep).trans_le (morseJoinDenominator_bounds hhL hhR hsep.le).1

private theorem contDiff_morseJoinLeftSlope {a hL : ℝ} {fL : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ fL) : ContDiff ℝ ∞ (morseJoinLeftSlope a hL fL) :=
  (contDiff_morseJoinLeftWeight a hL).mul (contDiff_infty_iff_deriv.mp hf).2

private theorem contDiff_morseJoinRightSlope {b hR : ℝ} {fR : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ fR) : ContDiff ℝ ∞ (morseJoinRightSlope b hR fR) :=
  (contDiff_morseJoinRightWeight b hR).mul (contDiff_infty_iff_deriv.mp hf).2

theorem contDiff_morseJoinSlope {a b hL hR : ℝ} {fL fR : ℝ → ℝ}
    (hfL : ContDiff ℝ ∞ fL) (hfR : ContDiff ℝ ∞ fR) :
    ContDiff ℝ ∞ (morseJoinSlope a b hL hR fL fR) :=
  ((contDiff_morseJoinLeftSlope hfL).add (contDiff_morseJoinRightSlope hfR)).add
    (contDiff_const.mul (contDiff_morseJoinRemainder a b hL hR))

theorem hasDerivAt_morseJoinLog {a b hL hR : ℝ} {fL fR : ℝ → ℝ}
    (hfL : ContDiff ℝ ∞ fL) (hfR : ContDiff ℝ ∞ fR) (x : ℝ) :
    HasDerivAt (morseJoinLog a b hL hR fL fR) (morseJoinSlope a b hL hR fL fR x) x := by
  have hc := (contDiff_morseJoinSlope (a := a) (b := b) (hL := hL) (hR := hR) hfL hfR).continuous
  exact (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable a x)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).const_add (fL a)

theorem contDiff_morseJoinLog {a b hL hR : ℝ} {fL fR : ℝ → ℝ}
    (hfL : ContDiff ℝ ∞ fL) (hfR : ContDiff ℝ ∞ fR) :
    ContDiff ℝ ∞ (morseJoinLog a b hL hR fL fR) := by
  have hd (x : ℝ) : HasDerivAt (morseJoinLog a b hL hR fL fR)
      (morseJoinSlope a b hL hR fL fR x) x := hasDerivAt_morseJoinLog hfL hfR x
  refine contDiff_infty_iff_deriv.mpr ⟨fun x => (hd x).differentiableAt, ?_⟩
  rw [show deriv (morseJoinLog a b hL hR fL fR) = morseJoinSlope a b hL hR fL fR from
    funext fun x => (hd x).deriv]
  exact contDiff_morseJoinSlope hfL hfR

private theorem morseJoinSlope_eq_left {a b hL hR x : ℝ} {fL fR : ℝ → ℝ}
    (hhL : 0 < hL) (hhR : 0 < hR) (hsep : a + hL ≤ b - hR) (hx : x ≤ a + hL / 2) :
    morseJoinSlope a b hL hR fL fR x = deriv fL x := by
  have hL := morseJoinLeftWeight_one hhL hx
  have hR := morseJoinRightWeight_zero hhR (show x ≤ b - hR by linarith only [hx, hsep, hhL])
  simp [morseJoinSlope, morseJoinLeftSlope, morseJoinRightSlope, morseJoinRemainder, hL, hR]

private theorem morseJoinSlope_eq_right {a b hL hR x : ℝ} {fL fR : ℝ → ℝ}
    (hhL : 0 < hL) (hhR : 0 < hR) (hsep : a + hL ≤ b - hR) (hx : b - hR / 2 ≤ x) :
    morseJoinSlope a b hL hR fL fR x = deriv fR x := by
  have hL := morseJoinLeftWeight_zero hhL (show a + hL ≤ x by linarith only [hx, hsep, hhR])
  have hR := morseJoinRightWeight_one hhR hx
  simp [morseJoinSlope, morseJoinLeftSlope, morseJoinRightSlope, morseJoinRemainder, hL, hR]

theorem morseJoinLog_right_value {a b hL hR : ℝ} {fL fR : ℝ → ℝ}
    (hhL : 0 < hL) (hhR : 0 < hR) (hsep : a + hL < b - hR)
    (hfL : ContDiff ℝ ∞ fL) (hfR : ContDiff ℝ ∞ fR) :
    morseJoinLog a b hL hR fL fR b = fR b := by
  let l := morseJoinLeftSlope a hL fL
  let r := morseJoinRightSlope b hR fR
  let q := morseJoinRemainder a b hL hR
  let C := morseJoinConstant a b hL hR fL fR
  have hl : Continuous l := (contDiff_morseJoinLeftSlope hfL).continuous
  have hr : Continuous r := (contDiff_morseJoinRightSlope hfR).continuous
  have hq : Continuous q := (contDiff_morseJoinRemainder a b hL hR).continuous
  have hil : IntervalIntegrable l volume a b := hl.intervalIntegrable a b
  have hir : IntervalIntegrable r volume a b := hr.intervalIntegrable a b
  have hilr : IntervalIntegrable (fun x => l x + r x) volume a b := (hl.add hr).intervalIntegrable a b
  have hicq : IntervalIntegrable (fun x => C * q x) volume a b :=
    (continuous_const.mul hq).intervalIntegrable a b
  have hInt : (∫ x in a..b, morseJoinSlope a b hL hR fL fR x) =
      (∫ x in a..b, l x) + (∫ x in a..b, r x) + C * (∫ x in a..b, q x) := by
    change (∫ x in a..b, (l x + r x) + C * q x) = _
    rw [intervalIntegral.integral_add hilr hicq, intervalIntegral.integral_add hil hir,
      intervalIntegral.integral_const_mul]
  have hC : C * (∫ x in a..b, q x) =
      fR b - fL a - (∫ x in a..b, l x) - (∫ x in a..b, r x) :=
    div_mul_cancel₀ _ (morseJoinDenominator_pos hhL hhR hsep).ne'
  change fL a + (∫ x in a..b, morseJoinSlope a b hL hR fL fR x) = fR b
  rw [hInt, hC]
  ring

/-- The primitive agrees with the original left function on the
whole ray where the left weight is one. -/
theorem morseJoinLog_eqOn_left {a b hL hR : ℝ} {fL fR : ℝ → ℝ}
    (hhL : 0 < hL) (hhR : 0 < hR) (hsep : a + hL ≤ b - hR)
    (hfL : ContDiff ℝ ∞ fL) :
    EqOn (morseJoinLog a b hL hR fL fR) fL (Iic (a + hL / 2)) := by
  intro x hx
  have ha : a ≤ a + hL / 2 := by linarith only [hhL]
  have hsub : uIcc a x ⊆ Iic (a + hL / 2) := by
    intro y hy
    exact hy.2.trans (sup_le ha hx)
  have he : (∫ y in a..x, morseJoinSlope a b hL hR fL fR y) =
      ∫ y in a..x, deriv fL y := by
    apply intervalIntegral.integral_congr
    intro y hy
    exact morseJoinSlope_eq_left hhL hhR hsep (hsub hy)
  have hFTC : (∫ y in a..x, deriv fL y) = fL x - fL a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun y _ => (hfL.differentiable (by simp) y).hasDerivAt)
      ((contDiff_infty_iff_deriv.mp hfL).2.continuous.intervalIntegrable a x)
  change fL a + (∫ y in a..x, morseJoinSlope a b hL hR fL fR y) = fL x
  rw [he, hFTC]
  ring

/-- The chosen constant makes the right endpoint value agree, so the
primitive agrees with the original right function on its ray as well. -/
theorem morseJoinLog_eqOn_right {a b hL hR : ℝ} {fL fR : ℝ → ℝ}
    (hhL : 0 < hL) (hhR : 0 < hR) (hsep : a + hL < b - hR)
    (hfL : ContDiff ℝ ∞ fL) (hfR : ContDiff ℝ ∞ fR) :
    EqOn (morseJoinLog a b hL hR fL fR) fR (Ici (b - hR / 2)) := by
  intro x hx
  let g := morseJoinSlope a b hL hR fL fR
  have hg : Continuous g := (contDiff_morseJoinSlope hfL hfR).continuous
  have hb : b - hR / 2 ≤ b := by linarith only [hhR]
  have hsub : uIcc b x ⊆ Ici (b - hR / 2) := by
    intro y hy
    exact (le_inf hb hx).trans hy.1
  have he : (∫ y in b..x, g y) = ∫ y in b..x, deriv fR y := by
    apply intervalIntegral.integral_congr
    intro y hy
    exact morseJoinSlope_eq_right hhL hhR hsep.le (hsub hy)
  have hFTC : (∫ y in b..x, deriv fR y) = fR x - fR b :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun y _ => (hfR.differentiable (by simp) y).hasDerivAt)
      ((contDiff_infty_iff_deriv.mp hfR).2.continuous.intervalIntegrable b x)
  have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hg.intervalIntegrable a b) (hg.intervalIntegrable b x)
  calc
    morseJoinLog a b hL hR fL fR x =
        morseJoinLog a b hL hR fL fR b + (∫ y in b..x, g y) := by
      change fL a + (∫ y in a..x, g y) = (fL a + (∫ y in a..b, g y)) + (∫ y in b..x, g y)
      rw [← hadd]
      ring
    _ = _ := by rw [morseJoinLog_right_value hhL hhR hsep hfL hfR, he, hFTC]; ring

theorem morseJoinLog_endpoint_germs {a b hL hR : ℝ} {fL fR : ℝ → ℝ}
    (hhL : 0 < hL) (hhR : 0 < hR) (hsep : a + hL < b - hR)
    (hfL : ContDiff ℝ ∞ fL) (hfR : ContDiff ℝ ∞ fR) :
    (morseJoinLog a b hL hR fL fR =ᶠ[𝓝 a] fL) ∧
      (morseJoinLog a b hL hR fL fR =ᶠ[𝓝 b] fR) := by
  constructor
  · filter_upwards [Iic_mem_nhds (show a < a + hL / 2 by linarith only [hhL])] with x hx
    exact morseJoinLog_eqOn_left hhL hhR hsep.le hfL hx
  · filter_upwards [Ici_mem_nhds (show b - hR / 2 < b by linarith only [hhR])] with x hx
    exact morseJoinLog_eqOn_right hhL hhR hsep hfL hfR hx

theorem morseJoinProfile_endpoint_germs {a b hL hR : ℝ} {fL fR : ℝ → ℝ}
    (hhL : 0 < hL) (hhR : 0 < hR) (hsep : a + hL < b - hR)
    (hfL : ContDiff ℝ ∞ fL) (hfR : ContDiff ℝ ∞ fR) :
    (morseJoinProfile a b hL hR fL fR =ᶠ[𝓝 a] fun x => exp (fL x)) ∧
      (morseJoinProfile a b hL hR fL fR =ᶠ[𝓝 b] fun x => exp (fR x)) := by
  obtain ⟨hleft, hright⟩ := morseJoinLog_endpoint_germs hhL hhR hsep hfL hfR
  exact ⟨hleft.fun_comp exp, hright.fun_comp exp⟩

theorem morseJoinLog_deriv_middle {a b hL hR x : ℝ} {fL fR : ℝ → ℝ}
    (hhL : 0 < hL) (hhR : 0 < hR) (hfL : ContDiff ℝ ∞ fL) (hfR : ContDiff ℝ ∞ fR)
    (hx : x ∈ Icc (a + hL) (b - hR)) :
    deriv (morseJoinLog a b hL hR fL fR) x = morseJoinConstant a b hL hR fL fR := by
  rw [(hasDerivAt_morseJoinLog hfL hfR x).deriv]
  simp [morseJoinSlope, morseJoinLeftSlope, morseJoinRightSlope, morseJoinRemainder,
    morseJoinLeftWeight_zero hhL hx.1, morseJoinRightWeight_zero hhR hx.2]

/-- The log-height budget for a constant lower slope on the connector. -/
def MorseJoinBudget (a b hL hR m : ℝ) (fL fR : ℝ → ℝ) : Prop :=
  (∫ x in a..b, morseJoinLeftSlope a hL fL x) +
    (∫ x in a..b, morseJoinRightSlope b hR fR x) +
    m * morseJoinDenominator a b hL hR ≤ fR b - fL a

theorem morseJoinConstant_ge {a b hL hR m : ℝ} {fL fR : ℝ → ℝ}
    (hhL : 0 < hL) (hhR : 0 < hR) (hsep : a + hL < b - hR)
    (hbudget : MorseJoinBudget a b hL hR m fL fR) :
    m ≤ morseJoinConstant a b hL hR fL fR := by
  unfold MorseJoinBudget at hbudget
  unfold morseJoinConstant
  exact (le_div_iff₀ (morseJoinDenominator_pos hhL hhR hsep)).mpr (by linarith only [hbudget])

/-- A convex combination of the two endpoint slopes and the chosen
constant preserves the lower slope on the entire connector. -/
theorem morseJoinLog_deriv_ge {a b hL hR m : ℝ} {fL fR : ℝ → ℝ}
    (hhL : 0 < hL) (hhR : 0 < hR) (hsep : a + hL < b - hR)
    (hfL : ContDiff ℝ ∞ fL) (hfR : ContDiff ℝ ∞ fR)
    (hleftSlope : ∀ x ∈ Icc a (a + hL), m ≤ deriv fL x)
    (hrightSlope : ∀ x ∈ Icc (b - hR) b, m ≤ deriv fR x)
    (hbudget : MorseJoinBudget a b hL hR m fL fR) :
    ∀ x ∈ Icc a b, m ≤ deriv (morseJoinLog a b hL hR fL fR) x := by
  have hC := morseJoinConstant_ge hhL hhR hsep hbudget
  intro x hx
  rw [(hasDerivAt_morseJoinLog hfL hfR x).deriv]
  have hleft : morseJoinLeftWeight a hL x * m ≤ morseJoinLeftSlope a hL fL x := by
    by_cases hx' : x ≤ a + hL
    · exact mul_le_mul_of_nonneg_left (hleftSlope x ⟨hx.1, hx'⟩) (smoothTransition.nonneg _)
    · simp [morseJoinLeftSlope, morseJoinLeftWeight_zero hhL (le_of_lt (lt_of_not_ge hx'))]
  have hright : morseJoinRightWeight b hR x * m ≤ morseJoinRightSlope b hR fR x := by
    by_cases hx' : b - hR ≤ x
    · exact mul_le_mul_of_nonneg_left (hrightSlope x ⟨hx', hx.2⟩) (smoothTransition.nonneg _)
    · simp [morseJoinRightSlope, morseJoinRightWeight_zero hhR (le_of_lt (lt_of_not_ge hx'))]
  have hmiddle : m * morseJoinRemainder a b hL hR x ≤
      morseJoinConstant a b hL hR fL fR * morseJoinRemainder a b hL hR x :=
    mul_le_mul_of_nonneg_right hC (morseJoinRemainder_bounds hhL hhR hsep.le x).1
  calc
    m = morseJoinLeftWeight a hL x * m + morseJoinRightWeight b hR x * m +
        m * morseJoinRemainder a b hL hR x := by unfold morseJoinRemainder; ring
    _ ≤ _ := add_le_add (add_le_add hleft hright) hmiddle

theorem morseJoinProfile_deriv {a b hL hR : ℝ} {fL fR : ℝ → ℝ}
    (hfL : ContDiff ℝ ∞ fL) (hfR : ContDiff ℝ ∞ fR) (x : ℝ) :
    deriv (morseJoinProfile a b hL hR fL fR) x =
      morseJoinProfile a b hL hR fL fR x * deriv (morseJoinLog a b hL hR fL fR) x := by
  have h : HasDerivAt (morseJoinLog a b hL hR fL fR) (morseJoinSlope a b hL hR fL fR x) x :=
    hasDerivAt_morseJoinLog hfL hfR x
  rw [h.deriv]
  exact h.exp.deriv

theorem morseJoinProfile_positive_mono {a b hL hR m : ℝ} {fL fR : ℝ → ℝ}
    (hhL : 0 < hL) (hhR : 0 < hR) (hsep : a + hL < b - hR)
    (hfL : ContDiff ℝ ∞ fL) (hfR : ContDiff ℝ ∞ fR) (hm : 0 ≤ m)
    (hleftSlope : ∀ x ∈ Icc a (a + hL), m ≤ deriv fL x)
    (hrightSlope : ∀ x ∈ Icc (b - hR) b, m ≤ deriv fR x)
    (hbudget : MorseJoinBudget a b hL hR m fL fR) :
    let w := morseJoinProfile a b hL hR fL fR
    ContDiff ℝ ∞ w ∧ (∀ x, 0 < w x) ∧
      (∀ x ∈ Icc a b, m * w x ≤ deriv w x) ∧ MonotoneOn w (Icc a b) ∧
      (0 < m → StrictMonoOn w (Icc a b)) := by
  dsimp only
  let w := morseJoinProfile a b hL hR fL fR
  have hws : ContDiff ℝ ∞ w := (contDiff_morseJoinLog hfL hfR).exp
  have hpos (x : ℝ) : 0 < w x := exp_pos _
  have hlower := morseJoinLog_deriv_ge hhL hhR hsep hfL hfR hleftSlope hrightSlope hbudget
  have hwd (x : ℝ) (hx : x ∈ Icc a b) : m * w x ≤ deriv w x := calc
    _ = w x * m := mul_comm _ _
    _ ≤ w x * deriv (morseJoinLog a b hL hR fL fR) x :=
      mul_le_mul_of_nonneg_left (hlower x hx) (hpos x).le
    _ = _ := (morseJoinProfile_deriv hfL hfR x).symm
  refine ⟨hws, hpos, hwd, ?_, ?_⟩
  · exact monotoneOn_of_deriv_nonneg (convex_Icc a b) hws.continuous.continuousOn
      (hws.differentiable (by simp)).differentiableOn
      (fun x hx => (mul_nonneg hm (hpos x).le).trans (hwd x (interior_subset hx)))
  · intro hm'
    exact strictMonoOn_of_deriv_pos (convex_Icc a b) hws.continuous.continuousOn
      (fun x hx => (mul_pos hm' (hpos x)).trans_le (hwd x (interior_subset hx)))

/-- A sufficient budget using only the upper slope bounds on the two
supported collars. -/
theorem morseJoinBudget_of_upper_slopes {a b hL hR m KL KR : ℝ} {fL fR : ℝ → ℝ}
    (hhL : 0 < hL) (hhR : 0 < hR) (hsep : a + hL < b - hR)
    (hfL : ContDiff ℝ ∞ fL) (hfR : ContDiff ℝ ∞ fR) (hm : 0 ≤ m)
    (hKL : 0 ≤ KL) (hKR : 0 ≤ KR)
    (hleftSlope : ∀ x ∈ Icc a (a + hL), deriv fL x ≤ KL)
    (hrightSlope : ∀ x ∈ Icc (b - hR) b, deriv fR x ≤ KR)
    (hgap : (KL + KR + m) * (b - a) ≤ fR b - fL a) :
    MorseJoinBudget a b hL hR m fL fR := by
  have hab : a ≤ b := by linarith only [hhL, hhR, hsep]
  have hleft (x : ℝ) (hx : x ∈ Icc a b) : morseJoinLeftSlope a hL fL x ≤ KL := by
    by_cases hx' : x ≤ a + hL
    · calc
        _ ≤ morseJoinLeftWeight a hL x * KL :=
          mul_le_mul_of_nonneg_left (hleftSlope x ⟨hx.1, hx'⟩) (smoothTransition.nonneg _)
        _ ≤ 1 * KL := mul_le_mul_of_nonneg_right (smoothTransition.le_one _) hKL
        _ = KL := one_mul _
    · simpa only [morseJoinLeftSlope, morseJoinLeftWeight_zero hhL (le_of_lt (lt_of_not_ge hx')),
        zero_mul] using hKL
  have hright (x : ℝ) (hx : x ∈ Icc a b) : morseJoinRightSlope b hR fR x ≤ KR := by
    by_cases hx' : b - hR ≤ x
    · calc
        _ ≤ morseJoinRightWeight b hR x * KR :=
          mul_le_mul_of_nonneg_left (hrightSlope x ⟨hx', hx.2⟩) (smoothTransition.nonneg _)
        _ ≤ 1 * KR := mul_le_mul_of_nonneg_right (smoothTransition.le_one _) hKR
        _ = KR := one_mul _
    · simpa only [morseJoinRightSlope, morseJoinRightWeight_zero hhR (le_of_lt (lt_of_not_ge hx')),
        zero_mul] using hKR
  have hli : (∫ x in a..b, morseJoinLeftSlope a hL fL x) ≤ ∫ _ in a..b, KL :=
    intervalIntegral.integral_mono_on hab
      ((contDiff_morseJoinLeftSlope hfL).continuous.intervalIntegrable a b)
      ((continuous_const : Continuous (fun _ : ℝ => KL)).intervalIntegrable a b) hleft
  have hri : (∫ x in a..b, morseJoinRightSlope b hR fR x) ≤ ∫ _ in a..b, KR :=
    intervalIntegral.integral_mono_on hab
      ((contDiff_morseJoinRightSlope hfR).continuous.intervalIntegrable a b)
      ((continuous_const : Continuous (fun _ : ℝ => KR)).intervalIntegrable a b) hright
  rw [intervalIntegral.integral_const, smul_eq_mul] at hli hri
  unfold MorseJoinBudget
  calc
    _ ≤ (b - a) * KL + (b - a) * KR + m * (b - a) :=
      add_le_add (add_le_add hli hri)
        (mul_le_mul_of_nonneg_left (morseJoinDenominator_bounds hhL hhR hsep.le).2 hm)
    _ = (KL + KR + m) * (b - a) := by ring
    _ ≤ _ := hgap

private theorem hasCompactSupport_deriv_joinTransition : HasCompactSupport (deriv smoothTransition) := by
  have hs : Function.support (deriv smoothTransition) ⊆ Icc (0 : ℝ) 1 := by
    intro x hx
    by_contra hn
    change deriv smoothTransition x ≠ 0 at hx
    by_cases h₀ : x < 0
    · have he : smoothTransition =ᶠ[𝓝 x] (fun _ : ℝ => (0 : ℝ)) := by
        filter_upwards [Iio_mem_nhds h₀] with y hy
        exact smoothTransition.zero_of_nonpos hy.le
      exact hx (by simpa only [deriv_const] using he.deriv_eq)
    · have h₁ : 1 < x := lt_of_not_ge (fun h => hn ⟨le_of_not_gt h₀, h⟩)
      have he : smoothTransition =ᶠ[𝓝 x] (fun _ : ℝ => (1 : ℝ)) := by
        filter_upwards [Ioi_mem_nhds h₁] with y hy
        exact smoothTransition.one_of_one_le hy.le
      exact hx (by simpa only [deriv_const] using he.deriv_eq)
  exact isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (closure_minimal hs isClosed_Icc)

private theorem exists_joinTransition_jet_bound (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, |iteratedDeriv k smoothTransition x| ≤ C := by
  cases k with
  | zero =>
    exact ⟨1, zero_le_one, fun x => by
      simpa only [iteratedDeriv_zero, abs_of_nonneg (smoothTransition.nonneg x)] using
        smoothTransition.le_one x⟩
  | succ k =>
    have hs : HasCompactSupport (iteratedDeriv k (deriv smoothTransition)) := by
      induction k with
      | zero => simpa only [iteratedDeriv_zero] using hasCompactSupport_deriv_joinTransition
      | succ k ih =>
        rw [iteratedDeriv_succ]
        exact ih.deriv
    have hD : ContDiff ℝ ∞ (deriv smoothTransition) :=
      (contDiff_infty_iff_deriv.mp smoothTransition.contDiff).2
    have hc := ContDiff.continuous_iteratedDeriv k hD (by simp)
    obtain ⟨C, hC⟩ := hs.exists_bound_of_continuous hc
    exact ⟨C, (norm_nonneg _).trans (hC 0), fun x => by
      simpa only [iteratedDeriv_succ', Real.norm_eq_abs] using hC x⟩

/-- The transition costs a power of the inverse collar width at each
fixed derivative order, with one constant for all positions and widths. -/
theorem exists_morseJoinWeight_jet_bound (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a b h : ℝ, 0 < h → ∀ x : ℝ,
      |iteratedDeriv k (morseJoinLeftWeight a h) x| ≤ C * (2 / h) ^ k ∧
        |iteratedDeriv k (morseJoinRightWeight b h) x| ≤ C * (2 / h) ^ k := by
  obtain ⟨C, hC, hbnd⟩ := exists_joinTransition_jet_bound k
  have hSmooth : ContDiff ℝ ∞ smoothTransition := smoothTransition.contDiff
  have hcd : ContDiff ℝ k smoothTransition := hSmooth.of_le (by simp)
  have haffine (c s x : ℝ) :
      |iteratedDeriv k (fun t => smoothTransition (c * (t - s))) x| ≤ C * |c| ^ k := by
    rw [iteratedDeriv_comp_sub_const k (fun t : ℝ => smoothTransition (c * t)) s,
      iteratedDeriv_comp_const_mul hcd c, abs_mul, abs_pow]
    exact (mul_le_mul_of_nonneg_left (hbnd _) (pow_nonneg (abs_nonneg c) k)).trans_eq (mul_comm _ _)
  refine ⟨C, hC, fun a b h hh x => ?_⟩
  have hcancel : (2 : ℝ) / h * h = 2 := div_mul_cancel₀ _ hh.ne'
  have hL : morseJoinLeftWeight a h = fun t => smoothTransition (-(2 / h) * (t - (a + h))) := by
    funext t
    unfold morseJoinLeftWeight
    congr 1
    calc
      _ = 2 - (2 / h) * (t - a) := by ring
      _ = (2 / h) * h - (2 / h) * (t - a) := by rw [hcancel]
      _ = _ := by ring
  have hR : morseJoinRightWeight b h = fun t => smoothTransition ((2 / h) * (t - (b - h))) := by
    funext t
    unfold morseJoinRightWeight
    congr 1
    calc
      _ = 2 + (2 / h) * (t - b) := by ring
      _ = (2 / h) * h + (2 / h) * (t - b) := by rw [hcancel]
      _ = _ := by ring
  have h2 : 0 ≤ (2 : ℝ) / h := div_nonneg (by norm_num) hh.le
  constructor
  · rw [hL]
    simpa only [abs_neg, abs_of_nonneg h2] using haffine (-(2 / h)) (a + h) x
  · rw [hR]
    simpa only [abs_of_nonneg h2] using haffine (2 / h) (b - h) x

theorem iteratedDeriv_morseJoinLog_succ {a b hL hR : ℝ} {fL fR : ℝ → ℝ}
    (hfL : ContDiff ℝ ∞ fL) (hfR : ContDiff ℝ ∞ fR) (k : ℕ) :
    iteratedDeriv (k + 1) (morseJoinLog a b hL hR fL fR) =
      iteratedDeriv k (morseJoinSlope a b hL hR fL fR) := by
  rw [iteratedDeriv_succ']
  have hd : deriv (morseJoinLog a b hL hR fL fR) = morseJoinSlope a b hL hR fL fR :=
    funext fun x => (hasDerivAt_morseJoinLog hfL hfR x).deriv
  rw [hd]

end ContinuousFlexibility.Radial
