import ContinuousFlexibility.Radial.MorseLeftCapIntegrals
import ContinuousFlexibility.Radial.MorseRightCapBounds

/-!
# The left part of the actual Morse cell

The backwards Volterra equation bounds the radius before any assumption
on its sign. The two signed coefficient integrals give the left initial
expansions in (rm6a), and the two turning points then control the velocity.
The same initial-value solution can be used on the retained right cap.
-/

namespace ContinuousFlexibility.Radial

open MeasureTheory Set
open scoped ContDiff

private theorem left_cap_small_parameters {A B : ℝ}
    (hB : 0 < B) (hAB : 4 * B < A) (hA₀ : A ≤ 1 / 1000)
    (hBAlo : A ^ 9 / (9 : ℝ) ^ 9 ≤ B) (hBAhi : B ≤ A ^ 9) :
    let L := morseLeftMassLength A B
    B ≤ A ^ 2 ∧ B * L ≤ A ^ 2 ∧ B * (L ^ 2 / 2) ≤ A ^ 2 ∧
      (1 / 100 : ℝ) * A ^ 5 * L ≤ A ^ 2 := by
  let L := morseLeftMassLength A B
  change B ≤ A ^ 2 ∧ B * L ≤ A ^ 2 ∧ B * (L ^ 2 / 2) ≤ A ^ 2 ∧
    (1 / 100 : ℝ) * A ^ 5 * L ≤ A ^ 2
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  have hL : 0 ≤ L := sub_nonneg.mpr (morseCellLeftCut_lt_rightTurn hB hAB).le
  have hL' : L ≤ 100 / A := morseLeftMassLength_le_hundred_div
    (hA₀.trans (by norm_num)) hB hAB hBAlo
  have hPow (k : ℕ) : A ^ k ≤ (1 / 1000 : ℝ) ^ k :=
    pow_le_pow_left₀ hA.le hA₀ k
  have hB₁ : B ≤ A ^ 2 := calc
    B ≤ A ^ 9 := hBAhi
    _ = A ^ 2 * A ^ 7 := by ring
    _ ≤ A ^ 2 * 1 := mul_le_mul_of_nonneg_left
      ((hPow 7).trans (by norm_num)) (sq_nonneg A)
    _ = _ := mul_one _
  have hBL : B * L ≤ A ^ 2 := calc
    _ ≤ A ^ 9 * (100 / A) := mul_le_mul hBAhi hL' hL (by positivity)
    _ = A ^ 2 * (100 * A ^ 6) := by field_simp [hA.ne']
    _ ≤ A ^ 2 * 1 := mul_le_mul_of_nonneg_left
      ((mul_le_mul_of_nonneg_left (hPow 6) (by norm_num : (0 : ℝ) ≤ 100)).trans
        (by norm_num)) (sq_nonneg A)
    _ = _ := mul_one _
  have hBL₂ : B * (L ^ 2 / 2) ≤ A ^ 2 := calc
    _ ≤ A ^ 9 * ((100 / A) ^ 2 / 2) :=
      mul_le_mul hBAhi
        (div_le_div_of_nonneg_right (pow_le_pow_left₀ hL hL' 2) (by norm_num))
        (by positivity) (by positivity)
    _ = A ^ 2 * (5000 * A ^ 5) := by
      field_simp [hA.ne']
      ring
    _ ≤ A ^ 2 * 1 := mul_le_mul_of_nonneg_left
      ((mul_le_mul_of_nonneg_left (hPow 5) (by norm_num : (0 : ℝ) ≤ 5000)).trans
        (by norm_num)) (sq_nonneg A)
    _ = _ := mul_one _
  have hD : (1 / 100 : ℝ) * A ^ 5 * L ≤ A ^ 2 := calc
    _ ≤ (1 / 100 : ℝ) * A ^ 5 * (100 / A) :=
      mul_le_mul_of_nonneg_left hL' (by positivity)
    _ = A ^ 2 * A ^ 2 := by field_simp [hA.ne']
    _ ≤ A ^ 2 * 1 := mul_le_mul_of_nonneg_left
      ((hPow 2).trans (by norm_num)) (sq_nonneg A)
    _ = _ := mul_one _
  exact ⟨hB₁, hBL, hBL₂, hD⟩

private theorem abs_integral_weight_mul_le {a b : ℝ} {w g f : ℝ → ℝ}
    {M : ℝ} (hab : a ≤ b) (hw : Continuous w) (hg : Continuous g)
    (hf : Continuous f) (hwp : ∀ y ∈ Icc a b, 0 ≤ w y)
    (hbound : ∀ y ∈ Icc a b, |f y| ≤ M) :
    |∫ y in a..b, w y * g y * f y| ≤ M * (∫ y in a..b, w y * |g y|) := by
  have hI : Continuous (fun y => w y * g y * f y) := (hw.mul hg).mul hf
  have hJ : Continuous (fun y => M * (w y * |g y|)) :=
    continuous_const.mul (hw.mul hg.abs)
  calc
    _ ≤ ∫ y in a..b, |w y * g y * f y| :=
      intervalIntegral.abs_integral_le_integral_abs hab
    _ ≤ ∫ y in a..b, M * (w y * |g y|) := by
      apply intervalIntegral.integral_mono_on hab (hI.abs.intervalIntegrable a b)
        (hJ.intervalIntegrable a b)
      intro y hy
      change |w y * g y * f y| ≤ M * (w y * |g y|)
      rw [abs_mul, abs_mul, abs_of_nonneg (hwp y hy), mul_comm M]
      exact mul_le_mul_of_nonneg_left (hbound y hy)
        (mul_nonneg (hwp y hy) (abs_nonneg _))
    _ = _ := intervalIntegral.integral_const_mul _ _

private theorem morseRadius_backward_velocity {A B a b x : ℝ} {r : ℝ → ℝ}
    (hr : ContDiff ℝ ∞ r) (hx : x ∈ Icc a b)
    (hEq : ∀ y ∈ Icc a b, deriv (deriv r) y = -morseRho A B y * r y) :
    deriv r x = deriv r b + ∫ y in x..b, morseRho A B y * r y := by
  have h := morseRadius_velocity_eq_integral hr (right_mem_Icc.mpr (hx.1.trans hx.2)) hx hEq
  rw [intervalIntegral.integral_symm x b, sub_neg_eq_add] at h
  exact h

private theorem morseRadius_backward_volterra {A B a b x : ℝ} {r : ℝ → ℝ}
    (hr : ContDiff ℝ ∞ r) (hx : x ∈ Icc a b)
    (hEq : ∀ y ∈ Icc a b, deriv (deriv r) y = -morseRho A B y * r y) :
    r x = r b - deriv r b * (b - x) -
      ∫ y in x..b, (y - x) * morseRho A B y * r y := by
  have h := morseRadius_eq_volterra hr (right_mem_Icc.mpr (hx.1.trans hx.2)) hx hEq
  have he : (∫ y in b..x, (x - y) * morseRho A B y * r y) =
      ∫ y in x..b, (y - x) * morseRho A B y * r y := by
    rw [intervalIntegral.integral_symm x b, ← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro y _
    ring
  rw [he] at h
  linarith only [h]

private theorem interval_weight_sub_one {a b : ℝ} {w g r : ℝ → ℝ}
    (hw : Continuous w) (hg : Continuous g) (hr : Continuous r) :
    (∫ y in a..b, w y * g y * (r y - 1)) =
      (∫ y in a..b, w y * g y * r y) - ∫ y in a..b, w y * g y := by
  calc
    _ = ∫ y in a..b, w y * g y * r y - w y * g y := by
      apply intervalIntegral.integral_congr
      intro y _
      ring
    _ = _ := intervalIntegral.integral_sub (((hw.mul hg).mul hr).intervalIntegrable a b)
      ((hw.mul hg).intervalIntegrable a b)

/-- Bounds on the same actual solution before the right turning point.
The positive lower bound for the speed uses both curvature signs. -/
theorem morseLeftCap_radius_bounds {A B : ℝ} (hB : 0 < B) (hAB : 4 * B < A)
    (hA₀ : A ≤ 1 / 1000) (hBAlo : A ^ 9 / (9 : ℝ) ^ 9 ≤ B) (hBAhi : B ≤ A ^ 9)
    {r : ℝ → ℝ} (hr : ContDiff ℝ ∞ r) (hr₀ : r (morseRightTurn A B) = 1)
    (hv₀ : deriv r (morseRightTurn A B) = (1 / 100 : ℝ) * A ^ 5)
    (hEq : ∀ y ∈ Icc morseCellLeftCut (morseRightTurn A B),
      deriv (deriv r) y = -morseRho A B y * r y) :
    (∀ x ∈ Icc morseCellLeftCut (morseRightTurn A B),
      |r x - 1| ≤ 6 * A ∧ 0 < r x ∧ r x ≤ 2 ∧
        (1 / 100 : ℝ) * A ^ 5 ≤ deriv r x ∧ deriv r x ≤ 7 * A) ∧
    |deriv r morseCellLeftCut - (3 / 8 : ℝ) * A| ≤ 22 * A ^ 2 ∧
    A / 4 ≤ deriv r morseCellLeftCut ∧
    |r morseCellLeftCut - (1 - (15 / 16 : ℝ) * A)| ≤ 21 * A ^ 2 := by
  let a := morseCellLeftCut
  let b := morseRightTurn A B
  let L := morseLeftMassLength A B
  let v₀ := (1 / 100 : ℝ) * A ^ 5
  let ρ := morseRho A B
  change r b = 1 at hr₀
  change deriv r b = v₀ at hv₀
  change ∀ y ∈ Icc a b, deriv (deriv r) y = -ρ y * r y at hEq
  have hab : a ≤ b := (morseCellLeftCut_lt_rightTurn hB hAB).le
  have ha : a ∈ Icc a b := left_mem_Icc.mpr hab
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  have hA₂ : A ^ 2 ≤ (1 / 1000 : ℝ) * A := by
    simpa only [pow_two] using mul_le_mul_of_nonneg_right hA₀ hA.le
  have hAv : v₀ ≤ A ^ 2 := calc
    _ = A ^ 2 * ((1 / 100 : ℝ) * A ^ 3) := by dsimp [v₀]; ring
    _ ≤ A ^ 2 * 1 := mul_le_mul_of_nonneg_left
      ((mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hA.le hA₀ 3)
        (by norm_num : (0 : ℝ) ≤ 1 / 100)).trans (by norm_num)) (sq_nonneg A)
    _ = _ := mul_one _
  have hvpos : 0 < v₀ := by dsimp [v₀]; positivity
  obtain ⟨hB₂, hBL, hBL₂, hD⟩ := left_cap_small_parameters hB hAB hA₀ hBAlo hBAhi
  change B * L ≤ A ^ 2 at hBL
  change B * (L ^ 2 / 2) ≤ A ^ 2 at hBL₂
  change v₀ * L ≤ A ^ 2 at hD
  have hI₀ (x : ℝ) (hx : x ∈ Icc a b) : (∫ y in x..b, |ρ y|) ≤ 3 * A := by
    have h := morseLeftMass_abs_integral_from_le hB hAB hx
    change (∫ y in x..b, |ρ y|) ≤ (21 / 8) * A + B * L at h
    linarith only [h, hBL, hA₂, hA]
  have hI₁ (x : ℝ) (hx : x ∈ Icc a b) :
      (∫ y in x..b, (y - x) * |ρ y|) ≤ (5 / 2 : ℝ) * A := by
    have h := morseLeftMass_abs_first_moment_from_le hB hAB hx
    change (∫ y in x..b, (y - x) * |ρ y|) ≤ (33 / 16) * A + B * (L ^ 2 / 2) at h
    linarith only [h, hBL₂, hA₂, hA]
  have hρ : Continuous ρ := (contDiff_morseRho A B).continuous
  obtain ⟨p, hp, hpmax⟩ := (isCompact_Icc : IsCompact (Icc a b)).exists_isMaxOn
    ⟨a, ha⟩ ((hr.continuous.sub continuous_const).abs.continuousOn)
  let M := |r p - 1|
  have hM₀ : 0 ≤ M := abs_nonneg _
  have hM (x : ℝ) (hx : x ∈ Icc a b) : |r x - 1| ≤ M := isMaxOn_iff.mp hpmax x hx
  have hrabs (x : ℝ) (hx : x ∈ Icc a b) : |r x| ≤ 1 + M := calc
    |r x| = |(r x - 1) + 1| := by rw [sub_add_cancel]
    _ ≤ |r x - 1| + |(1 : ℝ)| := abs_add_le _ _
    _ ≤ 1 + M := by
      rw [abs_one, add_comm (|r x - 1|) 1]
      exact add_le_add_right (hM x hx) 1
  have hdev (x : ℝ) (hx : x ∈ Icc a b) :
      |r x - 1| ≤ A ^ 2 + ((5 / 2 : ℝ) * A) * (1 + M) := by
    let I := ∫ y in x..b, (y - x) * ρ y * r y
    have hI : |I| ≤ ((5 / 2 : ℝ) * A) * (1 + M) := calc
      _ ≤ (1 + M) * (∫ y in x..b, (y - x) * |ρ y|) :=
        abs_integral_weight_mul_le hx.2 (continuous_id.sub continuous_const) hρ hr.continuous
          (fun _ hy => sub_nonneg.mpr hy.1)
          (fun y hy => hrabs y ⟨hx.1.trans hy.1, hy.2⟩)
      _ ≤ (1 + M) * ((5 / 2 : ℝ) * A) :=
        mul_le_mul_of_nonneg_left (hI₁ x hx) (by positivity)
      _ = _ := mul_comm _ _
    have hdx : v₀ * (b - x) ≤ A ^ 2 := by
      have h : b - x ≤ L := sub_le_sub_left hx.1 b
      exact (mul_le_mul_of_nonneg_left h hvpos.le).trans hD
    have h := morseRadius_backward_volterra hr hx hEq
    change r x = r b - deriv r b * (b - x) - I at h
    rw [hr₀, hv₀] at h
    have he : r x - 1 = -(v₀ * (b - x) + I) := by linarith only [h]
    rw [he, abs_neg]
    calc
      _ ≤ |v₀ * (b - x)| + |I| := abs_add_le _ _
      _ = v₀ * (b - x) + |I| := by
        rw [abs_of_nonneg (mul_nonneg hvpos.le (sub_nonneg.mpr hx.2))]
      _ ≤ _ := add_le_add hdx hI
  have hMp : M ≤ A ^ 2 + ((5 / 2 : ℝ) * A) * (1 + M) := hdev p hp
  have hcoef : (5 / 2 : ℝ) * A ≤ 1 / 2 := by linarith only [hA₀]
  have hηM := mul_le_mul_of_nonneg_right hcoef hM₀
  have hM' : M ≤ 6 * A := by nlinarith only [hMp, hηM, hA₂, hA]
  have hclose (x : ℝ) (hx : x ∈ Icc a b) : |r x - 1| ≤ 6 * A := (hM x hx).trans hM'
  have hrange (x : ℝ) (hx : x ∈ Icc a b) : 0 < r x ∧ r x ≤ 2 := by
    obtain ⟨hlo, hhi⟩ := abs_le.mp (hclose x hx)
    exact ⟨by linarith only [hlo, hA₀], by linarith only [hhi, hA₀]⟩
  have hJ₀ : |(∫ y in a..b, ρ y * r y) - ∫ y in a..b, ρ y| ≤ 18 * A ^ 2 := by
    have h := abs_integral_weight_mul_le hab (w := fun _ => 1) (g := ρ)
      (f := fun y => r y - 1) continuous_const hρ (hr.continuous.sub continuous_const)
      (fun _ _ => zero_le_one) hclose
    rw [interval_weight_sub_one continuous_const hρ hr.continuous] at h
    simp only [one_mul] at h
    exact h.trans (calc
      _ ≤ (6 * A) * (3 * A) := mul_le_mul_of_nonneg_left (hI₀ a ha) (by positivity)
      _ = _ := by ring)
  have hJ₁ : |(∫ y in a..b, (y - a) * ρ y * r y) -
      ∫ y in a..b, (y - a) * ρ y| ≤ 15 * A ^ 2 := by
    have h := abs_integral_weight_mul_le hab (w := fun y => y - a) (g := ρ)
      (f := fun y => r y - 1) (continuous_id.sub continuous_const) hρ
      (hr.continuous.sub continuous_const) (fun _ hy => sub_nonneg.mpr hy.1) hclose
    rw [interval_weight_sub_one (a := a) (b := b) (w := fun y => y - a)
      (continuous_id.sub continuous_const) hρ hr.continuous] at h
    exact h.trans (calc
      _ ≤ (6 * A) * ((5 / 2 : ℝ) * A) :=
        mul_le_mul_of_nonneg_left (hI₁ a ha) (by positivity)
      _ = _ := by ring)
  have hE₀ := morseLeftMass_integral_error hB hAB
  change |(∫ y in a..b, ρ y) - (3 / 8) * A| ≤ 2 * B + B * L at hE₀
  have hE₁ := morseLeftMass_first_moment_error hB hAB
  change |(∫ y in a..b, (y - a) * ρ y) - (15 / 16) * A| ≤
    2 * B * (L + 1) + B * (L ^ 2 / 2) at hE₁
  have hvE : |deriv r a - (3 / 8 : ℝ) * A| ≤ 22 * A ^ 2 := by
    have h := morseRadius_backward_velocity hr ha hEq
    rw [hv₀] at h
    apply abs_le.mpr
    have h₀ := abs_le.mp hE₀
    have h₁ := abs_le.mp hJ₀
    constructor <;> linarith only [h, h₀.1, h₀.2, h₁.1, h₁.2, hvpos, hAv, hB₂, hBL]
  have hvl : A / 4 ≤ deriv r a := by linarith only [(abs_le.mp hvE).1, hA₂, hA]
  have hrE : |r a - (1 - (15 / 16 : ℝ) * A)| ≤ 21 * A ^ 2 := by
    have h := morseRadius_backward_volterra hr ha hEq
    change r a = r b - deriv r b * L - ∫ y in a..b, (y - a) * ρ y * r y at h
    rw [hr₀, hv₀] at h
    have hD₀ : 0 ≤ v₀ * L := mul_nonneg hvpos.le (sub_nonneg.mpr hab)
    apply abs_le.mpr
    have h₀ := abs_le.mp hE₁
    have h₁ := abs_le.mp hJ₁
    constructor <;>
      nlinarith only [h, h₀.1, h₀.2, h₁.1, h₁.2, hD₀, hD, hB₂, hBL, hBL₂]
  refine ⟨?_, hvE, hvl, hrE⟩
  intro x hx
  change x ∈ Icc a b at hx
  change |r x - 1| ≤ 6 * A ∧ 0 < r x ∧ r x ≤ 2 ∧ v₀ ≤ deriv r x ∧ deriv r x ≤ 7 * A
  refine ⟨hclose x hx, (hrange x hx).1, (hrange x hx).2, ?_, ?_⟩
  · by_cases hXL : morseLeftTurn A B ≤ x
    · have hI : 0 ≤ ∫ y in x..b, ρ y * r y := by
        apply intervalIntegral.integral_nonneg hx.2
        intro y hy
        have hLy := hXL.trans hy.1
        have hsign : 0 ≤ ρ y := by
          rcases eq_or_lt_of_le hLy with h | h
          · exact le_of_eq (((morseRho_zero_iff_turn hB hAB y).2 (Or.inl h.symm)).symm)
          rcases eq_or_lt_of_le hy.2 with h' | h'
          · exact le_of_eq (((morseRho_zero_iff_turn hB hAB y).2 (Or.inr h')).symm)
          · exact (morseRho_pos_between_turns hB hAB ⟨h, h'⟩).le
        exact mul_nonneg hsign (hrange y ⟨hx.1.trans hy.1, hy.2⟩).1.le
      have h := morseRadius_backward_velocity hr hx hEq
      change deriv r x = deriv r b + ∫ y in x..b, ρ y * r y at h
      rw [h, hv₀]
      exact le_add_of_nonneg_right hI
    · have hI : 0 ≤ ∫ y in a..x, -(ρ y * r y) := by
        apply intervalIntegral.integral_nonneg hx.1
        intro y hy
        exact neg_nonneg.mpr (mul_nonpos_of_nonpos_of_nonneg
          (morseRho_neg_before_left_turn hB hAB (hy.2.trans_lt (lt_of_not_ge hXL))).le
          (hrange y ⟨hy.1, hy.2.trans hx.2⟩).1.le)
      rw [intervalIntegral.integral_neg] at hI
      have h := morseRadius_velocity_eq_integral hr ha hx hEq
      change deriv r x = deriv r a - ∫ y in a..x, ρ y * r y at h
      have hvle : v₀ ≤ A / 4 := by linarith only [hAv, hA₂, hA]
      linarith only [h, hI, hvl, hvle]
  · have hI : |∫ y in x..b, ρ y * r y| ≤ 6 * A := by
      have h := abs_integral_weight_mul_le hx.2 (w := fun _ => 1) (g := ρ)
        (f := r) continuous_const hρ hr.continuous (fun _ _ => zero_le_one)
        (fun y hy => by
          obtain ⟨hpos, hle⟩ := hrange y ⟨hx.1.trans hy.1, hy.2⟩
          rwa [abs_of_pos hpos])
      simp only [one_mul] at h
      exact h.trans (calc
        _ ≤ 2 * (3 * A) := mul_le_mul_of_nonneg_left (hI₀ x hx) (by norm_num)
        _ = _ := by ring)
    have h := morseRadius_backward_velocity hr hx hEq
    rw [hv₀] at h
    linarith only [h, (abs_le.mp hI).2, hAv, hA₂, hA]

/-- The left and right estimates hold for one globally smooth function
satisfying the true radius equation throughout the retained Morse cell. -/
theorem exists_morseRadius_retainedCell {A B : ℝ} (hB : 0 < B) (hAB : 4 * B < A)
    (hA₀ : A ≤ 1 / 1000) (hBAlo : A ^ 9 / (9 : ℝ) ^ 9 ≤ B) (hBAhi : B ≤ A ^ 9) :
    let b := morseRightTurn A B
    let e := morseRightCapEnd A B (1 / 100)
    ∃ r : ℝ → ℝ, ContDiff ℝ ∞ r ∧ r b = 1 ∧ deriv r b = (1 / 100 : ℝ) * A ^ 5 ∧
      (∀ x ∈ Icc morseCellLeftCut e, deriv (deriv r) x = -morseRho A B x * r x) ∧
      (∀ x ∈ Icc morseCellLeftCut e,
        |r x - 1| ≤ 6 * A ∧ 0 < r x ∧ r x ≤ 2 ∧
          (1 / 100 : ℝ) * A ^ 5 ≤ deriv r x ∧ deriv r x ≤ 7 * A) ∧
      (∀ x ∈ Icc b e, deriv r x ≤ (3 / 100 : ℝ) * A ^ 5) ∧
      |deriv r morseCellLeftCut - (3 / 8 : ℝ) * A| ≤ 22 * A ^ 2 ∧
      A / 4 ≤ deriv r morseCellLeftCut ∧
      |r morseCellLeftCut - (1 - (15 / 16 : ℝ) * A)| ≤ 21 * A ^ 2 ∧
      (9 / 10 : ℝ) * A ≤ r e - r morseCellLeftCut ∧
      r e - r morseCellLeftCut ≤ 2 * A := by
  let b := morseRightTurn A B
  let e := morseRightCapEnd A B (1 / 100)
  have hab : morseCellLeftCut ≤ b := (morseCellLeftCut_lt_rightTurn hB hAB).le
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  have hA₁ : A ≤ 1 := hA₀.trans (by norm_num)
  have hbe : b ≤ e :=
    le_add_of_nonneg_right (morseRightCapLength_pos hA (by norm_num : (0 : ℝ) < 1 / 100)).le
  obtain ⟨r, hr, hr₀, hv₀, hEq, hRight, hspanLo, hspanHi⟩ :=
    exists_morseRadius_with_rightCap hB hAB hA₁ hBAhi hab
  obtain ⟨hLeft, hvE, hvL, hrE⟩ := morseLeftCap_radius_bounds hB hAB hA₀ hBAlo hBAhi
    hr hr₀ hv₀ (fun x hx => hEq x ⟨hx.1, hx.2.trans hbe⟩)
  have hA₂ : A ^ 2 ≤ (1 / 1000 : ℝ) * A := by
    simpa only [pow_two] using mul_le_mul_of_nonneg_right hA₀ hA.le
  have hA₅ : A ^ 5 ≤ A := calc
    _ = A * A ^ 4 := by ring
    _ ≤ A * 1 := mul_le_mul_of_nonneg_left
      (by simpa only [one_pow] using pow_le_pow_left₀ hA.le hA₁ 4) hA.le
    _ = _ := mul_one _
  change (1 / 10000 : ℝ) * A ≤ r e - 1 at hspanLo
  change r e - 1 ≤ (3 / 10000 : ℝ) * A at hspanHi
  refine ⟨r, hr, hr₀, hv₀, hEq, ?_, fun x hx => (hRight x hx).2.2.2.2,
    hvE, hvL, hrE, ?_, ?_⟩
  · intro x hx
    by_cases hxb : x ≤ b
    · exact hLeft x ⟨hx.1, hxb⟩
    · obtain ⟨hdev, hpos, hhi, hvlo, hvhi⟩ := hRight x ⟨le_of_lt (lt_of_not_ge hxb), hx.2⟩
      exact ⟨by linarith only [hdev, hA], hpos, hhi, hvlo,
        by linarith only [hvhi, hA₅, hA]⟩
  · linarith only [hspanLo, (abs_le.mp hrE).2, hA₂, hA]
  · linarith only [hspanHi, (abs_le.mp hrE).1, hA₂, hA]

end ContinuousFlexibility.Radial
