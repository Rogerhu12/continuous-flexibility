module

public import ContinuousFlexibility.Radial.MorseLeftCapBounds
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-!
# Positive model collars at the physical joining cuts

The same Morse initial-value solution is continued a fixed distance in X
past the retained interval. The outward left collar has curvature of order
A and speed of order A. The outward right collar has curvature of order B
and speed of order A^5. No sign assumptions are made on the solution before
the Volterra estimate. These bounds control the actual log-height slope of
the radial profile on the germs used in (rm8).
-/

@[expose] public section

namespace ContinuousFlexibility.Radial

open Filter MeasureTheory Real Set
open scoped ContDiff Topology

private theorem morseRadius_short_collar {A B Q a b x₀ : ℝ}
    {r : ℝ → ℝ} (hr : ContDiff ℝ ∞ r) (hx₀ : x₀ ∈ Icc a b)
    (hshort : b - a ≤ 1 / 1000) (hQ₀ : 0 ≤ Q) (hQ : Q ≤ 1)
    (hr₀ : (3 / 4 : ℝ) ≤ r x₀ ∧ r x₀ ≤ 5 / 4) (hv₀ : |deriv r x₀| ≤ 1)
    (hρ : ∀ y ∈ Icc a b, |morseRho A B y| ≤ Q)
    (hEq : ∀ y ∈ Icc a b, deriv (deriv r) y = -morseRho A B y * r y) :
    ∀ x ∈ Icc a b, (1 / 2 : ℝ) ≤ r x ∧ r x ≤ 2 ∧
      |deriv r x - deriv r x₀| ≤ 2 * Q * |x - x₀| := by
  obtain ⟨p, hp, hpmax⟩ := (isCompact_Icc : IsCompact (Icc a b)).exists_isMaxOn
    ⟨x₀, hx₀⟩ hr.continuous.abs.continuousOn
  let M := |r p|
  have hM₀ : 0 ≤ M := abs_nonneg _
  have hM (y : ℝ) (hy : y ∈ Icc a b) : |r y| ≤ M := isMaxOn_iff.mp hpmax y hy
  have hdist (x : ℝ) (hx : x ∈ Icc a b) : |x - x₀| ≤ 1 / 1000 := by
    apply abs_le.mpr
    exact ⟨by linarith only [hshort, hx₀.2, hx.1],
      by linarith only [hshort, hx₀.1, hx.2]⟩
  have hdev (x : ℝ) (hx : x ∈ Icc a b) :
      |r x - r x₀| ≤ (1 / 1000 : ℝ) + (1 / 1000000 : ℝ) * M := by
    let I := ∫ y in x₀..x, (x - y) * morseRho A B y * r y
    have hI : |I| ≤ ((1 / 1000000 : ℝ) * M) := calc
      _ ≤ ((1 / 1000 : ℝ) * 1 * M) * |x - x₀| := by
        rw [← Real.norm_eq_abs]
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro y hy
        have hy' := uIoc_subset_uIcc hy
        have hy'' := uIcc_subset_Icc hx₀ hx hy'
        have hxy : |x - y| ≤ 1 / 1000 := (abs_sub_right_of_mem_uIcc hy').trans (hdist x hx)
        rw [Real.norm_eq_abs, abs_mul, abs_mul]
        exact mul_le_mul
          (mul_le_mul hxy ((hρ y hy'').trans hQ) (abs_nonneg _) (by norm_num))
          (hM y hy'') (abs_nonneg _) (by positivity)
      _ ≤ ((1 / 1000 : ℝ) * 1 * M) * (1 / 1000) :=
        mul_le_mul_of_nonneg_left (hdist x hx) (by positivity)
      _ = _ := by ring
    have h := morseRadius_eq_volterra hr hx₀ hx hEq
    change r x = r x₀ + deriv r x₀ * (x - x₀) - I at h
    have he : r x - r x₀ = deriv r x₀ * (x - x₀) - I := by linarith only [h]
    rw [he]
    calc
      _ ≤ |deriv r x₀ * (x - x₀)| + |I| := abs_sub _ _
      _ ≤ 1 * (1 / 1000 : ℝ) + (1 / 1000000 : ℝ) * M := by
        rw [abs_mul]
        exact add_le_add
          (mul_le_mul hv₀ (hdist x hx) (abs_nonneg _) zero_le_one) hI
      _ = _ := by ring
  have hMp : M ≤ (5 / 4 : ℝ) + ((1 / 1000 : ℝ) + (1 / 1000000 : ℝ) * M) := calc
    M = |(r p - r x₀) + r x₀| := by simp only [M, sub_add_cancel]
    _ ≤ |r p - r x₀| + |r x₀| := abs_add_le _ _
    _ ≤ _ := by
      rw [abs_of_nonneg (by linarith only [hr₀.1] : 0 ≤ r x₀), add_comm (5 / 4 : ℝ)]
      exact add_le_add (hdev p hp) hr₀.2
  have hM₂ : M ≤ 2 := by linarith only [hMp]
  intro x hx
  have hdevx := abs_le.mp (hdev x hx)
  have hrlo : (1 / 2 : ℝ) ≤ r x := by linarith only [hdevx.1, hM₂, hr₀.1]
  have hrhi : r x ≤ 2 := by linarith only [hdevx.2, hM₂, hr₀.2]
  refine ⟨hrlo, hrhi, ?_⟩
  have h := morseRadius_velocity_eq_integral hr hx₀ hx hEq
  have he : deriv r x - deriv r x₀ = -(∫ y in x₀..x, morseRho A B y * r y) := by
    linarith only [h]
  rw [he, abs_neg, ← Real.norm_eq_abs]
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro y hy
  have hy' := uIcc_subset_Icc hx₀ hx (uIoc_subset_uIcc hy)
  rw [Real.norm_eq_abs, abs_mul, mul_comm 2 Q]
  exact mul_le_mul (hρ y hy') ((hM y hy').trans hM₂) (abs_nonneg _) hQ₀

noncomputable def morseJoinCollarWidth : ℝ := 1 / 1000

private theorem morseLeftCut_coefficient_bounds {A B x : ℝ}
    (hB : 0 < B) (hAB : 4 * B < A)
    (hx : x ∈ Icc (morseCellLeftCut - morseJoinCollarWidth) morseCellLeftCut) :
    (3 / 4 : ℝ) * A ≤ -morseRho A B x ∧ -morseRho A B x ≤ 7 * A := by
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  have htL : (3 / 2 : ℝ) ≤ exp (-x) := by
    rw [← exp_neg_morseCellLeftCut]
    exact exp_le_exp.mpr (neg_le_neg hx.2)
  have hlog2 : morseJoinCollarWidth ≤ log 2 := calc
    _ ≤ 1 - (2 : ℝ)⁻¹ := by norm_num [morseJoinCollarWidth]
    _ ≤ _ := one_sub_inv_le_log_of_pos (by norm_num)
  have htU : exp (-x) ≤ 3 := calc
    _ ≤ exp (-morseCellLeftCut + log 2) := by
      apply exp_le_exp.mpr
      linarith only [hx.1, hlog2]
    _ = _ := by
      rw [exp_add, exp_neg_morseCellLeftCut, exp_log (by norm_num : (0 : ℝ) < 2)]
      norm_num
  let t := exp (-x)
  have htL' : (3 / 2 : ℝ) ≤ t := htL
  have htU' : t ≤ 3 := htU
  have ht₀ : 0 ≤ t := by linarith only [htL']
  have ht₁ : 0 ≤ t - 1 := by linarith only [htL']
  have htwo : exp (-2 * x) = t ^ 2 := by
    dsimp only [t]
    rw [pow_two, ← exp_add]
    congr 1
    ring
  have hρ : -morseRho A B x = A * (t * (t - 1)) + B := by
    unfold morseRho
    rw [htwo]
    change -(A * (t - t ^ 2) - B) = _
    ring
  have htl : (3 / 2 : ℝ) * (1 / 2) ≤ t * (t - 1) :=
    mul_le_mul htL' (by linarith only [htL']) (by norm_num) ht₀
  have htu : t * (t - 1) ≤ (3 : ℝ) * 2 :=
    mul_le_mul htU' (by linarith only [htU']) ht₁ (by norm_num)
  rw [hρ]
  exact ⟨by linarith only [mul_le_mul_of_nonneg_left htl hA.le, hB],
    by linarith only [mul_le_mul_of_nonneg_left htu hA.le, hAB, hA]⟩

private theorem morseRightEnd_after_log_four {A B : ℝ} (hA : 0 < A)
    (hA₀ : A ≤ 1 / 1000) :
    morseRightTurn A B + log 4 ≤ morseRightCapEnd A B (1 / 100) := by
  have hAp : A ^ 4 ≤ (1 / 10 : ℝ) ^ 4 :=
    pow_le_pow_left₀ hA.le (hA₀.trans (by norm_num)) 4
  have hbig : (100 : ℝ) ≤ morseRightCapLength A (1 / 100) := by
    apply (le_div_iff₀ (pow_pos hA 4)).mpr
    linarith only [hAp]
  have hlog : log 4 ≤ 100 := (log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)).trans (by norm_num)
  exact add_le_add_right (hlog.trans hbig) _

/-- Collar estimates for an actual extended solution, with the same initial
data and the retained bounds supplied by the two cap theorems. -/
theorem morseRadius_joinCollar_bounds {A B : ℝ}
    (hB : 0 < B) (hAB : 4 * B < A) (hA₀ : A ≤ 1 / 1000) (hBAhi : B ≤ A ^ 9)
    {r : ℝ → ℝ} (hr : ContDiff ℝ ∞ r)
    (hLeftR : |r morseCellLeftCut - 1| ≤ 6 * A)
    (hLeftV : A / 4 ≤ deriv r morseCellLeftCut ∧ deriv r morseCellLeftCut ≤ 7 * A)
    (hRightR : |r (morseRightCapEnd A B (1 / 100)) - 1| ≤ (3 / 10000 : ℝ) * A)
    (hRightV : (1 / 100 : ℝ) * A ^ 5 ≤ deriv r (morseRightCapEnd A B (1 / 100)) ∧
      deriv r (morseRightCapEnd A B (1 / 100)) ≤ (3 / 100 : ℝ) * A ^ 5)
    (hEq : ∀ x ∈ Icc (morseCellLeftCut - morseJoinCollarWidth)
      (morseRightCapEnd A B (1 / 100) + morseJoinCollarWidth),
      deriv (deriv r) x = -morseRho A B x * r x) :
    (∀ x ∈ Icc (morseCellLeftCut - morseJoinCollarWidth) morseCellLeftCut,
      (1 / 2 : ℝ) ≤ r x ∧ r x ≤ 2 ∧ A / 5 ≤ deriv r x ∧ deriv r x ≤ 8 * A ∧
        (3 / 4 : ℝ) * A ≤ -morseRho A B x ∧ -morseRho A B x ≤ 7 * A) ∧
    (∀ x ∈ Icc (morseRightCapEnd A B (1 / 100))
        (morseRightCapEnd A B (1 / 100) + morseJoinCollarWidth),
      (1 / 2 : ℝ) ≤ r x ∧ r x ≤ 2 ∧ A ^ 5 / 200 ≤ deriv r x ∧ deriv r x ≤ A ^ 5 / 25 ∧
        B / 2 ≤ -morseRho A B x ∧ -morseRho A B x ≤ B) := by
  let a := morseCellLeftCut
  let b := morseRightTurn A B
  let e := morseRightCapEnd A B (1 / 100)
  let h := morseJoinCollarWidth
  change |r a - 1| ≤ 6 * A at hLeftR
  change A / 4 ≤ deriv r a ∧ deriv r a ≤ 7 * A at hLeftV
  change |r e - 1| ≤ (3 / 10000 : ℝ) * A at hRightR
  change (1 / 100 : ℝ) * A ^ 5 ≤ deriv r e ∧
    deriv r e ≤ (3 / 100 : ℝ) * A ^ 5 at hRightV
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  have hA₁ : A ≤ 1 := hA₀.trans (by norm_num)
  have hh : 0 < h := by norm_num [h, morseJoinCollarWidth]
  have hh₁ : h = (1 / 1000 : ℝ) := rfl
  have hab : a ≤ b := (morseCellLeftCut_lt_rightTurn hB hAB).le
  have hbe : b ≤ e :=
    le_add_of_nonneg_right (morseRightCapLength_pos hA (by norm_num : (0 : ℝ) < 1 / 100)).le
  have hae : a ≤ e := hab.trans hbe
  have hLeftEq : ∀ y ∈ Icc (a - h) a, deriv (deriv r) y = -morseRho A B y * r y :=
    fun y hy => hEq y ⟨hy.1, by linarith only [hy.2, hae, hh]⟩
  have hRightEq : ∀ y ∈ Icc e (e + h), deriv (deriv r) y = -morseRho A B y * r y :=
    fun y hy => hEq y ⟨by linarith only [hy.1, hae, hh], hy.2⟩
  have hLeftρ (y : ℝ) (hy : y ∈ Icc (a - h) a) : |morseRho A B y| ≤ 7 * A := by
    obtain ⟨hlo, hhi⟩ := morseLeftCut_coefficient_bounds hB hAB hy
    rw [abs_of_nonpos (by linarith only [hlo, hA] : morseRho A B y ≤ 0)]
    exact hhi
  have hRightρ (y : ℝ) (hy : y ∈ Icc e (e + h)) :
      B / 2 ≤ -morseRho A B y ∧ -morseRho A B y ≤ B :=
    ⟨morseRho_right_cap_lower hB hAB ((morseRightEnd_after_log_four hA hA₀).trans hy.1),
      (morseRho_right_cap_bounds hB hAB (hbe.trans hy.1)).2⟩
  have hB₅ : B ≤ A ^ 5 := calc
    _ ≤ A ^ 9 := hBAhi
    _ = A ^ 5 * A ^ 4 := by ring
    _ ≤ A ^ 5 * 1 := mul_le_mul_of_nonneg_left
      (by simpa only [one_pow] using pow_le_pow_left₀ hA.le hA₁ 4) (by positivity)
    _ = _ := mul_one _
  have hA₅ : A ^ 5 ≤ 1 := by simpa only [one_pow] using pow_le_pow_left₀ hA.le hA₁ 5
  have hLeft := morseRadius_short_collar (Q := 7 * A) hr
    (right_mem_Icc.mpr (sub_le_self a hh.le))
    (by linarith only [hh₁]) (by positivity) (by linarith only [hA₀])
    ⟨by linarith only [(abs_le.mp hLeftR).1, hA₀],
      by linarith only [(abs_le.mp hLeftR).2, hA₀]⟩
    (by
      rw [abs_of_nonneg (by linarith only [hLeftV.1, hA] : 0 ≤ deriv r a)]
      linarith only [hLeftV.2, hA₀])
    hLeftρ hLeftEq
  have hRight := morseRadius_short_collar (Q := B) hr
    (left_mem_Icc.mpr (le_add_of_nonneg_right hh.le))
    (by linarith only [hh₁]) hB.le (hB₅.trans hA₅)
    ⟨by linarith only [(abs_le.mp hRightR).1, hA₀],
      by linarith only [(abs_le.mp hRightR).2, hA₀]⟩
    (by
      rw [abs_of_nonneg ((show 0 ≤ (1 / 100 : ℝ) * A ^ 5 by positivity).trans hRightV.1)]
      linarith only [hRightV.2, hA₅])
    (fun y hy => by
      obtain ⟨hlo, hhi⟩ := hRightρ y hy
      rw [abs_of_nonpos (by linarith only [hlo, hB] : morseRho A B y ≤ 0)]
      exact hhi)
    hRightEq
  constructor
  · intro x hx
    change x ∈ Icc (a - h) a at hx
    obtain ⟨hlo, hhi, hv⟩ := hLeft x hx
    have hxdist : |x - a| ≤ 1 / 1000 := by
      rw [abs_of_nonpos (sub_nonpos.mpr hx.2)]
      linarith only [hx.1, hh₁]
    have hv' := (mul_le_mul_of_nonneg_left hxdist (by positivity : 0 ≤ 2 * (7 * A)))
    obtain ⟨hl, hu⟩ := abs_le.mp hv
    exact ⟨hlo, hhi, by linarith only [hl, hv', hLeftV.1, hA],
      by linarith only [hu, hv', hLeftV.2, hA], morseLeftCut_coefficient_bounds hB hAB hx⟩
  · intro x hx
    change x ∈ Icc e (e + h) at hx
    obtain ⟨hlo, hhi, hv⟩ := hRight x hx
    have hxDist : |x - e| ≤ 1 / 1000 := by
      rw [abs_of_nonneg (sub_nonneg.mpr hx.1)]
      linarith only [hx.2, hh₁]
    have hv' := mul_le_mul_of_nonneg_left hxDist (by positivity : 0 ≤ 2 * B)
    have hAp : 0 ≤ A ^ 5 := pow_nonneg hA.le _
    obtain ⟨hl, hu⟩ := abs_le.mp hv
    exact ⟨hlo, hhi, by linarith only [hl, hv', hRightV.1, hB₅, hAp],
      by linarith only [hu, hv', hRightV.2, hB₅, hAp], hRightρ x hx⟩

/-- One actual solution covers both collars and the retained Morse cell,
with the same initial data at the right turning point. -/
theorem exists_morseRadius_with_joinCollars {A B : ℝ}
    (hB : 0 < B) (hAB : 4 * B < A) (hA₀ : A ≤ 1 / 1000)
    (hBAlo : A ^ 9 / (9 : ℝ) ^ 9 ≤ B) (hBAhi : B ≤ A ^ 9) :
    let a := morseCellLeftCut
    let b := morseRightTurn A B
    let e := morseRightCapEnd A B (1 / 100)
    let h := morseJoinCollarWidth
    ∃ r : ℝ → ℝ, ContDiff ℝ ∞ r ∧ r b = 1 ∧ deriv r b = (1 / 100 : ℝ) * A ^ 5 ∧
      (∀ x ∈ Icc (a - h) (e + h), deriv (deriv r) x = -morseRho A B x * r x) ∧
      (∀ x ∈ Icc a b,
        |r x - 1| ≤ 6 * A ∧ 0 < r x ∧ r x ≤ 2 ∧
          (1 / 100 : ℝ) * A ^ 5 ≤ deriv r x ∧ deriv r x ≤ 7 * A) ∧
      (∀ x ∈ Icc b e,
        |r x - 1| ≤ (3 / 10000 : ℝ) * A ∧ 0 < r x ∧ r x ≤ 2 ∧
          (1 / 100 : ℝ) * A ^ 5 ≤ deriv r x ∧ deriv r x ≤ (3 / 100 : ℝ) * A ^ 5) ∧
      (∀ x ∈ Icc (a - h) a,
        (1 / 2 : ℝ) ≤ r x ∧ r x ≤ 2 ∧ A / 5 ≤ deriv r x ∧ deriv r x ≤ 8 * A ∧
          (3 / 4 : ℝ) * A ≤ -morseRho A B x ∧ -morseRho A B x ≤ 7 * A) ∧
      (∀ x ∈ Icc e (e + h),
        (1 / 2 : ℝ) ≤ r x ∧ r x ≤ 2 ∧ A ^ 5 / 200 ≤ deriv r x ∧ deriv r x ≤ A ^ 5 / 25 ∧
          B / 2 ≤ -morseRho A B x ∧ -morseRho A B x ≤ B) ∧
      (∀ x ∈ Icc (a - h) (e + h), 0 < deriv r x) ∧
      |deriv r a - (3 / 8 : ℝ) * A| ≤ 22 * A ^ 2 ∧
      A / 4 ≤ deriv r a ∧
      |r a - (1 - (15 / 16 : ℝ) * A)| ≤ 21 * A ^ 2 := by
  let a := morseCellLeftCut
  let b := morseRightTurn A B
  let e := morseRightCapEnd A B (1 / 100)
  let h := morseJoinCollarWidth
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  have hh : 0 ≤ h := by norm_num [h, morseJoinCollarWidth]
  have hab : a ≤ b := (morseCellLeftCut_lt_rightTurn hB hAB).le
  have hbe : b ≤ e :=
    le_add_of_nonneg_right (morseRightCapLength_pos hA (by norm_num : (0 : ℝ) < 1 / 100)).le
  have hstart : b ∈ Icc (a - h) (e + h) :=
    ⟨(sub_le_self _ hh).trans hab, hbe.trans (le_add_of_nonneg_right hh)⟩
  obtain ⟨r, hr, hr₀, hv₀, hEq⟩ := exists_morseRadius A B hstart 1 ((1 / 100 : ℝ) * A ^ 5)
  have hLeftEq : ∀ x ∈ Icc a b, deriv (deriv r) x = -morseRho A B x * r x :=
    fun x hx => hEq x ⟨(sub_le_self _ hh).trans hx.1, hx.2.trans hstart.2⟩
  have hRightEq : ∀ x ∈ Icc b e, deriv (deriv r) x = -morseRho A B x * r x :=
    fun x hx => hEq x ⟨hstart.1.trans hx.1, hx.2.trans (le_add_of_nonneg_right hh)⟩
  obtain ⟨hLeft, hvE, hvL, hrE⟩ :=
    morseLeftCap_radius_bounds hB hAB hA₀ hBAlo hBAhi hr hr₀ hv₀ hLeftEq
  have hc : (0 : ℝ) < 1 / 100 := by norm_num
  have hRight' := morseRightCap_radius_bounds (δ := (1 / 100 : ℝ)) (c := (1 / 100 : ℝ))
    hB hAB (hA₀.trans (by norm_num)) hBAhi hc (by norm_num) hc (by norm_num)
    hr hr₀ hv₀ hRightEq
  have hRight (x : ℝ) (hx : x ∈ Icc b e) :
      |r x - 1| ≤ (3 / 10000 : ℝ) * A ∧ 0 < r x ∧ r x ≤ 2 ∧
        (1 / 100 : ℝ) * A ^ 5 ≤ deriv r x ∧ deriv r x ≤ (3 / 100 : ℝ) * A ^ 5 := by
    simpa only [show 2 * (1 / 100 : ℝ) * (1 / 100) + (1 / 100) ^ 2 = 3 / 10000 by norm_num,
      show (1 / 100 : ℝ) + 2 * (1 / 100) = 3 / 100 by norm_num] using hRight' x hx
  have hLcut := hLeft a (left_mem_Icc.mpr hab)
  have hRcut := hRight e (right_mem_Icc.mpr hbe)
  obtain ⟨hLc, hRc⟩ := morseRadius_joinCollar_bounds hB hAB hA₀ hBAhi hr hLcut.1
    ⟨hvL, hLcut.2.2.2.2⟩ hRcut.1 ⟨hRcut.2.2.2.1, hRcut.2.2.2.2⟩ hEq
  refine ⟨r, hr, hr₀, hv₀, hEq, hLeft, hRight, hLc, hRc, ?_, hvE, hvL, hrE⟩
  intro x hx
  by_cases ha : x ≤ a
  · exact (by positivity : 0 < A / 5).trans_le (hLc x ⟨hx.1, ha⟩).2.2.1
  · have hax : a ≤ x := le_of_lt (lt_of_not_ge ha)
    by_cases hb : x ≤ b
    · exact (by positivity : 0 < (1 / 100 : ℝ) * A ^ 5).trans_le (hLeft x ⟨hax, hb⟩).2.2.2.1
    · have hbx : b ≤ x := le_of_lt (lt_of_not_ge hb)
      by_cases he : x ≤ e
      · exact (by positivity : 0 < (1 / 100 : ℝ) * A ^ 5).trans_le (hRight x ⟨hbx, he⟩).2.2.2.1
      · exact (by positivity : 0 < A ^ 5 / 200).trans_le
          (hRc x ⟨le_of_lt (lt_of_not_ge he), hx.2⟩).2.2.1

/-- Actual model coordinate on the image of the indicated open interval. -/
noncomputable def morseCollarCoordinate (r : ℝ → ℝ) (s a b : ℝ) : ℝ → ℝ :=
  Function.invFunOn (fun x => s * r x) (Ioo a b)

noncomputable def morseCollarLogProfile (r : ℝ → ℝ) (amplitude s a b y : ℝ) : ℝ :=
  log (amplitude * s * deriv r (morseCollarCoordinate r s a b y))

/-- The local inverse is smooth at every point of the physical collar.
Its derivative, the true ODE, and the logarithm give the actual physical
log-height slope; no derivative is taken in the wrong coordinate. -/
theorem morseCollarLogProfile_jet {A B amplitude s a b x : ℝ} {r : ℝ → ℝ}
    (hAmplitude : 0 < amplitude) (hs : 0 < s) (hr : ContDiff ℝ ∞ r)
    (hv : ∀ t ∈ Ioo a b, 0 < deriv r t) (hx : x ∈ Ioo a b)
    (hEq : deriv (deriv r) x = -morseRho A B x * r x) :
    morseCollarCoordinate r s a b (s * r x) = x ∧
    ContDiffAt ℝ ∞ (morseCollarLogProfile r amplitude s a b) (s * r x) ∧
    HasDerivAt (morseCollarLogProfile r amplitude s a b)
      (-morseRho A B x * r x / (s * (deriv r x) ^ 2)) (s * r x) := by
  let R : ℝ → ℝ := fun t => s * r t
  let X := morseCollarCoordinate r s a b
  let v := deriv r
  have hR : ContDiff ℝ ∞ R := contDiff_const.mul hr
  have hV : ContDiff ℝ ∞ v := (contDiff_infty_iff_deriv.mp hr).2
  have hD (t : ℝ) : HasDerivAt R (s * v t) t :=
    ((hr.differentiable (by simp) t).hasDerivAt).const_mul s
  have hmono : StrictMonoOn R (Ioo a b) :=
    strictMonoOn_of_deriv_pos (convex_Ioo a b) hR.continuous.continuousOn (fun t ht => by
      rw [(hD t).deriv]
      exact mul_pos hs (hv t (interior_subset ht)))
  have hleft : LeftInvOn X R (Ioo a b) := hmono.injOn.leftInvOn_invFunOn
  have hleftX : X (R x) = x := hleft hx
  have hnear : (fun t => X (R t)) =ᶠ[𝓝 x] (fun t => t) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with t ht
    exact hleft ht
  have hn : s * v x ≠ 0 := (mul_pos hs (hv x hx)).ne'
  have hstrict : HasStrictDerivAt R (s * v x) x := by
    rw [← (hD x).deriv]
    exact hR.hasStrictDerivAt (by simp)
  have hInvD := hstrict.to_local_left_inverse hn hnear
  let hd := hstrict.hasStrictFDerivAt_equiv hn
  let e := hd.toOpenPartialHomeomorph R
  have he : e.symm (R x) = x := hd.localInverse_apply_image
  have heD : HasDerivAt e (s * v x) (e.symm (R x)) := by
    rw [he]
    exact hD x
  have heC : ContDiffAt ℝ ∞ (e : ℝ → ℝ) (e.symm (R x)) := by
    rw [he]
    exact hR.contDiffAt
  have hInvC : ContDiffAt ℝ ∞ X (R x) :=
    (e.contDiffAt_symm_deriv hn hd.image_mem_toOpenPartialHomeomorph_target heD heC).congr_of_eventuallyEq
      (hd.localInverse_unique hnear)
  have hLogNZ : amplitude * s * v x ≠ 0 := (mul_pos (mul_pos hAmplitude hs) (hv x hx)).ne'
  have hLogC : ContDiffAt ℝ ∞ (fun t => log (amplitude * s * v t)) x :=
    ((contDiff_const.mul hV).contDiffAt).log hLogNZ
  have hLogD : HasDerivAt (fun t => log (amplitude * s * v t))
      ((amplitude * s * deriv v x) / (amplitude * s * v x)) x :=
    (((hV.differentiable (by simp) x).hasDerivAt).const_mul (amplitude * s)).log hLogNZ
  have hLogC' : ContDiffAt ℝ ∞ (fun t => log (amplitude * s * v t)) (X (R x)) := by
    rw [hleftX]
    exact hLogC
  refine ⟨hleftX, hLogC'.comp (R x) hInvC, ?_⟩
  have hG : HasDerivAt (fun y => log (amplitude * s * v (X y)))
      ((amplitude * s * deriv v x) / (amplitude * s * v x) * (s * v x)⁻¹) (R x) :=
    hLogD.comp_of_eq (R x) hInvD.hasDerivAt hleftX.symm
  apply hG.congr_deriv
  change (amplitude * s * deriv (deriv r) x) / (amplitude * s * deriv r x) * (s * deriv r x)⁻¹ =
    -morseRho A B x * r x / (s * (deriv r x) ^ 2)
  rw [hEq]
  field_simp [hAmplitude.ne', hs.ne', (hv x hx).ne']

/-- The actual logarithmic slope has the same size on both model collars,
despite the different sizes of their speeds and curvatures. -/
theorem morseCollarLogSlope_bounds {A B s v R κ : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hs : 0 < s)
    (hBAlo : A ^ 9 / (9 : ℝ) ^ 9 ≤ B) (hBAhi : B ≤ A ^ 9)
    (hR : (1 / 2 : ℝ) ≤ R ∧ R ≤ 2)
    (hcase : (A / 5 ≤ v ∧ v ≤ 8 * A ∧ (3 / 4 : ℝ) * A ≤ κ ∧ κ ≤ 7 * A) ∨
      (A ^ 5 / 200 ≤ v ∧ v ≤ A ^ 5 / 25 ∧ B / 2 ≤ κ ∧ κ ≤ B)) :
    (100 / (9 : ℝ) ^ 9) / (s * A) ≤ κ * R / (s * v ^ 2) ∧
      κ * R / (s * v ^ 2) ≤ 100000 / (s * A) := by
  have hv : 0 < v := by
    rcases hcase with h | h
    · exact (by positivity : 0 < A / 5).trans_le h.1
    · exact (by positivity : 0 < A ^ 5 / 200).trans_le h.1
  have hRp : 0 ≤ R := by linarith only [hR.1]
  have hbase :
      (100 / (9 : ℝ) ^ 9) / A ≤ κ * R / v ^ 2 ∧ κ * R / v ^ 2 ≤ 100000 / A := by
    constructor
    · apply (le_div_iff₀ (pow_pos hv 2)).mpr
      rcases hcase with ⟨_, hV, hκ, _⟩ | ⟨_, hV, hκ, _⟩
      · calc
          _ ≤ ((100 / (9 : ℝ) ^ 9) / A) * (8 * A) ^ 2 :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hv.le hV 2) (by positivity)
          _ = (6400 / (9 : ℝ) ^ 9) * A := by
            field_simp [hA.ne']
            ring
          _ ≤ (3 / 8 : ℝ) * A := mul_le_mul_of_nonneg_right (by norm_num) hA.le
          _ = ((3 / 4 : ℝ) * A) * (1 / 2) := by ring
          _ ≤ _ := mul_le_mul hκ hR.1 (by norm_num) (hκ.trans' (by positivity))
      · calc
          _ ≤ ((100 / (9 : ℝ) ^ 9) / A) * (A ^ 5 / 25) ^ 2 :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hv.le hV 2) (by positivity)
          _ = (4 / 25 : ℝ) * (A ^ 9 / (9 : ℝ) ^ 9) := by
            field_simp [hA.ne']
            ring
          _ ≤ (1 / 4 : ℝ) * B :=
            mul_le_mul (by norm_num) hBAlo (by positivity) (by norm_num)
          _ = (B / 2) * (1 / 2) := by ring
          _ ≤ _ := mul_le_mul hκ hR.1 (by norm_num) (hκ.trans' (by positivity))
    · apply (div_le_iff₀ (pow_pos hv 2)).mpr
      rcases hcase with ⟨hV, _, _, hκ⟩ | ⟨hV, _, _, hκ⟩
      · calc
          _ ≤ (7 * A) * 2 := mul_le_mul hκ hR.2 hRp (by positivity)
          _ ≤ 4000 * A := by linarith only [hA]
          _ = (100000 / A) * (A / 5) ^ 2 := by
            field_simp [hA.ne']
            ring
          _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hV 2) (by positivity)
      · calc
          _ ≤ B * 2 := mul_le_mul hκ hR.2 hRp hB.le
          _ ≤ A ^ 9 * 2 := mul_le_mul_of_nonneg_right hBAhi (by norm_num)
          _ ≤ (5 / 2 : ℝ) * A ^ 9 := by nlinarith only [pow_nonneg hA.le 9]
          _ = (100000 / A) * (A ^ 5 / 200) ^ 2 := by
            field_simp [hA.ne']
            ring
          _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hV 2) (by positivity)
  have hscale (q d : ℝ) : q / d / s = q / (s * d) := by
    rw [div_div, mul_comm d s]
  constructor
  · have h := div_le_div_of_nonneg_right hbase.1 hs.le
    rw [hscale (100 / (9 : ℝ) ^ 9) A, hscale (κ * R) (v ^ 2)] at h
    exact h
  · have h := div_le_div_of_nonneg_right hbase.2 hs.le
    rw [hscale (κ * R) (v ^ 2), hscale 100000 A] at h
    exact h

/-- The collar slope exceeds the geometric positivity threshold once the
cell parameter is below a fixed threshold. -/
theorem morseCollarLogSlope_ge_two_div {A s R slope : ℝ}
    (hA : 0 < A) (hAs : A ≤ 25 / (9 : ℝ) ^ 9) (hs : 0 < s)
    (hR : (1 / 2 : ℝ) ≤ R)
    (hSlope : (100 / (9 : ℝ) ^ 9) / (s * A) ≤ slope) :
    2 / (s * R) ≤ slope := by
  have hRp : 0 < R := by linarith only [hR]
  calc
    2 / (s * R) ≤ 4 / s := by
      apply (div_le_iff₀ (mul_pos hs hRp)).mpr
      rw [show 4 / s * (s * R) = 4 * R by field_simp [hs.ne']]
      linarith only [hR]
    _ ≤ (100 / (9 : ℝ) ^ 9) / (s * A) := by
      apply (le_div_iff₀ (mul_pos hs hA)).mpr
      rw [show 4 / s * (s * A) = 4 * A by field_simp [hs.ne']]
      linarith only [hAs]
    _ ≤ slope := hSlope

end ContinuousFlexibility.Radial
