module

public import ContinuousFlexibility.Radial.ReferenceCellSaturation
public import ContinuousFlexibility.Radial.MorseArithmeticGap

/-!
# Negative components and the return margins of model intervals

The geometric input specifies the actual negative intervals, their
computed optical integrals, and their pointwise cell coverage.  The
quadratic irrationality, uniform small divisors, coefficient allowance,
and whole-cell containment are proved here.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real
open ContinuousFlexibility.Statements

/-- Two negative components with an interior point in common coincide.
Only the defining signs and the zero endpoint derivatives are used. -/
theorem negativeRadialComponent_unique_of_mem {D : ReferenceData}
    {l h l' h' r : ℝ}
    (h₁ : NegativeRadialComponent D l h)
    (h₂ : NegativeRadialComponent D l' h')
    (hr₁ : r ∈ Ioo l h) (hr₂ : r ∈ Ioo l' h') :
    l = l' ∧ h = h' := by
  rcases h₁ with ⟨ha, hlh, hb, hzl, hzh, hneg⟩
  rcases h₂ with ⟨ha', hlh', hb', hzl', hzh', hneg'⟩
  constructor
  · apply le_antisymm
    · apply le_of_not_gt
      intro hlt
      have hz := hneg' l ⟨hlt, hr₁.1.trans hr₂.2⟩
      linarith only [hz, hzl]
    · apply le_of_not_gt
      intro hlt
      have hz := hneg l' ⟨hlt, hr₂.1.trans hr₁.2⟩
      linarith only [hz, hzl']
  · apply le_antisymm
    · apply le_of_not_gt
      intro hlt
      have hz := hneg h' ⟨hr₁.1.trans hr₂.2, hlt⟩
      linarith only [hz, hzh']
    · apply le_of_not_gt
      intro hlt
      have hz := hneg' h ⟨hr₂.1.trans hr₁.2, hlt⟩
      linarith only [hz, hzh]

theorem quadraticIrrational_half_inv_sqrt {d : ℕ} (hd : 0 < d)
    (hns : ¬ ∃ k : ℕ, k ^ 2 = d) :
    QuadraticIrrational (1 / (2 * sqrt (d : ℝ))) := by
  have hirr : Irrational (sqrt (d : ℝ)) :=
    irrational_sqrt_natCast_iff.mpr (by
      rintro ⟨k, hk⟩
      exact hns ⟨k, by simpa only [pow_two] using hk.symm⟩)
  have hs : 0 < sqrt (d : ℝ) := sqrt_pos.mpr (by exact_mod_cast hd)
  have hscaled : Irrational (2 * sqrt (d : ℝ)) := by
    simpa only [Int.cast_ofNat] using hirr.intCast_mul (m := 2) (by norm_num)
  refine ⟨?_, 4 * (d : ℤ), 0, -1, ?_, ?_⟩
  · simpa only [one_div] using hscaled.inv
  · exact mul_ne_zero (by norm_num) (by exact_mod_cast hd.ne')
  · norm_num only [Int.cast_mul, Int.cast_ofNat, Int.cast_natCast,
      Int.cast_zero, Int.cast_neg, Int.cast_one, zero_mul, add_zero]
    field_simp [hs.ne'] <;> nlinarith only [sq_sqrt (Nat.cast_nonneg d)]

theorem quadraticIrrational_morseTravelRatio {d : ℕ} (hd : 0 < d)
    (hns : ¬ ∃ k : ℕ, k ^ 2 = d) :
    QuadraticIrrational ((Real.pi / (2 * sqrt (d : ℝ))) / Real.pi) := by
  have hs : sqrt (d : ℝ) ≠ 0 := (sqrt_pos.mpr (by exact_mod_cast hd)).ne'
  rw [show (Real.pi / (2 * sqrt (d : ℝ))) / Real.pi =
      1 / (2 * sqrt (d : ℝ)) by field_simp [pi_ne_zero, hs]]
  exact quadraticIrrational_half_inv_sqrt hd hns

/-- The arithmetic small-divisor loss costs one fixed coefficient power,
uniformly over the actual model labels. -/
theorem morseReturnCoefficient_allowance {n d : ℕ}
    (hn : 1 ≤ n) (hd : 0 < d)
    (hsize : (d : ℝ) ≤ exp ((n : ℝ) ^ 2) + 2) :
    3 * sqrt (d : ℝ) ≤ radialE n ^ (10 : ℝ) := by
  have hd₁ : (1 : ℝ) ≤ d := by exact_mod_cast (Nat.succ_le_iff.mpr hd)
  have hsqrt : sqrt (d : ℝ) ≤ d := by
    apply sqrt_le_iff.mpr
    exact ⟨Nat.cast_nonneg d, by
      nlinarith only [mul_nonneg (Nat.cast_nonneg d) (sub_nonneg.mpr hd₁)]⟩
  have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn₂ : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith only [hn₁]
  have hexp : 1 ≤ exp ((n : ℝ) ^ 2) :=
    one_le_exp_iff.mpr (sq_nonneg (n : ℝ))
  have hbig : 9 ≤ exp (9 * (n : ℝ) ^ 2) := by
    have h := add_one_le_exp (9 * (n : ℝ) ^ 2)
    linarith only [h, hn₂]
  calc
    3 * sqrt (d : ℝ) ≤ 3 * (d : ℝ) :=
      mul_le_mul_of_nonneg_left hsqrt (by norm_num)
    _ ≤ 9 * exp ((n : ℝ) ^ 2) := by linarith only [hsize, hexp]
    _ ≤ exp (9 * (n : ℝ) ^ 2) * exp ((n : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right hbig (exp_pos _).le
    _ = exp (10 * (n : ℝ) ^ 2) := by
      rw [← exp_add]
      congr 1
      ring
    _ ≤ exp (10 * radialQ n) :=
      exp_le_exp.mpr (mul_le_mul_of_nonneg_left (radial_nat_sq_le_Q n) (by norm_num))
    _ = radialE n ^ (10 : ℝ) := by
      rw [radialE, ← exp_mul]
      congr 1
      ring

private theorem inverse_three_sqrt_div (d k : ℕ) :
    (3 * sqrt (d : ℝ))⁻¹ / (k : ℝ) =
      (3 * (k : ℝ) * sqrt (d : ℝ))⁻¹ := by
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- A cover by actual model components suffices for every return-margin
clause. Whole-cell containment is obtained by the explicit cell completion,
rather than included among the hypotheses. -/
theorem radialReturnMargins_saturate_of_model_components {D : ReferenceData}
    (hmodels : ∀ r ∈ radialCore D, deriv D.w r < 0 →
      ∃ l h : ℝ, ∃ n d : ℕ,
        NegativeRadialComponent D l h ∧ r ∈ Ioo l h ∧
        1 ≤ n ∧ 0 < d ∧ (¬ ∃ k : ℕ, k ^ 2 = d) ∧
        (d : ℝ) ≤ exp ((n : ℝ) ^ 2) + 2 ∧
        radialTravel D l h = Real.pi / (2 * sqrt (d : ℝ)) ∧
        ∀ t ∈ Ioo l h, ∃ m, D.cellIndex m = n ∧ t ∈ D.cells m) :
    RadialReturnMargins (saturateReferenceCells D) := by
  constructor
  · intro r hr hder
    obtain ⟨l, h, n, d, hneg, hrI, hrest⟩ := hmodels r hr hder
    exact ⟨l, h, hneg, hrI⟩
  · refine ⟨10, by norm_num, ?_⟩
    intro l h hneg
    have hnegD : NegativeRadialComponent D l h := hneg
    have hmid : (l + h) / 2 ∈ Ioo l h := by
      constructor <;> linarith only [hnegD.2.1]
    have hmidCore : (l + h) / 2 ∈ radialCore D :=
      ⟨hnegD.1.trans hmid.1, hmid.2.trans hnegD.2.2.1⟩
    obtain ⟨l', h', n, d, hmodel, hmem, hn, hd, hns, hsize, htravel, hcover⟩ :=
      hmodels ((l + h) / 2) hmidCore (hnegD.2.2.2.2.2 _ hmid)
    obtain ⟨hl, hh⟩ := negativeRadialComponent_unique_of_mem hnegD hmodel hmid hmem
    subst l'
    subst h'
    obtain ⟨m, hm, hcell⟩ := saturateReferenceCells_covers_interval hnegD.2.1 hcover
    refine ⟨?_, m, hcell, (3 * sqrt (d : ℝ))⁻¹, ?_, ?_, ?_⟩
    · change QuadraticIrrational (radialTravel D l h / Real.pi)
      rw [htravel]
      exact quadraticIrrational_morseTravelRatio hd hns
    · exact inv_pos.mpr (mul_pos (by norm_num) (sqrt_pos.mpr (by exact_mod_cast hd)))
    · change ((3 * sqrt (d : ℝ))⁻¹)⁻¹ ≤ radialE (D.cellIndex m) ^ (10 : ℝ)
      rw [inv_inv, hm]
      exact morseReturnCoefficient_allowance hn hd hsize
    · intro k hk
      change (3 * sqrt (d : ℝ))⁻¹ / (k : ℝ) ≤
        |sin ((k : ℝ) * radialTravel D l h)|
      rw [htravel]
      rw [inverse_three_sqrt_div]
      exact morse_return_small_divisor hd hns hk

end ContinuousFlexibility.Radial
