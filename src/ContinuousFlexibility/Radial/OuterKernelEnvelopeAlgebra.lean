import ContinuousFlexibility.Radial.OuterLocalizationWeights

/-!
# Algebra of uniform localized Green envelopes

Fixed numerical prefactors and bounded label shifts only change a fixed
power of the coefficient weights. Products of two decays from the same
entrance retain the full attenuation between their two endpoints.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real
open ContinuousFlexibility.Statements

theorem outer_envelope_exponent_mono (n : ℕ) {A B : ℝ} (h : A ≤ B) :
    radialE n ^ A ≤ radialE n ^ B := by
  rw [outer_radialE_rpow, outer_radialE_rpow]
  exact exp_le_exp.mpr (mul_le_mul_of_nonneg_right h (radialQ_nonneg n))

theorem outer_envelope_index_mono {m n : ℕ} (hmn : m ≤ n) {A : ℝ} (hA : 0 ≤ A) :
    radialE m ^ A ≤ radialE n ^ A := by
  rw [outer_radialE_rpow, outer_radialE_rpow]
  exact exp_le_exp.mpr (mul_le_mul_of_nonneg_left (radialQ_monotone hmn) hA)

theorem outer_envelope_one_le (n : ℕ) {A : ℝ} (hA : 0 ≤ A) : 1 ≤ radialE n ^ A := by
  rw [outer_radialE_rpow]
  exact one_le_exp_iff.mpr (mul_nonneg hA (radialQ_nonneg n))

theorem outer_envelope_prefactor {n : ℕ} (hn : 1 ≤ n) {P A : ℝ} (hP : 0 ≤ P) :
    P * radialE n ^ A ≤ radialE n ^ (P + A) := by
  calc
    _ ≤ radialE n ^ P * radialE n ^ A :=
      mul_le_mul_of_nonneg_right (outer_prefactor_le_envelope hn hP)
        (rpow_nonneg (show 0 ≤ radialE n from (exp_pos _).le) _)
    _ = _ := (rpow_add (show 0 < radialE n from exp_pos _) P A).symm

theorem outer_envelope_sum {n : ℕ} (hn : 1 ≤ n) {A B : ℝ} :
    radialE n ^ A + radialE n ^ B ≤ radialE n ^ (2 + max A B) := by
  calc
    _ ≤ radialE n ^ max A B + radialE n ^ max A B :=
      add_le_add (outer_envelope_exponent_mono n (le_max_left _ _))
        (outer_envelope_exponent_mono n (le_max_right _ _))
    _ = 2 * radialE n ^ max A B := by ring
    _ ≤ _ := outer_envelope_prefactor hn (by norm_num)

theorem outer_envelope_pair_prefactor {m n : ℕ} (hm : 1 ≤ m)
    {P A B : ℝ} (hP : 0 ≤ P) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    P * radialE m ^ A * radialE n ^ B ≤
      radialE m ^ (P + A + B) * radialE n ^ (P + A + B) := by
  apply mul_le_mul
    ((outer_envelope_prefactor hm hP).trans
      (outer_envelope_exponent_mono m (by linarith)))
    (outer_envelope_exponent_mono n (by linarith))
    (rpow_nonneg (show 0 ≤ radialE n from (exp_pos _).le) _)
    (rpow_nonneg (show 0 ≤ radialE m from (exp_pos _).le) _)

theorem outer_attenuation_product_le (p q base : ℕ) :
    exp (-|radialS p - radialS base|) * exp (-|radialS q - radialS base|) ≤
      exp (-|radialS p - radialS q|) := by
  rw [← exp_add]
  apply exp_le_exp.mpr
  have h := abs_sub_le (radialS p) (radialS base) (radialS q)
  rw [abs_sub_comm (radialS base) (radialS q)] at h
  linarith only [h]

/-- The actual two-label displacement preserves the manuscript exponent. -/
theorem outer_localized_envelope_shift {A : ℝ} (hA : 0 ≤ A) :
    ∃ B : ℝ, 0 < B ∧ ∀ p q i k : ℕ,
      1 ≤ p → 1 ≤ q → 1 ≤ i → 1 ≤ k →
      p ≤ i + 2 → i ≤ p + 2 → q ≤ k + 2 → k ≤ q + 2 →
      radialE p ^ A * radialE q ^ A * exp (-|radialS p - radialS q|) ≤
        radialE i ^ B * radialE k ^ B * exp (-|radialS i - radialS k|) := by
  obtain ⟨B, hB, hshift⟩ := outer_coefficient_weight_nearby hA
  refine ⟨B + 18, by linarith, ?_⟩
  intro p q i k hp hq hi hk hpi hip hqk hkq
  have hw := mul_le_mul (hshift p i hi hpi) (hshift q k hk hqk)
    (rpow_nonneg (show 0 ≤ radialE q from (exp_pos _).le) _)
    (rpow_nonneg (show 0 ≤ radialE i from (exp_pos _).le) _)
  have hd := outer_attenuation_nearby hp hq hi hk hpi hip hqk hkq
  calc
    _ ≤ (radialE i ^ B * radialE k ^ B) *
        (radialE i ^ (18 : ℝ) * radialE k ^ (18 : ℝ) *
          exp (-|radialS i - radialS k|)) :=
      mul_le_mul hw hd (exp_pos _).le
        (mul_nonneg (rpow_nonneg (show 0 ≤ radialE i from (exp_pos _).le) _)
          (rpow_nonneg (show 0 ≤ radialE k from (exp_pos _).le) _))
    _ = _ := by
      rw [rpow_add (show 0 < radialE i from exp_pos _) B 18,
        rpow_add (show 0 < radialE k from exp_pos _) B 18]
      ring

theorem outer_kernel_cutoff_bound {φ ψ : ℝ → ℝ} {K : ℝ → ℝ → ℝ} {B : ℝ}
    (hB : 0 ≤ B) (hφ : ∀ x, |φ x| ≤ 1) (hψ : ∀ y, |ψ y| ≤ 1)
    (hK : ∀ x y, φ x ≠ 0 → ψ y ≠ 0 → |K x y| ≤ B) (x y : ℝ) :
    |φ x * K x y * ψ y| ≤ B := by
  by_cases hx : φ x = 0
  · simpa only [hx, zero_mul, abs_zero] using hB
  by_cases hy : ψ y = 0
  · simpa only [hy, mul_zero, abs_zero] using hB
  calc
    _ = (|φ x| * |ψ y|) * |K x y| := by simp only [abs_mul]; ring
    _ ≤ (1 * 1) * B := mul_le_mul
      (mul_le_mul (hφ x) (hψ y) (abs_nonneg _) zero_le_one)
      (hK x y hx hy) (abs_nonneg _) (by norm_num)
    _ = B := by ring

end ContinuousFlexibility.Radial
