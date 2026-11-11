import ContinuousFlexibility.Radial.FourierOrthogonality

/-!
# Normalized real sine modes and their angular orthogonality

The normalization agrees with the existing cosine modes and the actual
angular average. Positive sine modes have unit square average and are
mutually orthogonal. Their pairings with all cosine modes vanish.
-/

namespace ContinuousFlexibility.Radial

noncomputable section

open MeasureTheory

def sineMode (j : ℕ) (θ : ℝ) : ℝ :=
  Real.sqrt 2 * Real.sin ((j : ℝ) * θ)

theorem continuous_sineMode (j : ℕ) : Continuous (sineMode j) :=
  continuous_const.mul (Real.continuous_sin.comp (continuous_const.mul continuous_id))

theorem sineMode_odd (j : ℕ) : Function.Odd (sineMode j) := by
  intro θ
  unfold sineMode
  rw [mul_neg, Real.sin_neg, mul_neg]

theorem cosineModeFirst_eq_neg_mul_sineMode (j : ℕ) (θ : ℝ) :
    cosineModeFirst j θ = -(j : ℝ) * sineMode j θ := by
  unfold cosineModeFirst sineMode
  ring

theorem integral_sin_int_frequency (m : ℤ) :
    (∫ θ in (0 : ℝ)..2 * Real.pi, Real.sin ((m : ℝ) * θ)) = 0 := by
  by_cases hm : m = 0
  · simp [hm]
  · have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm
    rw [intervalIntegral.integral_comp_mul_left (fun t : ℝ => Real.sin t) hmR]
    simp only [mul_zero, integral_sin, Real.cos_zero, Real.cos_int_mul_two_pi,
      sub_self, smul_eq_mul, mul_zero]

theorem integral_sineMode (j : ℕ) :
    (∫ θ in (0 : ℝ)..2 * Real.pi, sineMode j θ) = 0 := by
  unfold sineMode
  rw [intervalIntegral.integral_const_mul]
  have hzero : (∫ θ in (0 : ℝ)..2 * Real.pi, Real.sin ((j : ℝ) * θ)) = 0 := by
    simpa only [Int.cast_natCast] using integral_sin_int_frequency (j : ℤ)
  rw [hzero, mul_zero]

theorem angularAverage_sineMode (j : ℕ) : angularAverage (sineMode j) = 0 := by
  unfold angularAverage
  rw [integral_sineMode j, mul_zero]

theorem sineMode_product_formula (j k : ℕ) (θ : ℝ) :
    sineMode j θ * sineMode k θ =
      Real.cos ((((j : ℤ) - (k : ℤ) : ℤ) : ℝ) * θ) -
        Real.cos ((((j : ℤ) + (k : ℤ) : ℤ) : ℝ) * θ) := by
  calc
    _ = Real.sqrt 2 ^ 2 *
        (Real.sin ((j : ℝ) * θ) * Real.sin ((k : ℝ) * θ)) := by
      unfold sineMode
      ring
    _ = 2 * (Real.sin ((j : ℝ) * θ) * Real.sin ((k : ℝ) * θ)) := by
      rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    _ = _ := by
      push_cast
      rw [sub_mul, add_mul, Real.cos_sub, Real.cos_add]
      ring

theorem integral_sineMode_product_of_ne (j k : ℕ)
    (hj : 0 < j) (hk : 0 < k) (hjk : j ≠ k) :
    (∫ θ in (0 : ℝ)..2 * Real.pi, sineMode j θ * sineMode k θ) = 0 := by
  have hdiff : (j : ℤ) - (k : ℤ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hjk)
  have hsum : (j : ℤ) + (k : ℤ) ≠ 0 := by
    have hjZ : (0 : ℤ) < j := by exact_mod_cast hj
    have hkZ : (0 : ℤ) < k := by exact_mod_cast hk
    linarith
  have hcont (m : ℤ) : Continuous (fun θ : ℝ => Real.cos ((m : ℝ) * θ)) :=
    Real.continuous_cos.comp (continuous_const.mul continuous_id)
  calc
    _ = ∫ θ in (0 : ℝ)..2 * Real.pi,
        Real.cos ((((j : ℤ) - (k : ℤ) : ℤ) : ℝ) * θ) -
          Real.cos ((((j : ℤ) + (k : ℤ) : ℤ) : ℝ) * θ) := by
      apply intervalIntegral.integral_congr
      intro θ _
      exact sineMode_product_formula j k θ
    _ = _ := by
      rw [intervalIntegral.integral_sub ((hcont _).intervalIntegrable _ _)
          ((hcont _).intervalIntegrable _ _),
        integral_cos_int_frequency _ hdiff, integral_cos_int_frequency _ hsum]
      ring

theorem integral_sineMode_product_self (j : ℕ) (hj : 0 < j) :
    (∫ θ in (0 : ℝ)..2 * Real.pi, sineMode j θ * sineMode j θ) =
      2 * Real.pi := by
  have hsum : (j : ℤ) + (j : ℤ) ≠ 0 := by
    have hjZ : (0 : ℤ) < j := by exact_mod_cast hj
    linarith
  have hcont : Continuous
      (fun θ : ℝ => Real.cos ((((j : ℤ) + (j : ℤ) : ℤ) : ℝ) * θ)) :=
    Real.continuous_cos.comp (continuous_const.mul continuous_id)
  calc
    _ = ∫ θ in (0 : ℝ)..2 * Real.pi,
        1 - Real.cos ((((j : ℤ) + (j : ℤ) : ℤ) : ℝ) * θ) := by
      apply intervalIntegral.integral_congr
      intro θ _
      rw [sineMode_product_formula]
      simp only [sub_self, Int.cast_zero, zero_mul, Real.cos_zero]
    _ = _ := by
      rw [intervalIntegral.integral_sub (continuous_const.intervalIntegrable _ _)
          (hcont.intervalIntegrable _ _), integral_cos_int_frequency _ hsum]
      simp

theorem angularPairing_sineMode (j k : ℕ) (hj : 0 < j) (hk : 0 < k) :
    angularPairing (sineMode j) (sineMode k) = if j = k then 1 else 0 := by
  by_cases h : j = k
  · subst k
    simp only [ite_true]
    unfold angularPairing angularAverage
    rw [integral_sineMode_product_self j hj]
    field_simp [Real.pi_ne_zero]
  · rw [ite_eq_right h]
    unfold angularPairing angularAverage
    rw [integral_sineMode_product_of_ne j k hj hk h, mul_zero]

theorem cosineMode_sineMode_product_formula (j k : ℕ) (θ : ℝ) :
    cosineMode j θ * sineMode k θ =
      Real.sin ((((k : ℤ) + (j : ℤ) : ℤ) : ℝ) * θ) +
        Real.sin ((((k : ℤ) - (j : ℤ) : ℤ) : ℝ) * θ) := by
  calc
    _ = Real.sqrt 2 ^ 2 *
        (Real.cos ((j : ℝ) * θ) * Real.sin ((k : ℝ) * θ)) := by
      unfold cosineMode sineMode
      ring
    _ = 2 * (Real.cos ((j : ℝ) * θ) * Real.sin ((k : ℝ) * θ)) := by
      rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    _ = _ := by
      push_cast
      rw [add_mul, sub_mul, Real.sin_add, Real.sin_sub]
      ring

theorem angularPairing_cosineMode_sineMode (j k : ℕ) :
    angularPairing (cosineMode j) (sineMode k) = 0 := by
  have hcont (m : ℤ) : Continuous (fun θ : ℝ => Real.sin ((m : ℝ) * θ)) :=
    Real.continuous_sin.comp (continuous_const.mul continuous_id)
  have hzero : (∫ θ in (0 : ℝ)..2 * Real.pi, cosineMode j θ * sineMode k θ) = 0 := by
    calc
      _ = ∫ θ in (0 : ℝ)..2 * Real.pi,
          Real.sin ((((k : ℤ) + (j : ℤ) : ℤ) : ℝ) * θ) +
            Real.sin ((((k : ℤ) - (j : ℤ) : ℤ) : ℝ) * θ) := by
        apply intervalIntegral.integral_congr
        intro θ _
        exact cosineMode_sineMode_product_formula j k θ
      _ = _ := by
        rw [intervalIntegral.integral_add ((hcont _).intervalIntegrable _ _)
            ((hcont _).intervalIntegrable _ _),
          integral_sin_int_frequency, integral_sin_int_frequency]
        ring
  unfold angularPairing angularAverage
  rw [hzero, mul_zero]

end

end ContinuousFlexibility.Radial
