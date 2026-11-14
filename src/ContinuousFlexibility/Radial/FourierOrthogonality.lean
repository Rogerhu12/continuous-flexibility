module

public import ContinuousFlexibility.Radial.FourierModes
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-!
# Normalized angular pairings for the real cosine sector

The normalization is the actual integral `(2π)⁻¹ ∫[0,2π]`, not a
formal coefficient functional. Infinite Fourier completeness and the
weighted endpoint source spaces remain separate obligations.
-/

@[expose] public section

namespace ContinuousFlexibility.Radial

noncomputable section

open MeasureTheory

def angularAverage (f : ℝ → ℝ) : ℝ :=
  1 / (2 * Real.pi) * ∫ θ in (0 : ℝ)..2 * Real.pi, f θ

def angularPairing (f g : ℝ → ℝ) : ℝ :=
  angularAverage (fun θ => f θ * g θ)

/-- Integer cosine frequencies have zero unnormalized angular integral. -/
theorem integral_cos_int_frequency (m : ℤ) (hm : m ≠ 0) :
    (∫ θ in (0 : ℝ)..2 * Real.pi, Real.cos ((m : ℝ) * θ)) = 0 := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  rw [intervalIntegral.integral_comp_mul_left (fun t : ℝ => Real.cos t) hmR]
  simp only [mul_zero, integral_cos, Real.sin_zero, sub_zero, smul_eq_mul]
  have hphase : (m : ℝ) * (2 * Real.pi) = ((2 * m : ℤ) : ℝ) * Real.pi := by
    push_cast
    ring
  rw [hphase, Real.sin_int_mul_pi, mul_zero]

theorem integral_cosineMode (j : ℕ) (hj : 0 < j) :
    (∫ θ in (0 : ℝ)..2 * Real.pi, cosineMode j θ) = 0 := by
  unfold cosineMode
  rw [intervalIntegral.integral_const_mul]
  have hjZ : (j : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hj)
  have hzero : (∫ θ in (0 : ℝ)..2 * Real.pi, Real.cos ((j : ℝ) * θ)) = 0 := by
    simpa only [Int.cast_natCast] using integral_cos_int_frequency (j : ℤ) hjZ
  rw [hzero, mul_zero]

theorem angularAverage_cosineMode (j : ℕ) (hj : 0 < j) :
    angularAverage (cosineMode j) = 0 := by
  unfold angularAverage
  rw [integral_cosineMode j hj, mul_zero]

/-- The factor `sqrt 2` makes the product-to-sum formula have unit coefficients. -/
theorem cosineMode_product_formula (j k : ℕ) (θ : ℝ) :
    cosineMode j θ * cosineMode k θ =
      Real.cos ((((j : ℤ) - (k : ℤ) : ℤ) : ℝ) * θ) +
        Real.cos ((((j : ℤ) + (k : ℤ) : ℤ) : ℝ) * θ) := by
  calc
    _ = Real.sqrt 2 ^ 2 *
        (Real.cos ((j : ℝ) * θ) * Real.cos ((k : ℝ) * θ)) := by
      unfold cosineMode
      ring
    _ = 2 * (Real.cos ((j : ℝ) * θ) * Real.cos ((k : ℝ) * θ)) := by
      rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    _ = _ := by
      push_cast
      rw [sub_mul, add_mul, Real.cos_sub, Real.cos_add]
      ring

theorem integral_cosineMode_product_of_ne (j k : ℕ)
    (hj : 0 < j) (hk : 0 < k) (hjk : j ≠ k) :
    (∫ θ in (0 : ℝ)..2 * Real.pi, cosineMode j θ * cosineMode k θ) = 0 := by
  have hdiff : (j : ℤ) - (k : ℤ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hjk)
  have hsum : (j : ℤ) + (k : ℤ) ≠ 0 := by
    have hjZ : (0 : ℤ) < j := by exact_mod_cast hj
    have hkZ : (0 : ℤ) < k := by exact_mod_cast hk
    linarith
  have hcont (m : ℤ) : Continuous (fun θ : ℝ => Real.cos ((m : ℝ) * θ)) :=
    Real.continuous_cos.comp (continuous_const.mul continuous_id)
  calc
    _ = ∫ θ in (0 : ℝ)..2 * Real.pi,
        Real.cos ((((j : ℤ) - (k : ℤ) : ℤ) : ℝ) * θ) +
          Real.cos ((((j : ℤ) + (k : ℤ) : ℤ) : ℝ) * θ) := by
      apply intervalIntegral.integral_congr
      intro θ _
      exact cosineMode_product_formula j k θ
    _ = _ := by
      rw [intervalIntegral.integral_add ((hcont _).intervalIntegrable _ _)
          ((hcont _).intervalIntegrable _ _),
        integral_cos_int_frequency _ hdiff, integral_cos_int_frequency _ hsum]
      ring

theorem integral_cosineMode_product_self (j : ℕ) (hj : 0 < j) :
    (∫ θ in (0 : ℝ)..2 * Real.pi, cosineMode j θ * cosineMode j θ) =
      2 * Real.pi := by
  have hsum : (j : ℤ) + (j : ℤ) ≠ 0 := by
    have hjZ : (0 : ℤ) < j := by exact_mod_cast hj
    linarith
  have hcont : Continuous
      (fun θ : ℝ => Real.cos ((((j : ℤ) + (j : ℤ) : ℤ) : ℝ) * θ)) :=
    Real.continuous_cos.comp (continuous_const.mul continuous_id)
  calc
    _ = ∫ θ in (0 : ℝ)..2 * Real.pi,
        1 + Real.cos ((((j : ℤ) + (j : ℤ) : ℤ) : ℝ) * θ) := by
      apply intervalIntegral.integral_congr
      intro θ _
      change cosineMode j θ * cosineMode j θ =
        1 + Real.cos ((((j : ℤ) + (j : ℤ) : ℤ) : ℝ) * θ)
      rw [cosineMode_product_formula]
      simp only [sub_self, Int.cast_zero, zero_mul, Real.cos_zero]
    _ = _ := by
      rw [intervalIntegral.integral_add (continuous_const.intervalIntegrable _ _)
          (hcont.intervalIntegrable _ _), integral_cos_int_frequency _ hsum]
      simp

/-- Actual normalized angular orthogonality of all positive cosine modes. -/
theorem angularPairing_cosineMode (j k : ℕ) (hj : 0 < j) (hk : 0 < k) :
    angularPairing (cosineMode j) (cosineMode k) = if j = k then 1 else 0 := by
  by_cases h : j = k
  · subst k
    simp only [ite_true]
    unfold angularPairing angularAverage
    rw [integral_cosineMode_product_self j hj]
    field_simp [Real.pi_ne_zero]
  · rw [ite_eq_right h]
    unfold angularPairing angularAverage
    rw [integral_cosineMode_product_of_ne j k hj hk h, mul_zero]

end

end ContinuousFlexibility.Radial
