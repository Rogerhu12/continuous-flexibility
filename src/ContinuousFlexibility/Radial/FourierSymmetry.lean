import ContinuousFlexibility.Radial.FourierSineOrthogonality
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Actual Fourier moment cancellations from the radial symmetries

Evenness removes every sine moment. Half-turn periodicity removes the odd
cosine moments. Consequently a zero angular mean and zero positive even
cosine coefficients give zero cosine moments at every integer frequency.
These are integral identities; L² completeness is a separate step.
-/

namespace ContinuousFlexibility.Radial

noncomputable section

open MeasureTheory

theorem integral_eq_zero_of_angular_reflection_neg {g : ℝ → ℝ}
    (hg : ∀ θ, g (2 * Real.pi - θ) = -g θ) :
    (∫ θ in (0 : ℝ)..2 * Real.pi, g θ) = 0 := by
  have hreflect :
      (∫ θ in (0 : ℝ)..2 * Real.pi, g (2 * Real.pi - θ)) =
        ∫ θ in (0 : ℝ)..2 * Real.pi, g θ := by
    rw [intervalIntegral.integral_comp_sub_left]
    simp only [sub_self, sub_zero]
  have hneg :
      (∫ θ in (0 : ℝ)..2 * Real.pi, g (2 * Real.pi - θ)) =
        -(∫ θ in (0 : ℝ)..2 * Real.pi, g θ) := by
    calc
      _ = ∫ θ in (0 : ℝ)..2 * Real.pi, -g θ := by
        apply intervalIntegral.integral_congr
        intro θ _
        exact hg θ
      _ = _ := by rw [intervalIntegral.integral_neg]
  linarith

theorem integral_eq_zero_of_half_turn_neg {g : ℝ → ℝ}
    (hg : ∀ θ, g (θ + Real.pi) = -g θ) :
    (∫ θ in (0 : ℝ)..2 * Real.pi, g θ) = 0 := by
  have hp : Function.Periodic g (2 * Real.pi) := by
    intro θ
    calc
      g (θ + 2 * Real.pi) = g ((θ + Real.pi) + Real.pi) :=
        congrArg g (by ring)
      _ = -g (θ + Real.pi) := hg (θ + Real.pi)
      _ = g θ := by rw [hg θ, neg_neg]
  have hshift :
      (∫ θ in (0 : ℝ)..2 * Real.pi, g (θ + Real.pi)) =
        ∫ θ in (0 : ℝ)..2 * Real.pi, g θ := by
    rw [intervalIntegral.integral_comp_add_right]
    simpa only [zero_add, add_comm] using hp.intervalIntegral_add_eq Real.pi 0
  have hneg :
      (∫ θ in (0 : ℝ)..2 * Real.pi, g (θ + Real.pi)) =
        -(∫ θ in (0 : ℝ)..2 * Real.pi, g θ) := by
    calc
      _ = ∫ θ in (0 : ℝ)..2 * Real.pi, -g θ := by
        apply intervalIntegral.integral_congr
        intro θ _
        exact hg θ
      _ = _ := by rw [intervalIntegral.integral_neg]
  linarith

theorem integral_mul_sin_int_eq_zero_of_even_periodic {f : ℝ → ℝ}
    (heven : Function.Even f) (hperiodic : Function.Periodic f Real.pi) (n : ℤ) :
    (∫ θ in (0 : ℝ)..2 * Real.pi, f θ * Real.sin ((n : ℝ) * θ)) = 0 := by
  have hreflect (θ : ℝ) : f (2 * Real.pi - θ) = f θ := by
    calc
      _ = f ((-θ + Real.pi) + Real.pi) := congrArg f (by ring)
      _ = f (-θ + Real.pi) := hperiodic (-θ + Real.pi)
      _ = f (-θ) := hperiodic (-θ)
      _ = f θ := heven θ
  apply integral_eq_zero_of_angular_reflection_neg
  intro θ
  change f (2 * Real.pi - θ) * Real.sin ((n : ℝ) * (2 * Real.pi - θ)) =
    -(f θ * Real.sin ((n : ℝ) * θ))
  rw [hreflect θ, mul_sub, Real.sin_int_mul_two_pi_sub]
  ring

theorem integral_mul_cos_nat_eq_zero_of_periodic_odd {f : ℝ → ℝ}
    (hperiodic : Function.Periodic f Real.pi) (n : ℕ) (hn : Odd n) :
    (∫ θ in (0 : ℝ)..2 * Real.pi, f θ * Real.cos ((n : ℝ) * θ)) = 0 := by
  apply integral_eq_zero_of_half_turn_neg
  intro θ
  change f (θ + Real.pi) * Real.cos ((n : ℝ) * (θ + Real.pi)) =
    -(f θ * Real.cos ((n : ℝ) * θ))
  rw [hperiodic θ, mul_add, Real.cos_add_nat_mul_pi, hn.neg_one_pow]
  ring

theorem integral_eq_zero_of_angularAverage_eq_zero {f : ℝ → ℝ}
    (hf : angularAverage f = 0) :
    (∫ θ in (0 : ℝ)..2 * Real.pi, f θ) = 0 := by
  change (1 / (2 * Real.pi)) * (∫ θ in (0 : ℝ)..2 * Real.pi, f θ) = 0 at hf
  exact (mul_eq_zero.mp hf).resolve_left (by positivity)

theorem angularPairing_cosineMode_eq_scaled_integral (f : ℝ → ℝ) (j : ℕ) :
    angularPairing f (cosineMode j) =
      (Real.sqrt 2 / (2 * Real.pi)) *
        ∫ θ in (0 : ℝ)..2 * Real.pi, f θ * Real.cos ((j : ℝ) * θ) := by
  change (1 / (2 * Real.pi)) *
      (∫ θ in (0 : ℝ)..2 * Real.pi, f θ * (Real.sqrt 2 * Real.cos ((j : ℝ) * θ))) = _
  have hmul : (fun θ : ℝ => f θ * (Real.sqrt 2 * Real.cos ((j : ℝ) * θ))) =
      (fun θ : ℝ => Real.sqrt 2 * (f θ * Real.cos ((j : ℝ) * θ))) := by
    funext θ
    ring
  rw [hmul, intervalIntegral.integral_const_mul]
  ring

theorem integral_mul_cos_nat_eq_zero_of_pairing_zero {f : ℝ → ℝ} {j : ℕ}
    (hf : angularPairing f (cosineMode j) = 0) :
    (∫ θ in (0 : ℝ)..2 * Real.pi, f θ * Real.cos ((j : ℝ) * θ)) = 0 := by
  rw [angularPairing_cosineMode_eq_scaled_integral] at hf
  exact (mul_eq_zero.mp hf).resolve_left (by positivity)

theorem integral_mul_cos_int_eq_zero_of_even_coefficients {f : ℝ → ℝ}
    (hperiodic : Function.Periodic f Real.pi) (hmean : angularAverage f = 0)
    (hcoeff : ∀ j : ℕ, 0 < j → Even j → angularPairing f (cosineMode j) = 0) :
    ∀ n : ℤ, (∫ θ in (0 : ℝ)..2 * Real.pi, f θ * Real.cos ((n : ℝ) * θ)) = 0 := by
  have hnat (j : ℕ) :
      (∫ θ in (0 : ℝ)..2 * Real.pi, f θ * Real.cos ((j : ℝ) * θ)) = 0 := by
    by_cases hj : j = 0
    · subst j
      simpa only [Nat.cast_zero, zero_mul, Real.cos_zero, mul_one] using
        integral_eq_zero_of_angularAverage_eq_zero hmean
    · by_cases he : Even j
      · exact integral_mul_cos_nat_eq_zero_of_pairing_zero
          (hcoeff j (Nat.pos_of_ne_zero hj) he)
      · exact integral_mul_cos_nat_eq_zero_of_periodic_odd hperiodic j
          (Nat.not_even_iff_odd.mp he)
  intro n
  obtain ⟨j, rfl | rfl⟩ := n.eq_nat_or_neg
  · simpa only [Int.cast_natCast] using hnat j
  · simpa only [Int.cast_neg, Int.cast_natCast, neg_mul, Real.cos_neg] using hnat j

end

end ContinuousFlexibility.Radial
