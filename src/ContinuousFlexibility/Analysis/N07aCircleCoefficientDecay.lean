module

public import ContinuousFlexibility.Analysis.SpacesCircleFourierJets
public import ContinuousFlexibility.Analysis.OneHighCircleFourierWeights

/-!
# Actual coefficient tails for the angular block estimate

The Fourier coefficients use the prescribed period π. A bound on the
ordinary angular derivatives gives an inverse-square summable tail after
any fixed polynomial frequency weight. These are coefficient bounds;
the existing Schur theorem will sum the actual operator blocks.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff

theorem n07a_circleFourierCoeff_norm_le {f : ℝ → ℝ} {M : ℝ}
    (hM : ∀ θ, |f θ| ≤ M) (n : ℤ) : ‖circleFourierCoeff f n‖ ≤ M := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := Real.pi)
    (f := fun θ => circleFourierWave (-n) θ * (f θ : ℂ)) (fun θ _ => by
      simpa only [norm_mul, circleFourierWave_norm, Complex.norm_real,
        Real.norm_eq_abs, one_mul] using hM θ)
  rw [sub_zero, abs_of_pos Real.pi_pos,
    intervalIntegral.integral_of_le Real.pi_pos.le] at h
  rw [circleFourierCoeff_integral, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  exact (mul_le_mul_of_nonneg_left h (inv_nonneg.mpr Real.pi_pos.le)).trans_eq
    (by field_simp)

theorem n07a_int_frequency_one_le {n : ℤ} (hn : n ≠ 0) : 1 ≤ |(n : ℝ)| := by
  have h : n ≤ -1 ∨ 1 ≤ n := by omega
  rcases h with h | h
  · have h' : (n : ℝ) ≤ -1 := by exact_mod_cast h
    rw [abs_of_nonpos (by linarith)]
    linarith
  · have h' : (1 : ℝ) ≤ n := by exact_mod_cast h
    rw [abs_of_nonneg (by linarith)]
    exact h'

/-- The zero coefficient is controlled by order zero, and every other
coefficient by the same actual derivative of order `s`. -/
theorem n07a_circleFourierCoeff_weighted_le {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f Real.pi)
    (s : ℕ) {M₀ M : ℝ} (hM₀ : 0 ≤ M₀) (hM : 0 ≤ M)
    (h₀ : ∀ θ, |f θ| ≤ M₀) (hs : ∀ θ, |iteratedDeriv s f θ| ≤ M)
    (n : ℤ) :
    (1 + |(n : ℝ)|) ^ s * ‖circleFourierCoeff f n‖ ≤ M₀ + M := by
  by_cases hn : n = 0
  · subst n
    simpa only [Int.cast_zero, abs_zero, add_zero, one_pow, one_mul] using
      (n07a_circleFourierCoeff_norm_le h₀ 0).trans (le_add_of_nonneg_right hM)
  · have hx := n07a_int_frequency_one_le hn
    calc
      _ ≤ (2 * |(n : ℝ)|) ^ s * ‖circleFourierCoeff f n‖ :=
        mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (by positivity) (by linarith) s) (norm_nonneg _)
      _ = ‖circleFourierCoeff (iteratedDeriv s f) n‖ :=
        (circleFourierCoeff_iteratedDeriv_norm hf hp s n).symm
      _ ≤ M := n07a_circleFourierCoeff_norm_le hs n
      _ ≤ M₀ + M := le_add_of_nonneg_left hM₀

def n07aAngularTail (n : ℤ) : ℝ := 1 / (1 + |(n : ℝ)|) ^ 2

theorem n07aAngularTail_nonneg (n : ℤ) : 0 ≤ n07aAngularTail n := by
  unfold n07aAngularTail
  positivity

theorem n07aAngularTail_neg (n : ℤ) : n07aAngularTail (-n) = n07aAngularTail n := by
  simp only [n07aAngularTail, Int.cast_neg, abs_neg]

theorem n07aAngularTail_summable : Summable n07aAngularTail := by
  have h : Summable (fun n : ℤ => 1 / (1 + (n : ℝ) ^ 2)) := by
    simpa only [one_mul] using summable_circleInverseWeightSq (q := 1) zero_lt_one
  apply h.of_norm_bounded (fun n => ?_)
  rw [Real.norm_of_nonneg (n07aAngularTail_nonneg n)]
  exact one_div_le_one_div_of_le (by positivity)
    (by nlinarith [abs_nonneg (n : ℝ), sq_abs (n : ℝ)])

/-- Only two additional coefficient derivatives are needed for a
summable tail, independently of the requested output angular order. -/
theorem n07a_circleFourierCoeff_tail_le {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f Real.pi)
    (s : ℕ) {M₀ M : ℝ} (hM₀ : 0 ≤ M₀) (hM : 0 ≤ M)
    (h₀ : ∀ θ, |f θ| ≤ M₀) (hs : ∀ θ, |iteratedDeriv (s + 2) f θ| ≤ M)
    (n : ℤ) :
    (1 + |(n : ℝ)|) ^ s * ‖circleFourierCoeff f n‖ ≤
      (M₀ + M) * n07aAngularTail n := by
  have h := n07a_circleFourierCoeff_weighted_le hf hp (s + 2) hM₀ hM h₀ hs n
  have hpos : 0 < (1 + |(n : ℝ)|) ^ 2 := by positivity
  rw [n07aAngularTail, ← div_eq_mul_one_div, le_div_iff₀ hpos]
  simpa only [pow_add, mul_assoc, mul_comm, mul_left_comm] using h

theorem n07aAngularTail_shift_summable (l : ℤ) :
    Summable (fun j : ℕ => n07aAngularTail (l - j)) :=
  n07aAngularTail_summable.comp_injective (by intro i j h; exact_mod_cast sub_right_injective h)

theorem n07aAngularTail_shift_tsum_le (l : ℤ) :
    (∑' j : ℕ, n07aAngularTail (l - j)) ≤ ∑' k : ℤ, n07aAngularTail k := by
  apply tsum_comp_le_tsum_of_inj n07aAngularTail_summable n07aAngularTail_nonneg
  intro i j h
  exact_mod_cast sub_right_injective h

end ContinuousFlexibility.Analysis
