import ContinuousFlexibility.Radial.InnerUniformSuppression
import ContinuousFlexibility.Radial.InnerCoefficientWeights
import ContinuousFlexibility.Radial.MorseJoinHeightContrast

/-!
# Frequency-uniform choices, including the Poisson remainder

The extra frequency factor is retained before choosing the first cell.
Consequently a small remainder contributes at most a constant divided by
the frequency, even though the bands have no global upper frequency bound.
The logarithmic frequency comparison is proved from the actual Morse
parameters, rather than assumed as an additional estimate.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Filter Real ContinuousFlexibility.Statements
open scoped Topology

/-- The actual Morse action controls the frequency logarithm with one
fixed coefficient loss. -/
theorem inner_morse_frequency_log_bound (T : MorseChainData) {m : ℕ}
    (hd : T.d m = morseChainInteger m) (hm : 1 ≤ m) {j : ℝ} (hj : 0 ≤ j) :
    log (1 + j) ≤ log (1 + j * sqrt (morseChainA T m)) + 5 * radialQ m := by
  have hA : 0 < morseChainA T m :=
    (div_pos (exp_pos _) (by norm_num : (0 : ℝ) < 3)).trans_le
      (morseChainA_exp_bounds T m hd).1
  have hs : 0 < sqrt (morseChainA T m) := sqrt_pos.mpr hA
  have hQ := radial_nat_sq_le_Q m
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hQ1 : 1 ≤ radialQ m := (by nlinarith only [hm'] : (1 : ℝ) ≤ (m : ℝ) ^ 2).trans hQ
  have hlogA := (abs_le.mp (morseChainA_log_error T m hd)).1
  have hlogsq : log (morseChainA T m) = 2 * log (sqrt (morseChainA T m)) := by
    calc
      log (morseChainA T m) = log ((sqrt (morseChainA T m)) ^ 2) :=
        congrArg log (sq_sqrt hA.le).symm
      _ = _ := by rw [log_pow]; norm_num
  have hlower : -log (sqrt (morseChainA T m)) ≤ 5 * radialQ m := by
    nlinarith only [hlogA, hlogsq, hQ, hQ1]
  by_cases hsmall : sqrt (morseChainA T m) ≤ 1
  · have hpoint : (1 + j) * sqrt (morseChainA T m) ≤
        1 + j * sqrt (morseChainA T m) := by nlinarith only [hsmall]
    have hlog := log_le_log (mul_pos (by linarith) hs) hpoint
    rw [log_mul (by linarith : 1 + j ≠ 0) hs.ne'] at hlog
    linarith only [hlog, hlower]
  · have hlarge : 1 ≤ sqrt (morseChainA T m) := (lt_of_not_ge hsmall).le
    have hpoint : 1 + j ≤ 1 + j * sqrt (morseChainA T m) := by
      nlinarith only [mul_nonneg hj (sub_nonneg.mpr hlarge)]
    exact (log_le_log (by linarith) hpoint).trans
      (le_add_of_nonneg_right (mul_nonneg (by norm_num) (zero_le_one.trans hQ1)))

/-- Absorbing one additional frequency costs one logarithmic factor and
a fixed coefficient power, before the exponential suppression is used. -/
theorem inner_frequency_times_envelope {j q t c₁ c₂ c₃ r : ℝ} (hj : 0 < j)
    (hlog : log j ≤ log (1 + t) + r * q) :
    j * exp (c₁ * q + c₂ * log (1 + t) - c₃ * t) ≤
      exp ((c₁ + r) * q + (c₂ + 1) * log (1 + t) - c₃ * t) := by
  calc
    _ = exp (log j + (c₁ * q + c₂ * log (1 + t) - c₃ * t)) := by
      rw [exp_add, exp_log hj]
    _ ≤ _ := exp_le_exp.mpr (by linarith only [hlog])

/-- After the threshold is chosen, any prescribed lower index and weight
threshold may be imposed without changing it. Both the error and the
frequency times the remainder are uniformly small. -/
theorem inner_uniform_frequency_suppression
    (q : ℕ → ℝ) (hq : Tendsto q atTop atTop) (a : ℝ) (initial : ℕ)
    {c₁ c₂ c₃ r Cstar η : ℝ}
    (hc₂ : 0 ≤ c₂) (hc₃ : 0 < c₃) (hCstar : 0 < Cstar)
    (hscale : 4 * (c₁ + r) / c₃ ≤ Cstar) (hη : 0 < η) :
    ∃ N : ℕ, initial ≤ N ∧ 4096 ≤ N ∧ 64 * a ≤ (N : ℝ) ∧
      ∀ m : ℕ, N ≤ m → ∀ t j : ℝ, Cstar * q m ≤ t → 1 ≤ j →
        log j ≤ log (1 + t) + r * q m →
        exp (c₁ * q m + c₂ * log (1 + t) - c₃ * t) < η ∧
        j * exp (c₁ * q m + c₂ * log (1 + t) - c₃ * t) < η := by
  obtain ⟨K, hK⟩ := inner_uniform_suppression_of_tendsto q hq
    (show 0 ≤ c₂ + 1 by linarith) hc₃ hCstar hscale hη
  obtain ⟨N, hN, hlarge, hweight⟩ := exists_innerCellWeight_fixed_exponent a (max initial K)
  refine ⟨N, (le_max_left initial K).trans hN, hlarge, hweight, ?_⟩
  intro m hm t j ht hj hlog
  have hmK : K ≤ m := ((le_max_right initial K).trans hN).trans hm
  have hsmall := (inner_frequency_times_envelope (zero_lt_one.trans_le hj) hlog).trans_lt
    (hK m hmK t ht)
  refine ⟨?_, hsmall⟩
  have hle : exp (c₁ * q m + c₂ * log (1 + t) - c₃ * t) ≤
      j * exp (c₁ * q m + c₂ * log (1 + t) - c₃ * t) := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hj (exp_pos _).le
  exact hle.trans_lt hsmall

/-- Actual Morse cells satisfy the extra-frequency estimate on every
later transition band. There is no upper bound on the frequency. -/
theorem inner_morse_frequency_suppression (T : MorseChainData)
    (hd : ∀ m, T.index ≤ m → T.d m = morseChainInteger m)
    (a : ℝ) (initial : ℕ) {c₁ c₂ c₃ Cstar η : ℝ}
    (hc₂ : 0 ≤ c₂) (hc₃ : 0 < c₃) (hCstar : 0 < Cstar)
    (hscale : 4 * (c₁ + 5) / c₃ ≤ Cstar) (hη : 0 < η) :
    ∃ N : ℕ, max T.index initial ≤ N ∧ 4096 ≤ N ∧ 64 * a ≤ (N : ℝ) ∧
      ∀ m n j : ℕ, N ≤ m → m < n → 1 ≤ j →
        radialFrequencyBand T Cstar n j →
        exp (c₁ * radialQ m + c₂ * log (1 + (j : ℝ) * sqrt (morseChainA T m)) -
          c₃ * ((j : ℝ) * sqrt (morseChainA T m))) < η ∧
        (j : ℝ) * exp (c₁ * radialQ m +
          c₂ * log (1 + (j : ℝ) * sqrt (morseChainA T m)) -
          c₃ * ((j : ℝ) * sqrt (morseChainA T m))) < η := by
  obtain ⟨N, hN, hlarge, hweight, hsmall⟩ := inner_uniform_frequency_suppression
    radialQ inner_radialQ_tendsto a (max T.index initial) hc₂ hc₃ hCstar hscale hη
  refine ⟨N, hN, hlarge, hweight, ?_⟩
  intro m n j hm hmn hj hband
  have hmIndex := ((le_max_left T.index initial).trans hN).trans hm
  have hm1 : 1 ≤ m := by omega
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hlog := inner_morse_frequency_log_bound T (hd m hmIndex) hm1 (Nat.cast_nonneg j)
  have hlogj : log (j : ℝ) ≤ log (1 + (j : ℝ)) :=
    log_le_log (zero_lt_one.trans_le hj') (by linarith)
  exact hsmall m hm _ j
    (morseTransition_earlier_cap_action T hCstar hd hband hmIndex hmn) hj'
    (hlogj.trans hlog)

/-- Central and cone remainders obey the same strengthened bound.
The constant A is allowed to depend on the already chosen first index. -/
theorem inner_product_frequency_suppression {A b d c η : ℝ}
    (hb : 0 ≤ b) (hd : 0 ≤ d) (hc : 0 < c) (hη : 0 < η) :
    ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L → ∀ j : ℝ, 1 ≤ j →
      exp (A + b * log (1 + j) + d * log (1 + L) - c * j * L) < η ∧
      j * exp (A + b * log (1 + j) + d * log (1 + L) - c * j * L) < η := by
  obtain ⟨L₀, hL₀, hsmall⟩ := inner_product_uniform_suppression
    (A := A) (b := b + 1) (d := d) (c := c) (η := η)
    (by linarith) hd hc hη
  refine ⟨L₀, hL₀, ?_⟩
  intro L hL j hj
  have hj0 : 0 < j := zero_lt_one.trans_le hj
  have hlogj : log j ≤ log (1 + j) := log_le_log hj0 (by linarith)
  have hmul : j * exp (A + b * log (1 + j) + d * log (1 + L) - c * j * L) < η := by
    calc
      _ = exp (log j + (A + b * log (1 + j) + d * log (1 + L) - c * j * L)) := by
        rw [exp_add, exp_log hj0]
      _ ≤ exp (A + (b + 1) * log (1 + j) + d * log (1 + L) - c * j * L) :=
        exp_le_exp.mpr (by linarith only [hlogj])
      _ < η := hsmall L hL j hj
  refine ⟨?_, hmul⟩
  exact (show exp (A + b * log (1 + j) + d * log (1 + L) - c * j * L) ≤
      j * exp (A + b * log (1 + j) + d * log (1 + L) - c * j * L) by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hj (exp_pos _).le).trans_lt hmul

end ContinuousFlexibility.Radial
