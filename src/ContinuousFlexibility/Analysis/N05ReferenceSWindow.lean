module

public import ContinuousFlexibility.Radial.DeepTailPhysicalWeights

/-!
# Coefficient bounds from a controlled endpoint-exponent difference

The physical and sampled indices need not have bounded additive difference.
It suffices that their cubic endpoint exponents differ by a coefficient
exponent at the sampled index. Slow variation of `radialQ` then controls
coefficient powers in both directions, without spending endpoint decay.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

/-- An endpoint-exponent window controls the coefficient exponent at the
physical index by the coefficient exponent at the sampled index. -/
theorem n05_radialQ_swindow_bound {B : ℝ} (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ i n : ℕ,
      |radialS i - radialS n| ≤ B * (radialQ n + 1) →
        radialQ i ≤ C * (radialQ n + 1) := by
  obtain ⟨L, hL⟩ := Radial.radialQ_sub_le 1 zero_lt_one
  refine ⟨B + |L| + 1, by positivity, fun i n hwindow => ?_⟩
  have hdiff : radialQ i - radialQ n ≤ B * (radialQ n + 1) + |L| := by
    calc
      _ ≤ |radialQ i - radialQ n| := le_abs_self _
      _ ≤ |radialS i - radialS n| + L := by
        simpa only [one_mul] using hL i n
      _ ≤ B * (radialQ n + 1) + |L| := add_le_add hwindow (le_abs_self L)
  have hQ := Radial.radialQ_nonneg n
  nlinarith only [hdiff, mul_nonneg (abs_nonneg L) hQ]

/-- The same window also controls the sampled coefficient exponent by the
physical one. A small slow-variation factor absorbs the sampled exponent. -/
theorem n05_radialQ_swindow_reverse_bound {B : ℝ} (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ i n : ℕ,
      |radialS i - radialS n| ≤ B * (radialQ n + 1) →
        radialQ n ≤ C * (radialQ i + 1) := by
  let η : ℝ := (2 * (B + 1))⁻¹
  have hη : 0 < η := by dsimp only [η]; positivity
  have hηB : η * B ≤ (1 / 2 : ℝ) := by
    have hc : η * (2 * (B + 1)) = 1 := by
      dsimp only [η]
      exact inv_mul_cancel₀ (by positivity)
    nlinarith only [hc, hη.le]
  obtain ⟨L, hL⟩ := Radial.radialQ_sub_le η hη
  refine ⟨2 * |L| + 3, by positivity, fun i n hwindow => ?_⟩
  have hdiff : radialQ n - radialQ i ≤ η * B * (radialQ n + 1) + |L| := by
    calc
      _ ≤ |radialQ n - radialQ i| := le_abs_self _
      _ ≤ η * |radialS n - radialS i| + L := hL n i
      _ = η * |radialS i - radialS n| + L := by rw [abs_sub_comm]
      _ ≤ η * (B * (radialQ n + 1)) + |L| :=
        add_le_add (mul_le_mul_of_nonneg_left hwindow hη.le) (le_abs_self L)
      _ = _ := by ring
  have hsmall := mul_le_mul_of_nonneg_right hηB
    (add_nonneg (Radial.radialQ_nonneg n) zero_le_one)
  have hQi := Radial.radialQ_nonneg i
  nlinarith only [hdiff, hsmall, mul_nonneg (abs_nonneg L) hQi, hQi]

private theorem n05_radialE_power_of_Q_bound (A K : ℝ)
    (hA : 0 ≤ A) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ i n : ℕ,
      radialQ i ≤ K * (radialQ n + 1) →
        radialE i ^ A ≤ C * radialE n ^ C := by
  let C : ℝ := Real.exp (A * K) + A * K + 1
  have hAK : 0 ≤ A * K := mul_nonneg hA hK
  have hC : 0 < C := by dsimp only [C]; positivity
  have heC : Real.exp (A * K) ≤ C := by dsimp only [C]; linarith only [hAK]
  have hAC : A * K ≤ C := by
    have he := Real.exp_pos (A * K)
    dsimp only [C]
    linarith only [he]
  refine ⟨C, hC, fun i n hq => ?_⟩
  have hscaled := mul_le_mul_of_nonneg_left hq hA
  have hlarge := mul_le_mul_of_nonneg_right hAC (Radial.radialQ_nonneg n)
  have hexp : A * radialQ i ≤ A * K + C * radialQ n := by
    nlinarith only [hscaled, hlarge]
  calc
    radialE i ^ A = Real.exp (A * radialQ i) := by
      rw [radialE, ← Real.exp_mul, mul_comm]
    _ ≤ Real.exp (A * K + C * radialQ n) := Real.exp_le_exp.mpr hexp
    _ = Real.exp (A * K) * radialE n ^ C := by
      rw [Real.exp_add, radialE, ← Real.exp_mul]
      congr 1
      congr 1
      exact mul_comm _ _
    _ ≤ C * radialE n ^ C := mul_le_mul_of_nonneg_right heC
      (Real.rpow_nonneg (Real.exp_pos _).le _)

/-- Forward coefficient transport under the endpoint-exponent window. -/
theorem n05_radialE_power_swindow (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ i n : ℕ,
      |radialS i - radialS n| ≤ B * (radialQ n + 1) →
        radialE i ^ A ≤ C * radialE n ^ C := by
  obtain ⟨K, hK, hq⟩ := n05_radialQ_swindow_bound hB
  obtain ⟨C, hC, hE⟩ := n05_radialE_power_of_Q_bound A K hA hK.le
  exact ⟨C, hC, fun i n hwindow => hE i n (hq i n hwindow)⟩

/-- Reverse coefficient transport keeps the original direction of the
window hypothesis, which is measured at the sampled index `n`. -/
theorem n05_radialE_power_swindow_reverse (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ i n : ℕ,
      |radialS i - radialS n| ≤ B * (radialQ n + 1) →
        radialE n ^ A ≤ C * radialE i ^ C := by
  obtain ⟨K, hK, hq⟩ := n05_radialQ_swindow_reverse_bound hB
  obtain ⟨C, hC, hE⟩ := n05_radialE_power_of_Q_bound A K hA hK.le
  exact ⟨C, hC, fun i n hwindow => hE n i (hq i n hwindow)⟩

end ContinuousFlexibility.Statements
