import ContinuousFlexibility.Radial.R11bFiniteSource

/-!
# Exact selected coefficients of compatible finite sources

The coefficient is extracted from the ordinary angular integral. No
uniqueness or reconstruction statement is used.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory Real
open scoped BigOperators
open ContinuousFlexibility.Statements

theorem r11b_angularPairing_finsetSum {ι : Type*}
    (s : Finset ι) (F : ι → ℝ → ℝ) (g : ℝ → ℝ)
    (hF : ∀ i ∈ s, IntervalIntegrable (fun θ => F i θ * g θ)
      volume (0 : ℝ) (2 * Real.pi)) :
    angularPairing (fun θ => ∑ i ∈ s, F i θ) g =
      ∑ i ∈ s, angularPairing (F i) g := by
  unfold angularPairing angularAverage
  simp_rw [Finset.sum_mul]
  rw [intervalIntegral.integral_finsetSum hF, Finset.mul_sum]

theorem r11b_finiteEvenCosine_referenceMode
    (J : Finset ℕ) (hJ : ∀ n ∈ J, 0 < n) (c : ℕ → ℝ → ℝ)
    (j : ℕ) (hj : j ∈ J) (r : ℝ) :
    referenceMode (fun x => ∑ n ∈ J, c n x.1 * cosineMode (2 * n) x.2)
      (2 * j) r = c j r := by
  have hc (n : ℕ) : Continuous (cosineMode n) := by
    unfold cosineMode
    exact continuous_const.mul (Real.continuous_cos.comp
      (continuous_const.mul continuous_id))
  have hpair :
      angularPairing (fun θ => ∑ n ∈ J, c n r * cosineMode (2 * n) θ)
        (cosineMode (2 * j)) = c j r := by
    rw [r11b_angularPairing_finsetSum J
      (fun n θ => c n r * cosineMode (2 * n) θ) (cosineMode (2 * j))
      (fun n _ => ((continuous_const.mul (hc (2 * n))).mul
        (hc (2 * j))).intervalIntegrable _ _)]
    simp_rw [r11b_angularPairing_const_mul]
    rw [Finset.sum_eq_single j]
    · rw [angularPairing_cosineMode (2 * j) (2 * j)
        (Nat.mul_pos (by decide) (hJ j hj)) (Nat.mul_pos (by decide) (hJ j hj))]
      simp only [ite_true, mul_one]
    · intro n hn hnj
      rw [angularPairing_cosineMode (2 * n) (2 * j)
        (Nat.mul_pos (by decide) (hJ n hn)) (Nat.mul_pos (by decide) (hJ j hj))]
      have hneq : 2 * n ≠ 2 * j := by omega
      simp only [if_neg hneq, mul_zero]
    · intro hnot
      exact (hnot hj).elim
  simpa only [referenceMode, radialAngularMean, angularPairing, angularAverage, one_div]
    using hpair

theorem r11bSineCosineSource_referenceMode
    (J : Finset ℕ) (hJ : ∀ n ∈ J, 0 < n) (f : PolarPoint → ℝ)
    (j : ℕ) (hj : j ∈ J) (r : ℝ) :
    referenceMode (r11bSineCosineSource J f) (2 * j) r =
      -angularPairing (fun θ => f (r, θ)) (sineMode (2 * j)) := by
  exact (r11b_finiteEvenCosine_referenceMode J hJ
    (fun n r => angularPairing (fun θ => f (r, θ)) (fun θ => -sineMode (2 * n) θ))
    j hj r).trans (r11b_angularPairing_neg_right _ _)

end ContinuousFlexibility.Radial
