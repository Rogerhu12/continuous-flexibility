import ContinuousFlexibility.Analysis.N05ReferenceSourceWeightGap
import ContinuousFlexibility.Analysis.N05ReferencePieceCoefficients

/-!
# The output endpoint factor on a nearby actual cell

The endpoint exponential attached to a piece is retained explicitly. The
endpoint-exponent window moves it to an actual reference cell at the cost of
a coefficient power, including any prescribed output material exponent.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

/-- The output endpoint exponential is transferred to an actual cell
without changing its endpoint exponent. Only a coefficient power is spent. -/
theorem n05_referenceOutputWeight_swindow {B γ : ℝ}
    (hB : 0 ≤ B) (hγ : 0 ≤ γ) (M : ℝ) :
    ∃ C A : ℝ, 0 < C ∧ 0 < A ∧ ∀ i n : ℕ,
      |radialS i - radialS n| ≤ B * (radialQ n + 1) →
        Real.exp (2 * γ * radialS n) ≤
          C * radialE n ^ A *
            Real.exp (-2 * M * radialQ i + 2 * γ * radialS i) := by
  obtain ⟨Q, hQ, hq⟩ := n05_radialQ_swindow_bound hB
  let A : ℝ := 2 * γ * B + 2 * |M| * Q + 1
  have hA : 0 < A := by dsimp only [A]; positivity
  refine ⟨Real.exp A, A, Real.exp_pos _, hA, fun i n hwindow => ?_⟩
  have hs : radialS n - radialS i ≤ B * (radialQ n + 1) := by
    calc
      _ ≤ |radialS n - radialS i| := le_abs_self _
      _ = |radialS i - radialS n| := abs_sub_comm _ _
      _ ≤ _ := hwindow
  have hsg := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 2 * γ)
  have hm : 2 * M * radialQ i ≤ 2 * |M| * radialQ i :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (le_abs_self M) (by norm_num))
      (Radial.radialQ_nonneg i)
  have hmq := mul_le_mul_of_nonneg_left (hq i n hwindow)
    (by positivity : 0 ≤ 2 * |M|)
  have hexp : 2 * γ * radialS n ≤ A * (radialQ n + 1) +
      (-2 * M * radialQ i + 2 * γ * radialS i) := by
    have hn := Radial.radialQ_nonneg n
    dsimp only [A]
    nlinarith only [hsg, hm, hmq, hn]
  calc
    _ ≤ Real.exp (A * (radialQ n + 1) +
        (-2 * M * radialQ i + 2 * γ * radialS i)) := Real.exp_le_exp.mpr hexp
    _ = _ := by
      rw [radialE, ← Real.exp_mul, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring

/-- The old bounded-index output estimate remains available for explicit
seed geometry and is implied by the endpoint-exponent estimate. -/
theorem n05_referenceOutputWeight_index_window {B γ : ℝ}
    (hB : 0 ≤ B) (hγ : 0 ≤ γ) (M : ℝ) :
    ∃ C A : ℝ, 0 < C ∧ 0 < A ∧ ∀ i n : ℕ,
      |(i : ℝ) - (n : ℝ)| ≤ B →
        Real.exp (2 * γ * radialS n) ≤
          C * radialE n ^ A *
            Real.exp (-2 * M * radialQ i + 2 * γ * radialS i) := by
  obtain ⟨C, A, hC, hA, hw⟩ := n05_referenceOutputWeight_swindow
    (show 0 ≤ 6 * B * (B ^ 2 + 1) by positivity) hγ M
  exact ⟨C, A, hC, hA, fun i n hi => hw i n (n05_radialS_index_window hB i n hi)⟩

end ContinuousFlexibility.Statements
