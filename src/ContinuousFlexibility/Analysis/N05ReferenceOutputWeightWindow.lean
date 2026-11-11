import ContinuousFlexibility.Analysis.N05ReferenceSourceWeightGap
import ContinuousFlexibility.Analysis.N05ReferencePieceCoefficients

/-!
# The output endpoint factor on a nearby actual cell

The endpoint exponential attached to a piece is retained explicitly. Moving
it to a reference cell containing the same physical point costs a fixed
coefficient power, including the prescribed output material exponent.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

theorem n05_referenceOutputWeight_index_window {B γ : ℝ}
    (hB : 0 ≤ B) (hγ : 0 ≤ γ) (M : ℝ) :
    ∃ C A : ℝ, 0 < C ∧ 0 < A ∧ ∀ i n : ℕ,
      |(i : ℝ) - (n : ℝ)| ≤ B →
        Real.exp (2 * γ * radialS n) ≤
          C * radialE n ^ A *
            Real.exp (-2 * M * radialQ i + 2 * γ * radialS i) := by
  obtain ⟨C0, A0, hC0, hA0, hsource⟩ :=
    n05_referenceSourceWeight_index_window hB hγ 0
  have hA : 0 ≤ A0 + 2 * |M| := by positivity
  obtain ⟨C1, hC1, hcoefficient⟩ :=
    n05_radialE_power_index_window (A0 + 2 * |M|) B hA
  refine ⟨C0 * C1, C1, mul_pos hC0 hC1, hC1, fun i n hwindow => ?_⟩
  have hreverse : |(n : ℝ) - (i : ℝ)| ≤ B := by
    rw [abs_sub_comm]
    exact hwindow
  have hfirst : Real.exp (2 * γ * radialS n) ≤
      C0 * radialE i ^ A0 * Real.exp (2 * γ * radialS i) := by
    simpa only [mul_zero, zero_mul, zero_add] using hsource n i hreverse
  have hweight : radialE i ^ A0 * Real.exp (2 * γ * radialS i) ≤
      radialE i ^ (A0 + 2 * |M|) *
        Real.exp (-2 * M * radialQ i + 2 * γ * radialS i) := by
    rw [radialE, ← Real.exp_mul, ← Real.exp_mul,
      ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hm := le_abs_self M
    have hq := Radial.radialQ_nonneg i
    nlinarith only [mul_nonneg (sub_nonneg.mpr hm) hq]
  calc
    _ ≤ C0 * radialE i ^ A0 * Real.exp (2 * γ * radialS i) := hfirst
    _ ≤ C0 * (radialE i ^ (A0 + 2 * |M|) *
        Real.exp (-2 * M * radialQ i + 2 * γ * radialS i)) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hweight hC0.le
    _ ≤ C0 * ((C1 * radialE n ^ C1) *
        Real.exp (-2 * M * radialQ i + 2 * γ * radialS i)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (hcoefficient i n hwindow)
          (Real.exp_pos _).le) hC0.le
    _ = _ := by ring

end ContinuousFlexibility.Statements
