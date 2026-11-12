import ContinuousFlexibility.Analysis.TransitionCoefficient
import ContinuousFlexibility.Radial.WeightKernelBounds

/-!
# Full spatial decay through an intermediate matching level

The matching coefficient is evaluated at the common transition level.
The extra distance of the two genuine columns pays for any coefficient
growth beyond both endpoints. Thus combining the two columns preserves
the full endpoint travel exponent, including for interior return terms.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open ContinuousFlexibility.Statements

theorem matchedTransition_coefficient_absorb {d : ℝ} (hd : 0 ≤ d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n k m : ℕ,
      d * radialQ n - |radialS k - radialS n| - |radialS m - radialS n| ≤
        C + d * (radialQ k + radialQ m) - |radialS k - radialS m| := by
  obtain ⟨C, hC⟩ := absorb_radialQ d 2 (by norm_num)
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro n k m
  exact Analysis.transition_coefficient_absorb
    radialQ_nonneg radialQ_monotone radialS_monotone hd (le_max_right _ _)
    (fun k m => (hC k m).trans (add_le_add le_rfl (le_max_left C 0))) n k m

/-- Two actual column envelopes and a transition coefficient combine
into an endpoint envelope without reducing the spatial decay rate. -/
theorem matchedTransition_column_product {a d : ℝ} (ha : 0 ≤ a) (hd : 0 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ n k m : ℕ,
      Real.exp (d * radialQ n) *
        (Real.exp (a * (radialQ k + radialQ n) - |radialS k - radialS n|) *
          Real.exp (a * (radialQ m + radialQ n) - |radialS m - radialS n|)) ≤
        C * Real.exp ((3 * a + d) * (radialQ k + radialQ m) -
          |radialS k - radialS m|) := by
  obtain ⟨C, _, hC⟩ := matchedTransition_coefficient_absorb
    (d := 2 * a + d) (by positivity)
  refine ⟨Real.exp C, Real.exp_pos C, ?_⟩
  intro n k m
  simp only [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h := hC n k m
  nlinarith only [h]

end ContinuousFlexibility.Radial
