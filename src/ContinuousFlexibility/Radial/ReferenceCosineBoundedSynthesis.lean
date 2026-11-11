import ContinuousFlexibility.Radial.ReferenceOutputCosine

/-!
# Summing actual modal energy estimates

A uniform estimate for each actual radial mode gives a square-summable
sequence in the actual output measure. The scalar source enters only
the frequency-two coordinate. Isometric cosine synthesis then gives
the frozen output norm, including both scalar coordinates.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open MeasureTheory
open scoped ENNReal

theorem referenceCosine_bounded_synthesis {D : ReferenceData}
    (hab : D.a ≤ D.b) (hP : RadialPartition D)
    {γ M₀ M₁ : ℝ} {F : RadialSource} (hF : SourceMember D γ M₀ F)
    (v : ℕ → Lp ℝ 2 (referenceRadialWeightedMeasure D γ (-M₁)))
    {K aL ν : ℝ} (hK : 0 ≤ K)
    (haL : aL ^ 2 ≤ K * sourceNormSquare D γ M₀ F)
    (hν : ν ^ 2 ≤ K * sourceNormSquare D γ M₀ F)
    (hv : ∀ n : ℕ, ‖v n‖ ^ 2 ≤
      K * (‖referenceSourceCosineAnalysis hab hP hF n‖ ^ 2 +
        if n = 1 then F.2 ^ 2 else 0)) :
    ∃ a : lp (fun _ : ℕ => Lp ℝ 2 (referenceRadialWeightedMeasure D γ (-M₁))) 2,
      (∀ n, a n = v n) ∧
      OutputRealization D γ M₁ aL (referenceOutputCosine D γ M₁ aL ν a) ∧
      outputNormSquare D γ M₁ aL (referenceOutputCosine D γ M₁ aL ν a) ≤
        (3 * K) * sourceNormSquare D γ M₀ F := by
  let f := referenceSourceCosineAnalysis hab hP hF
  have hsf : Summable (fun n : ℕ => ‖f n‖ ^ 2) := by
    exact (referenceCosineAnalysisCoeff_hasSum_norm_sq
      (hF.memLp_radial_angular hab hP)
      (referenceSource_angular_periodic hF) hF.2.2.2.1).summable
  let b (n : ℕ) : ℝ := K * ‖f n‖ ^ 2 + if n = 1 then K * F.2 ^ 2 else 0
  have hsb : HasSum b (K * (∑' n : ℕ, ‖f n‖ ^ 2) + K * F.2 ^ 2) :=
    (hsf.hasSum.mul_left K).add (hasSum_ite_eq 1 (K * F.2 ^ 2))
  have hbound (n : ℕ) : ‖v n‖ ^ 2 ≤ b n := by
    apply (hv n).trans_eq
    dsimp only [b, f]
    by_cases hn : n = 1
    · simp only [hn, ite_true, mul_add]
    · simp only [hn, ite_false, add_zero, mul_zero]
  have hsv : Summable (fun n : ℕ => ‖v n‖ ^ 2) :=
    Summable.of_nonneg_of_le (fun n => sq_nonneg _) hbound hsb.summable
  have hsum : (∑' n : ℕ, ‖v n‖ ^ 2) ≤ K * sourceNormSquare D γ M₀ F := by
    calc
      _ ≤ ∑' n : ℕ, b n := Summable.tsum_le_tsum hbound hsv hsb.summable
      _ = K * (∑' n : ℕ, ‖f n‖ ^ 2) + K * F.2 ^ 2 := hsb.tsum_eq
      _ = K * sourceNormSquare D γ M₀ F := by
        rw [← referenceSourceCosineAnalysis_norm_sq hab hP hF]
        dsimp only [f]
        ring
  let a : lp (fun _ : ℕ => Lp ℝ 2 (referenceRadialWeightedMeasure D γ (-M₁))) 2 :=
    ⟨v, by
      apply memℓp_gen
      simpa using hsv⟩
  refine ⟨a, fun _ => rfl, referenceOutputCosine_realization hab hP γ M₁ aL ν a, ?_⟩
  rw [referenceOutputCosine_norm_sq hab hP]
  change aL ^ 2 + ν ^ 2 + (∑' n : ℕ, ‖v n‖ ^ 2) ≤
    (3 * K) * sourceNormSquare D γ M₀ F
  nlinarith only [haL, hν, hsum]

end ContinuousFlexibility.Statements
