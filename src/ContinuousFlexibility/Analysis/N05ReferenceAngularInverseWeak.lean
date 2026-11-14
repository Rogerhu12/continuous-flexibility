module

public import ContinuousFlexibility.Analysis.N05ReferenceOutputAngularWeak
public import ContinuousFlexibility.Analysis.N05ReferenceAngularWeighted

/-!
# Actual weak angular jets of the original high inverse output

Weighted strong convergence embeds into physical L². The underlying
finite projections converge to the original output minus its first two
angular modes. The closed physical weak identity consequently identifies
the reconstructed jet as a derivative of that very field.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology
open ContinuousFlexibility.Statements

theorem n05_referenceInverse_highWeakAngularJet_bound {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    {γ M₀ M₁ : ℝ} (hγ : 0 < γ) {G : RadialSource → RadialUnknown}
    (hG : ReferenceInverseProperties D γ M₀ M₁ G) :
    ∃ C : ℝ, 0 < C ∧ ∀ F, SourceMember D γ M₀ F → ∀ b : ℕ,
      Summable (fun n => (((2 * (n + 2) : ℕ) : ℝ) ^ (2 * b)) *
        n05_referenceHighSourceSquare D γ M₀ F n) →
      ∃ d : PolarPoint → ℝ,
        n05_weakReferenceAngularJet D (n05_referenceHighPart (G F).1) d b ∧
        MemLp d 2 (referenceWeightedMeasure D γ (-M₁)) ∧
        outputNormSquare D γ M₁ 0 (d, 0) ≤ C ^ 2 *
          ∑' n, (((2 * (n + 2) : ℕ) : ℝ) ^ (2 * b)) *
            n05_referenceHighSourceSquare D γ M₀ F n ∧
        Function.Periodic d (0, Real.pi) := by
  obtain ⟨C, hC, hbound⟩ :=
    n05_referenceInverse_angularWeighted_summable_bound hD hborder hγ hG
  refine ⟨C, hC, fun F hF b hs => ?_⟩
  obtain ⟨a, hU⟩ := (hG.1 F hF).1
  have hout := hbound F hF
    (fun n => (((2 * (n + 2) : ℕ) : ℝ) ^ (2 * b))) (fun n => by positivity) hs
  obtain ⟨d, hw, hd, he, hperiodic⟩ :=
    n05_referenceOutput_highWeakAngularJet hD hborder hγ hU b hout.1
  exact ⟨d, hw, hd, he.le.trans hout.2, hperiodic⟩

end ContinuousFlexibility.Radial
