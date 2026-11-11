import ContinuousFlexibility.Analysis.N05ReferenceOutputAngularLimit

/-!
# Strong high angular jet limits of the same reference inverse

The actual inverse bound supplies all projected output memberships and
all output coefficient square sums. The reconstruction therefore needs
only angular square summability on the actual source. Its energy bound
has the original constant and the original material exponents.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology
open ContinuousFlexibility.Statements

theorem n05_referenceInverse_highAngularJet_limit_bound {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    {γ M₀ M₁ : ℝ} (hγ : 0 < γ) {G : RadialSource → RadialUnknown}
    (hG : ReferenceInverseProperties D γ M₀ M₁ G) :
    ∃ C : ℝ, 0 < C ∧ ∀ F, SourceMember D γ M₀ F → ∀ b : ℕ,
      Summable (fun n => (((2 * (n + 2) : ℕ) : ℝ) ^ (2 * b)) *
        n05_referenceHighSourceSquare D γ M₀ F n) →
      ∃ d : PolarPoint → ℝ,
        MemLp d 2 (referenceWeightedMeasure D γ (-M₁)) ∧
        outputNormSquare D γ M₁ 0 (d, 0) ≤ C ^ 2 *
          ∑' n, (((2 * (n + 2) : ℕ) : ℝ) ^ (2 * b)) *
            n05_referenceHighSourceSquare D γ M₀ F n ∧
        Tendsto (fun N => ∫ x,
          (n05_referenceHighAngularJet (Finset.range N) b (G F).1 x - d x) ^ 2
          ∂referenceWeightedMeasure D γ (-M₁)) atTop (𝓝 0) ∧
        Function.Periodic d (0, Real.pi) := by
  obtain ⟨C, hC, hbound⟩ := n05_referenceInverse_angularWeighted_summable_bound
    hD hborder hγ hG
  refine ⟨C, hC, fun F hF b hs => ?_⟩
  obtain ⟨a, hU⟩ := (hG.1 F hF).1
  have hout := hbound F hF
    (fun n => (((2 * (n + 2) : ℕ) : ℝ) ^ (2 * b))) (fun n => by positivity) hs
  obtain ⟨d, hd, he, hlim, hperiodic⟩ :=
    n05_referenceOutput_highAngularJet_limit hD hborder hγ hU b hout.1
  exact ⟨d, hd, he.le.trans hout.2, hlim, hperiodic⟩

end ContinuousFlexibility.Radial
