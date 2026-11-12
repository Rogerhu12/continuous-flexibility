import ContinuousFlexibility.Analysis.N05ReferenceHighProjection

/-!
# Arbitrary angular square weights for the same reference inverse

These are squares of the actual singleton angular projections in the frozen
reference norms. A single inverse bound controls every nonnegative angular
weight, hence all polynomial frequency weights simultaneously. Summability
of the output is a conclusion, obtained from summability of the input.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements

def n05_referenceHighSourceSquare (D : ReferenceData) (γ M : ℝ)
    (F : RadialSource) (n : ℕ) : ℝ :=
  sourceNormSquare D γ M (referenceBasisProjection {n + 2} F.1, 0)

def n05_referenceHighOutputSquare (D : ReferenceData) (γ M : ℝ)
    (U : RadialUnknown) (n : ℕ) : ℝ :=
  outputNormSquare D γ M 0 (referenceBasisProjection {n + 2} U.1, 0)

theorem n05_referenceInverse_highMode_bound {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    {γ M₀ M₁ : ℝ} (hγ : 0 < γ) {G : RadialSource → RadialUnknown}
    (hG : ReferenceInverseProperties D γ M₀ M₁ G) :
    ∃ C : ℝ, 0 < C ∧ ∀ F, SourceMember D γ M₀ F → ∀ n : ℕ,
      0 ≤ n05_referenceHighOutputSquare D γ M₁ (G F) n ∧
      n05_referenceHighOutputSquare D γ M₁ (G F) n ≤
        C ^ 2 * n05_referenceHighSourceSquare D γ M₀ F n := by
  obtain ⟨C, hC, hbound⟩ := n05_referenceInverse_highProjected_bound hD hborder hγ hG
  refine ⟨C, hC, fun F hF n => ?_⟩
  have hI : ∀ k ∈ ({n + 2} : Finset ℕ), 2 ≤ k := by
    intro k hk
    simp only [Finset.mem_singleton] at hk
    omega
  obtain ⟨hU, hb⟩ := hbound F hF {n + 2} hI
  exact ⟨outputNormSquare_nonneg hD.choose_spec.1.2.1.le hU, hb⟩

/-- The constant is chosen before the angular weights and their finite
selection. In particular it is independent of the angular order. -/
theorem n05_referenceInverse_finiteAngularWeighted_bound {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    {γ M₀ M₁ : ℝ} (hγ : 0 < γ) {G : RadialSource → RadialUnknown}
    (hG : ReferenceInverseProperties D γ M₀ M₁ G) :
    ∃ C : ℝ, 0 < C ∧ ∀ F, SourceMember D γ M₀ F →
      ∀ w : ℕ → ℝ, (∀ n, 0 ≤ w n) → ∀ J : Finset ℕ,
      (∑ n ∈ J, w n * n05_referenceHighOutputSquare D γ M₁ (G F) n) ≤
        C ^ 2 * ∑ n ∈ J, w n * n05_referenceHighSourceSquare D γ M₀ F n := by
  obtain ⟨C, hC, hbound⟩ := n05_referenceInverse_highMode_bound hD hborder hγ hG
  refine ⟨C, hC, fun F hF w hw J => ?_⟩
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  calc
    w n * n05_referenceHighOutputSquare D γ M₁ (G F) n ≤
        w n * (C ^ 2 * n05_referenceHighSourceSquare D γ M₀ F n) :=
      mul_le_mul_of_nonneg_left (hbound F hF n).2 (hw n)
    _ = C ^ 2 * (w n * n05_referenceHighSourceSquare D γ M₀ F n) := by ring

/-- Infinite angular square summation requires only input summability.
Neither output summability nor a separate angular estimate is assumed. -/
theorem n05_referenceInverse_angularWeighted_summable_bound {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    {γ M₀ M₁ : ℝ} (hγ : 0 < γ) {G : RadialSource → RadialUnknown}
    (hG : ReferenceInverseProperties D γ M₀ M₁ G) :
    ∃ C : ℝ, 0 < C ∧ ∀ F, SourceMember D γ M₀ F →
      ∀ w : ℕ → ℝ, (∀ n, 0 ≤ w n) →
      Summable (fun n => w n * n05_referenceHighSourceSquare D γ M₀ F n) →
      Summable (fun n => w n * n05_referenceHighOutputSquare D γ M₁ (G F) n) ∧
      (∑' n, w n * n05_referenceHighOutputSquare D γ M₁ (G F) n) ≤
        C ^ 2 * ∑' n, w n * n05_referenceHighSourceSquare D γ M₀ F n := by
  obtain ⟨C, hC, hbound⟩ := n05_referenceInverse_highMode_bound hD hborder hγ hG
  refine ⟨C, hC, fun F hF w hw hs => ?_⟩
  have hnonneg (n : ℕ) :
      0 ≤ w n * n05_referenceHighOutputSquare D γ M₁ (G F) n :=
    mul_nonneg (hw n) (hbound F hF n).1
  have hle (n : ℕ) :
      w n * n05_referenceHighOutputSquare D γ M₁ (G F) n ≤
        C ^ 2 * (w n * n05_referenceHighSourceSquare D γ M₀ F n) := by
    calc
      w n * n05_referenceHighOutputSquare D γ M₁ (G F) n ≤
          w n * (C ^ 2 * n05_referenceHighSourceSquare D γ M₀ F n) :=
        mul_le_mul_of_nonneg_left (hbound F hF n).2 (hw n)
      _ = C ^ 2 * (w n * n05_referenceHighSourceSquare D γ M₀ F n) := by ring
  have hsC := hs.mul_left (C ^ 2)
  have hout := hsC.of_nonneg_of_le hnonneg hle
  refine ⟨hout, ?_⟩
  calc
    (∑' n, w n * n05_referenceHighOutputSquare D γ M₁ (G F) n) ≤
        ∑' n, C ^ 2 * (w n * n05_referenceHighSourceSquare D γ M₀ F n) :=
      Summable.tsum_le_tsum hle hout hsC
    _ = C ^ 2 * ∑' n, w n * n05_referenceHighSourceSquare D γ M₀ F n :=
      tsum_mul_left

end ContinuousFlexibility.Radial
