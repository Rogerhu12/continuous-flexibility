module

public import ContinuousFlexibility.Analysis.N01aReferenceCoarseningDifferences

/-!
# Graph topology under coarsening with measurable source representatives

The source-difference hypothesis needed for the frozen graph topology is
stated explicitly. It is a property of the actual source representatives,
not an assumed norm comparison. All norm comparisons used below have been
proved from the finite-fiber localizer formula.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements.N01aReferenceCoarsening

open MeasureTheory Filter
open scoped Topology

variable {D E : ReferenceData} {σ : ℕ → ℕ} (h : N01aReferenceCoarsening D E σ)

include h

theorem smooth_core_closure_of_source_aemeasurable
    (hD : RadialPartition D) (hE : RadialPartition E) (hab : D.a ≤ D.b)
    {γ M₀ M₁ : ℝ}
    (hMeas : ∀ F : RadialSource, SourceMember D γ M₀ F →
      AEMeasurable F.1 (radialPhysicalMeasure D))
    (hCore : ReferenceSmoothCoreClosure D γ M₀ M₁) :
    ReferenceSmoothCoreClosure E γ M₀ M₁ := by
  obtain ⟨K, _, hsrc, hout⟩ := h.exists_norm_comparison hD hE hab
  have habE : E.a ≤ E.b := by simpa only [h.a_eq, h.b_eq] using hab
  intro U F hUF
  have hUFD := (h.graph_iff hD hE hab γ M₀ M₁ U F).mp hUF
  obtain ⟨Un, Fn, an, hseq, hsource, houtput⟩ := hCore U F hUFD
  have hFn (n : ℕ) : SourceMember D γ M₀ (Fn n) := (hseq n).1.2.1
  have hF : SourceMember D γ M₀ F := hUFD.2.1
  have hdiff (n : ℕ) :
      RadialCellIntegrable D (Fn n - F).1 ∧
        Summable (sourceCellSquare D γ M₀ (Fn n - F).1) :=
    n01a_source_difference_square_member hD hab γ M₀ (hFn n).1 hF.1
      (hMeas (Fn n) (hFn n)) (hMeas F hF) (hFn n).2.1 hF.2.1
  refine ⟨Un, Fn, an, ?_, ?_, ?_⟩
  · intro n
    exact ⟨(h.graph_iff hD hE hab γ M₀ M₁ (Un n) (Fn n)).mpr (hseq n).1,
      (h.smooth_iff (Un n)).mpr (hseq n).2.1,
      (h.output_realization_iff hD hE hab γ M₁ (an n) (Un n - U)).mpr (hseq n).2.2⟩
  · apply squeeze_zero'
      (Eventually.of_forall fun n => n01a_sourceNormSquare_nonneg habE γ M₀ (Fn n - F))
      (Eventually.of_forall fun n => (hsrc γ M₀ (Fn n - F) (hdiff n).1 (hdiff n).2).2)
    simpa only [mul_zero] using hsource.const_mul K
  · apply squeeze_zero'
      (Eventually.of_forall fun n => n01a_outputNormSquare_nonneg habE γ M₁ (an n) (Un n - U))
      (Eventually.of_forall fun n => (hout γ M₁ (an n) (Un n - U) (hseq n).2.2).2)
    simpa only [mul_zero] using houtput.const_mul K

theorem graph_closed_of_source_aemeasurable
    (hD : RadialPartition D) (hE : RadialPartition E) (hab : D.a ≤ D.b)
    {γ M₀ M₁ : ℝ}
    (hMeas : ∀ F : RadialSource, SourceMember D γ M₀ F →
      AEMeasurable F.1 (radialPhysicalMeasure D))
    (hClosed : ReferenceGraphClosed D γ M₀ M₁) :
    ReferenceGraphClosed E γ M₀ M₁ := by
  obtain ⟨K, _, hsrc, hout⟩ := h.exists_norm_comparison hD hE hab
  intro U F Un Fn an hseq hU hF houtReal hsource houtput
  have hseqD (n : ℕ) : ReferenceGraph D γ M₀ M₁ (Un n) (Fn n) :=
    (h.graph_iff hD hE hab γ M₀ M₁ (Un n) (Fn n)).mp (hseq n)
  have hUD := (h.output_member_iff hD hE hab γ M₁ U).mp hU
  have hFD := (h.source_iff hD hE hab γ M₀ F).mp hF
  have houtD (n : ℕ) : OutputRealization D γ M₁ (an n) (Un n - U) :=
    (h.output_realization_iff hD hE hab γ M₁ (an n) (Un n - U)).mp (houtReal n)
  have hFn (n : ℕ) : SourceMember D γ M₀ (Fn n) := (hseqD n).2.1
  have hdiff (n : ℕ) :
      RadialCellIntegrable D (Fn n - F).1 ∧
        Summable (sourceCellSquare D γ M₀ (Fn n - F).1) :=
    n01a_source_difference_square_member hD hab γ M₀ (hFn n).1 hFD.1
      (hMeas (Fn n) (hFn n)) (hMeas F hFD) (hFn n).2.1 hFD.2.1
  have hsourceD : Tendsto (fun n => sourceNormSquare D γ M₀ (Fn n - F)) atTop (𝓝 0) :=
    squeeze_zero'
      (Eventually.of_forall fun n => n01a_sourceNormSquare_nonneg hab γ M₀ (Fn n - F))
      (Eventually.of_forall fun n => (hsrc γ M₀ (Fn n - F) (hdiff n).1 (hdiff n).2).1)
      hsource
  have houtputD : Tendsto (fun n => outputNormSquare D γ M₁ (an n) (Un n - U))
      atTop (𝓝 0) :=
    squeeze_zero'
      (Eventually.of_forall fun n => n01a_outputNormSquare_nonneg hab γ M₁ (an n) (Un n - U))
      (Eventually.of_forall fun n => (hout γ M₁ (an n) (Un n - U) (houtD n)).1)
      houtput
  exact (h.graph_iff hD hE hab γ M₀ M₁ U F).mpr
    (hClosed U F Un Fn an hseqD hUD hFD houtD hsourceD houtputD)

end ContinuousFlexibility.Statements.N01aReferenceCoarsening
