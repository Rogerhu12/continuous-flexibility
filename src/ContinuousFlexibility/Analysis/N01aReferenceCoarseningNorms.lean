module

public import ContinuousFlexibility.Analysis.N01aReferenceCoarseningBasic

/-!
# The actual weighted reference spaces under partition coarsening

The angular normalization is retained exactly. Source and output membership
are unchanged, and the squared norms are comparable with one common
constant for every exponent and every actual member.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory
open scoped BigOperators

theorem n01a_sourceNormSquare_nonneg {D : ReferenceData} (hab : D.a ≤ D.b)
    (γ M : ℝ) (F : RadialSource) : 0 ≤ sourceNormSquare D γ M F :=
  add_nonneg (sq_nonneg _) (tsum_nonneg fun i => n01a_sourceCellSquare_nonneg hab γ M F.1 i)

theorem n01a_outputNormSquare_nonneg {D : ReferenceData} (hab : D.a ≤ D.b)
    (γ M aL : ℝ) (U : RadialUnknown) : 0 ≤ outputNormSquare D γ M aL U :=
  add_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _))
    (tsum_nonneg fun i => n01a_outputCellSquare_nonneg hab γ M (outputRemainder D aL U) i)

private theorem n01a_add_weighted_sum_bounds {a b q : ℝ} (ha : 0 ≤ a) (hq : 0 ≤ q)
    (B : ℕ) (h : a ≤ b ∧ b ≤ (B : ℝ) * a) :
    q + a ≤ q + b ∧ q + b ≤ ((B : ℝ) + 1) * (q + a) := by
  refine ⟨add_le_add le_rfl h.1, ?_⟩
  nlinarith [mul_nonneg (Nat.cast_nonneg B : (0 : ℝ) ≤ B) hq, h.2]

namespace N01aReferenceCoarsening

variable {D E : ReferenceData} {σ : ℕ → ℕ} (h : N01aReferenceCoarsening D E σ)

include h

/-- A single estimate covers both signs of the coefficient weight. -/
theorem weighted_comparison (hD : RadialPartition D) (hE : RadialPartition E)
    (hab : D.a ≤ D.b) (B : ℕ)
    (hB : ∀ r, {i | D.localizer i r ≠ 0}.Finite ∧
      {i | D.localizer i r ≠ 0}.ncard ≤ B)
    (W : ℕ → ℝ) (hW : ∀ n, 0 ≤ W n) (f : PolarPoint → ℝ)
    (hf : RadialCellIntegrable D f) :
    (Summable (fun j => W (E.cellIndex j) * referenceCellSquare E j f) ↔
      Summable (fun i => W (D.cellIndex i) * referenceCellSquare D i f)) ∧
    (Summable (fun i => W (D.cellIndex i) * referenceCellSquare D i f) →
      (∑' i, W (D.cellIndex i) * referenceCellSquare D i f) ≤
        ∑' j, W (E.cellIndex j) * referenceCellSquare E j f ∧
      (∑' j, W (E.cellIndex j) * referenceCellSquare E j f) ≤
        (B : ℝ) * ∑' i, W (D.cellIndex i) * referenceCellSquare D i f) := by
  let Λ : ℕ → ℝ := fun j => W (E.cellIndex j) * (2 * Real.pi)⁻¹
  have hΛ (j : ℕ) : 0 ≤ Λ j := mul_nonneg (hW _) (by positivity)
  have hfE : RadialCellIntegrable E f := (h.cell_integrable_iff hD hE f).mpr hf
  have habE : E.a ≤ E.b := by simpa only [h.a_eq, h.b_eq] using hab
  have hm (i : ℕ) : AEMeasurable (fun p : PolarPoint => D.localizer i p.1)
      (radialPhysicalMeasure D) :=
    ((hD.1 i).continuous.comp continuous_fst).measurable.aemeasurable
  have hn (i : ℕ) (p : PolarPoint) : 0 ≤ D.localizer i p.1 := hD.2.1 i p.1
  have heqfine (i : ℕ) : Λ (σ i) * n01aLocalSquare (radialPhysicalMeasure D)
      (fun i (p : PolarPoint) => D.localizer i p.1) f i =
      W (D.cellIndex i) * referenceCellSquare D i f := by
    rw [n01a_referenceCellSquare_eq_integral hab hf i]
    simp only [Λ, n01aLocalSquare, h.index_eq]
    ring
  have heqcoarse (j : ℕ) : Λ j * n01aLocalSquare (radialPhysicalMeasure D)
      (n01aCoarseLocalizer σ h.finite_fibers
        (fun i (p : PolarPoint) => D.localizer i p.1)) f j =
      W (E.cellIndex j) * referenceCellSquare E j f := by
    rw [n01a_referenceCellSquare_eq_integral habE hfE j]
    simp only [Λ, n01aLocalSquare, h.coarse_localizer_apply, h.measure_eq]
    ring
  have hs := n01aCoarseLocalizer_summable_iff (radialPhysicalMeasure D) σ h.finite_fibers
    hn hm (hf.aemeasurable_sq hD) (fun i => hf.integrable_square i)
    B (fun p => hB p.1) Λ hΛ
  refine ⟨?_, fun hsum => ?_⟩
  · simpa only [heqfine, heqcoarse] using hs
  · have hsum' : Summable (fun i => Λ (σ i) * n01aLocalSquare (radialPhysicalMeasure D)
        (fun i (p : PolarPoint) => D.localizer i p.1) f i) := by
      simpa only [heqfine] using hsum
    have hb := n01aCoarseLocalizer_tsum_bounds (radialPhysicalMeasure D) σ h.finite_fibers
      hn hm (hf.aemeasurable_sq hD) (fun i => hf.integrable_square i)
      B (fun p => hB p.1) Λ hΛ hsum'
    simpa only [heqfine, heqcoarse] using hb

theorem source_iff (hD : RadialPartition D) (hE : RadialPartition E) (hab : D.a ≤ D.b)
    (γ M : ℝ) (F : RadialSource) : SourceMember E γ M F ↔ SourceMember D γ M F := by
  obtain ⟨B, hB⟩ := hD.2.2.2.2.2
  have hs (hf : RadialCellIntegrable D F.1) :
      Summable (sourceCellSquare E γ M F.1) ↔ Summable (sourceCellSquare D γ M F.1) := by
    change (Summable (fun j =>
      Real.exp (2 * M * radialQ (E.cellIndex j) + 2 * γ * radialS (E.cellIndex j)) *
        referenceCellSquare E j F.1)) ↔
      Summable (fun i =>
        Real.exp (2 * M * radialQ (D.cellIndex i) + 2 * γ * radialS (D.cellIndex i)) *
          referenceCellSquare D i F.1)
    exact (h.weighted_comparison hD hE hab B hB
      (fun n => Real.exp (2 * M * radialQ n + 2 * γ * radialS n))
      (fun _ => (Real.exp_pos _).le) F.1 hf).1
  constructor
  · rintro ⟨hi, hsum, hp, he, hint, hzero⟩
    have hiD := (h.cell_integrable_iff hD hE F.1).mp hi
    refine ⟨hiD, (hs hiD).mp hsum, hp, he, ?_, ?_⟩
    · simpa only [h.a_eq, h.b_eq] using hint
    · simpa only [h.a_eq, h.b_eq] using hzero
  · rintro ⟨hi, hsum, hp, he, hint, hzero⟩
    refine ⟨(h.cell_integrable_iff hD hE F.1).mpr hi, (hs hi).mpr hsum, hp, he, ?_, ?_⟩
    · simpa only [h.a_eq, h.b_eq] using hint
    · simpa only [h.a_eq, h.b_eq] using hzero

/-- The derivative source space retains local signed L² and the same
weighted square sum, without imposing evenness or a compatibility mean. -/
theorem source_derivative_iff (hD : RadialPartition D) (hE : RadialPartition E)
    (hab : D.a ≤ D.b) (γ M : ℝ) (f : PolarPoint → ℝ) :
    SourceDerivativeMember E γ M f ↔ SourceDerivativeMember D γ M f := by
  obtain ⟨B, hB⟩ := hD.2.2.2.2.2
  have hs (hf : RadialCellIntegrable D f) :
      Summable (sourceCellSquare E γ M f) ↔ Summable (sourceCellSquare D γ M f) := by
    change (Summable (fun j =>
      Real.exp (2 * M * radialQ (E.cellIndex j) + 2 * γ * radialS (E.cellIndex j)) *
        referenceCellSquare E j f)) ↔
      Summable (fun i =>
        Real.exp (2 * M * radialQ (D.cellIndex i) + 2 * γ * radialS (D.cellIndex i)) *
          referenceCellSquare D i f)
    exact (h.weighted_comparison hD hE hab B hB
      (fun n => Real.exp (2 * M * radialQ n + 2 * γ * radialS n))
      (fun _ => (Real.exp_pos _).le) f hf).1
  constructor
  · rintro ⟨hi, hsum⟩
    have hiD := (h.cell_integrable_iff hD hE f).mp hi
    exact ⟨hiD, (hs hiD).mp hsum⟩
  · rintro ⟨hi, hsum⟩
    exact ⟨(h.cell_integrable_iff hD hE f).mpr hi, (hs hi).mpr hsum⟩

theorem output_realization_iff (hD : RadialPartition D) (hE : RadialPartition E)
    (hab : D.a ≤ D.b) (γ M aL : ℝ) (U : RadialUnknown) :
    OutputRealization E γ M aL U ↔ OutputRealization D γ M aL U := by
  obtain ⟨B, hB⟩ := hD.2.2.2.2.2
  have hs (hf : RadialCellIntegrable D (outputRemainder D aL U)) :
      Summable (outputCellSquare E γ M (outputRemainder D aL U)) ↔
        Summable (outputCellSquare D γ M (outputRemainder D aL U)) := by
    change (Summable (fun j =>
      Real.exp (-2 * M * radialQ (E.cellIndex j) + 2 * γ * radialS (E.cellIndex j)) *
        referenceCellSquare E j (outputRemainder D aL U))) ↔
      Summable (fun i =>
        Real.exp (-2 * M * radialQ (D.cellIndex i) + 2 * γ * radialS (D.cellIndex i)) *
          referenceCellSquare D i (outputRemainder D aL U))
    exact (h.weighted_comparison hD hE hab B hB
      (fun n => Real.exp (-2 * M * radialQ n + 2 * γ * radialS n))
      (fun _ => (Real.exp_pos _).le) (outputRemainder D aL U) hf).1
  simp only [OutputRealization, h.remainder_eq]
  constructor
  · rintro ⟨hi, hsum, hp, he⟩
    have hiD := (h.cell_integrable_iff hD hE _).mp hi
    exact ⟨hiD, (hs hiD).mp hsum, hp, he⟩
  · rintro ⟨hi, hsum, hp, he⟩
    exact ⟨(h.cell_integrable_iff hD hE _).mpr hi, (hs hi).mpr hsum, hp, he⟩

theorem output_member_iff (hD : RadialPartition D) (hE : RadialPartition E)
    (hab : D.a ≤ D.b) (γ M : ℝ) (U : RadialUnknown) :
    OutputMember E γ M U ↔ OutputMember D γ M U := by
  simp only [OutputMember, h.output_realization_iff hD hE hab]

theorem graph_iff (hD : RadialPartition D) (hE : RadialPartition E) (hab : D.a ≤ D.b)
    (γ M₀ M₁ : ℝ) (U : RadialUnknown) (F : RadialSource) :
    ReferenceGraph E γ M₀ M₁ U F ↔ ReferenceGraph D γ M₀ M₁ U F := by
  simp only [ReferenceGraph, h.output_member_iff hD hE hab, h.source_iff hD hE hab,
    h.row_eq, h.test_iff, h.weakPairing_eq, h.a_eq, h.b_eq, h.column_eq]

/-- The same comparison constant works for every source and output exponent.
The source version requires only its actual square-space membership, which
is sufficient also for differences whose mean constraint is not needed. -/
theorem exists_norm_comparison (hD : RadialPartition D) (hE : RadialPartition E)
    (hab : D.a ≤ D.b) :
    ∃ K : ℝ, 1 ≤ K ∧
      (∀ (γ M : ℝ) (F : RadialSource),
        RadialCellIntegrable D F.1 → Summable (sourceCellSquare D γ M F.1) →
        sourceNormSquare D γ M F ≤ sourceNormSquare E γ M F ∧
        sourceNormSquare E γ M F ≤ K * sourceNormSquare D γ M F) ∧
      (∀ (γ M aL : ℝ) (U : RadialUnknown), OutputRealization D γ M aL U →
        outputNormSquare D γ M aL U ≤ outputNormSquare E γ M aL U ∧
        outputNormSquare E γ M aL U ≤ K * outputNormSquare D γ M aL U) := by
  obtain ⟨B, hB⟩ := hD.2.2.2.2.2
  refine ⟨(B : ℝ) + 1, ?_, ?_, ?_⟩
  · have hB0 : (0 : ℝ) ≤ B := Nat.cast_nonneg B
    linarith
  · intro γ M F hi hsum
    change Summable (fun i =>
      Real.exp (2 * M * radialQ (D.cellIndex i) + 2 * γ * radialS (D.cellIndex i)) *
        referenceCellSquare D i F.1) at hsum
    have hb : (∑' i, sourceCellSquare D γ M F.1 i) ≤
        (∑' j, sourceCellSquare E γ M F.1 j) ∧
        (∑' j, sourceCellSquare E γ M F.1 j) ≤
          (B : ℝ) * ∑' i, sourceCellSquare D γ M F.1 i := by
      simpa only [sourceCellSquare] using
        (h.weighted_comparison hD hE hab B hB
          (fun n => Real.exp (2 * M * radialQ n + 2 * γ * radialS n))
          (fun _ => (Real.exp_pos _).le) F.1 hi).2 hsum
    exact n01a_add_weighted_sum_bounds
      (tsum_nonneg fun i => n01a_sourceCellSquare_nonneg hab γ M F.1 i) (sq_nonneg F.2) B hb
  · intro γ M aL U hU
    have hsum := hU.2.1
    change Summable (fun i =>
      Real.exp (-2 * M * radialQ (D.cellIndex i) + 2 * γ * radialS (D.cellIndex i)) *
        referenceCellSquare D i (outputRemainder D aL U)) at hsum
    have hb : (∑' i, outputCellSquare D γ M (outputRemainder D aL U) i) ≤
        (∑' j, outputCellSquare E γ M (outputRemainder D aL U) j) ∧
        (∑' j, outputCellSquare E γ M (outputRemainder D aL U) j) ≤
          (B : ℝ) * ∑' i, outputCellSquare D γ M (outputRemainder D aL U) i := by
      simpa only [outputCellSquare] using
        (h.weighted_comparison hD hE hab B hB
          (fun n => Real.exp (-2 * M * radialQ n + 2 * γ * radialS n))
          (fun _ => (Real.exp_pos _).le) (outputRemainder D aL U) hU.1).2 hsum
    simpa only [outputNormSquare, h.remainder_eq] using n01a_add_weighted_sum_bounds
      (tsum_nonneg fun i => n01a_outputCellSquare_nonneg hab γ M (outputRemainder D aL U) i)
      (add_nonneg (sq_nonneg aL) (sq_nonneg U.2)) B hb

end N01aReferenceCoarsening

end ContinuousFlexibility.Statements
