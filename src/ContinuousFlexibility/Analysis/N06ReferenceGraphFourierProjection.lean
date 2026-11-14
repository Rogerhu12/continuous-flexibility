module

public import ContinuousFlexibility.Radial.ReferenceGraphProjection

/-!
# Physical Fourier projection of the original reference graph

The actual physical cosine projection preserves the source compatibility
condition when it retains the mean mode. Retaining the first positive mode
also preserves the border row and the nu column. Thus both sides of the
original weak graph can be projected without assuming that its source has
finite angular support.

In applications the source is f - omega * psi. We project that whole source
and then add omega * psi back; no finite spectrum of psi is needed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements
open scoped ContDiff Topology BigOperators

/-- Retaining mode zero preserves the actual angular mean at every radius. -/
theorem n06_referenceBasisProjection_mean {I : Finset ℕ} (h0 : 0 ∈ I)
    (f : PolarPoint → ℝ) (r : ℝ) :
    radialAngularMean (fun θ => referenceBasisProjection I f (r, θ)) =
      radialAngularMean (fun θ => f (r, θ)) := by
  simpa only [referenceAngularCoefficient_zero, if_pos h0,
    referenceBasisProjection] using
    referenceAngularCoefficient_projection I (fun θ => f (r, θ)) 0

/-- Every radial cutoff, including the two original left cutoffs, is fixed. -/
theorem n06_referenceBasisProjection_radial {I : Finset ℕ} (h0 : 0 ∈ I)
    (a : ℝ → ℝ) :
    referenceBasisProjection I (fun p : PolarPoint => a p.1) =
      (fun p : PolarPoint => a p.1) := by
  funext p
  exact congrFun (angularBasisProjection_const h0 (a p.1)) p.2

theorem n06_referenceBasisProjection_sourceCell_le {D : ReferenceData}
    (hab : D.a ≤ D.b) {f : PolarPoint → ℝ}
    (hf : RadialCellIntegrable D f) (γ M : ℝ) (I : Finset ℕ) (m : ℕ) :
    sourceCellSquare D γ M (referenceBasisProjection I f) m ≤
      sourceCellSquare D γ M f m :=
  mul_le_mul_of_nonneg_left (referenceBasisProjection_cell_sq_le hab hf I m)
    (Real.exp_pos _).le

/-- All original source conditions, including the genuine integral-zero
condition, hold for the projected source with its unchanged scalar row. -/
theorem n06_referenceBasisProjection_sourceMember {D : ReferenceData}
    (hab : D.a ≤ D.b) {γ M : ℝ} {F : RadialSource}
    (hF : SourceMember D γ M F) {I : Finset ℕ} (h0 : 0 ∈ I) :
    SourceMember D γ M (referenceBasisProjection I F.1, F.2) := by
  have hp := referenceBasisProjection_cellIntegrable hF.1 I
  have hs : Summable (sourceCellSquare D γ M (referenceBasisProjection I F.1)) :=
    Summable.of_nonneg_of_le (sourceCellSquare_nonneg hab γ M hp)
      (n06_referenceBasisProjection_sourceCell_le hab hF.1 γ M I) hF.2.1
  have hmean : (fun r => radialAngularMean (fun θ =>
      referenceBasisProjection I F.1 (r, θ))) =
      (fun r => radialAngularMean (fun θ => F.1 (r, θ))) :=
    funext (n06_referenceBasisProjection_mean h0 F.1)
  refine ⟨hp, hs, referenceBasisProjection_periodic I F.1,
    referenceBasisProjection_even I F.1, ?_, ?_⟩
  · rw [hmean]
    exact hF.2.2.2.2.1
  · rw [hmean]
    exact hF.2.2.2.2.2

theorem n06_referenceBasisProjection_sourceNormSquare_le {D : ReferenceData}
    (hab : D.a ≤ D.b) {γ M : ℝ} {F : RadialSource}
    (hF : SourceMember D γ M F) {I : Finset ℕ} (h0 : 0 ∈ I) :
    sourceNormSquare D γ M (referenceBasisProjection I F.1, F.2) ≤
      sourceNormSquare D γ M F := by
  unfold sourceNormSquare
  exact add_le_add le_rfl
    (Summable.tsum_le_tsum (n06_referenceBasisProjection_sourceCell_le hab hF.1 γ M I)
      (n06_referenceBasisProjection_sourceMember hab hF h0).2.1 hF.2.1)

/-- The original physical maximal weak graph is invariant under simultaneous
projection of its function components. Neither source nor solution is assumed
to have finite spectrum before the projection. -/
theorem n06_referenceGraph_basisProjection_source {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    {γ M₀ M₁ : ℝ} (hγ : 0 < γ) {U : RadialUnknown} {F : RadialSource}
    (hgraph : ReferenceGraph D γ M₀ M₁ U F) {I : Finset ℕ}
    (h0 : 0 ∈ I) (h1 : 1 ∈ I) :
    ReferenceGraph D γ M₀ M₁ (referenceBasisProjection I U.1, U.2)
      (referenceBasisProjection I F.1, F.2) := by
  have hgeom : RadialProfileGeometry D := hD.choose_spec.1
  have hpart : RadialPartition D := hD.choose_spec.2.1
  have hu := r11b_output_memLp hD hborder hγ hgraph.1
  have hf := r11b_source_memLp hD hγ hgraph.2.1
  have hc := r11b_continuous_memLp (D := D)
    (reference_column_mode_continuous hgeom hborder)
  refine ⟨?_, n06_referenceBasisProjection_sourceMember hgeom.2.1.le hgraph.2.1 h0,
    (referenceBasisProjection_row D h1 U.1).trans hgraph.2.2.1, ?_⟩
  · obtain ⟨aL, hU⟩ := hgraph.1
    exact ⟨aL, referenceBasisProjection_outputRealization hgeom.2.1.le hpart hU h0⟩
  · intro ψ hψ
    have hψL := r11b_continuous_memLp (D := D) hψ.1.continuous
    have h := hgraph.2.2.2 _ (referenceBasisProjection_test hψ I)
    have hcEq := referenceBasisProjection_integral_pairing hgeom.2.1.le hc hψL I
    rw [referenceBasisProjection_column D h1] at hcEq
    have hfEq := referenceBasisProjection_integral_pairing hgeom.2.1.le hf hψL I
    rw [← referenceBasisProjection_weakPairing hgeom hu hψ I, ← hcEq, ← hfEq] at h
    exact h

/-- Uniqueness identifies this projected solution with the same physical
inverse at the projected source. -/
theorem n06_referenceInverse_basisProjection_source {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    {γ M₀ M₁ : ℝ} (hγ : 0 < γ) {G : RadialSource → RadialUnknown}
    (hG : ReferenceInverseProperties D γ M₀ M₁ G)
    {U : RadialUnknown} {F : RadialSource}
    (hgraph : ReferenceGraph D γ M₀ M₁ U F) {I : Finset ℕ}
    (h0 : 0 ∈ I) (h1 : 1 ∈ I) :
    RadialRepresentativeEq D (G (referenceBasisProjection I F.1, F.2))
      (referenceBasisProjection I U.1, U.2) :=
  hG.2.1 _ _ (n06_referenceGraph_basisProjection_source hD hborder hγ hgraph h0 h1)

/-- The compatibility column is added back unchanged after projecting the
actual physical reference source. Its angular spectrum is unrestricted. -/
theorem n06_referenceGraph_basisProjection_compatibility {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    {γ M₀ M₁ : ℝ} (hγ : 0 < γ) {U : RadialUnknown}
    (f ψ : PolarPoint → ℝ) (omega c : ℝ)
    (hgraph : ReferenceGraph D γ M₀ M₁ U (fun p => f p - omega * ψ p, c))
    {I : Finset ℕ} (h0 : 0 ∈ I) (h1 : 1 ∈ I) :
    ReferenceGraph D γ M₀ M₁ (referenceBasisProjection I U.1, U.2)
      (fun p => (referenceBasisProjection I (fun q => f q - omega * ψ q) p + omega * ψ p) -
        omega * ψ p, c) := by
  simpa only [add_sub_cancel_right] using
    n06_referenceGraph_basisProjection_source hD hborder hγ hgraph h0 h1

end ContinuousFlexibility.Radial
