import ContinuousFlexibility.Analysis.N05ReferenceLeftChoice
import ContinuousFlexibility.Radial.ReferenceGraphProjection

/-!
# The actual reference inverse commutes with finite angular projection

The zero mode and the bordered frequency-two mode are retained. Projection
of the source is compatible, and self-adjointness and commutation on actual
test functions project the maximum weak graph. Its uniqueness identifies
the projected output with the same inverse applied to the projected source.
The original bound then holds for this projection with its original constant.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements

theorem n05_referenceBasisProjection_sourceMember {D : ReferenceData}
    (hab : D.a ≤ D.b) {γ M : ℝ} {F : RadialSource}
    (hF : SourceMember D γ M F) {I : Finset ℕ} (h0 : 0 ∈ I) :
    SourceMember D γ M (referenceBasisProjection I F.1, F.2) := by
  have hp := referenceBasisProjection_cellIntegrable hF.1 I
  have hs : Summable (sourceCellSquare D γ M (referenceBasisProjection I F.1)) := by
    apply hF.2.1.of_nonneg_of_le
      (fun m => mul_nonneg (Real.exp_pos _).le (referenceCellSquare_nonneg hab m hp))
    intro m
    exact mul_le_mul_of_nonneg_left (referenceBasisProjection_cell_sq_le hab hF.1 I m)
      (Real.exp_pos _).le
  have hmean (r : ℝ) :
      radialAngularMean (fun θ => referenceBasisProjection I F.1 (r, θ)) =
        radialAngularMean (fun θ => F.1 (r, θ)) := by
    simpa only [referenceAngularCoefficient_zero, if_pos h0, referenceBasisProjection] using
      referenceAngularCoefficient_projection I (fun θ => F.1 (r, θ)) 0
  refine ⟨hp, hs, referenceBasisProjection_periodic I F.1,
    referenceBasisProjection_even I F.1, ?_, ?_⟩
  · simpa only [hmean] using hF.2.2.2.2.1
  · simpa only [hmean] using hF.2.2.2.2.2

/-- No fixed-source hypothesis is needed: project the actual source as
well as the actual output, preserving the two scalar channels. -/
theorem n05_referenceGraph_basisProjection {D : ReferenceData}
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
  refine ⟨?_, n05_referenceBasisProjection_sourceMember hgeom.2.1.le hgraph.2.1 h0,
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

/-- The common reference inverse itself, rather than a new inverse, has
the projected graph representative. -/
theorem n05_referenceInverse_basisProjection {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    {γ M₀ M₁ : ℝ} (hγ : 0 < γ) {G : RadialSource → RadialUnknown}
    (hG : ReferenceInverseProperties D γ M₀ M₁ G)
    {F : RadialSource} (hF : SourceMember D γ M₀ F)
    {I : Finset ℕ} (h0 : 0 ∈ I) (h1 : 1 ∈ I) :
    RadialRepresentativeEq D (G (referenceBasisProjection I F.1, F.2))
      (referenceBasisProjection I (G F).1, (G F).2) :=
  hG.2.1 _ _ (n05_referenceGraph_basisProjection hD hborder hγ (hG.1 F hF) h0 h1)

/-- The bound constant is independent of the finite angular selection.
Both coefficient exponents and the selected physical left constant are
unchanged. All hypotheses concern the original reference inverse. -/
theorem n05_referenceInverse_projected_bound {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    {γ M₀ M₁ : ℝ} (hγ : 0 < γ) {G : RadialSource → RadialUnknown}
    (hG : ReferenceInverseProperties D γ M₀ M₁ G) :
    ∃ C : ℝ, 0 < C ∧ ∀ F, SourceMember D γ M₀ F →
      ∀ I : Finset ℕ, 0 ∈ I → 1 ∈ I →
      OutputRealization D γ M₁ (n05_referenceLeftConstant D (G F))
        (referenceBasisProjection I (G F).1, (G F).2) ∧
      outputNormSquare D γ M₁ (n05_referenceLeftConstant D (G F))
        (referenceBasisProjection I (G F).1, (G F).2) ≤
          C ^ 2 * sourceNormSquare D γ M₀ (referenceBasisProjection I F.1, F.2) := by
  obtain ⟨C, hC, hbound⟩ := n05_referenceInverse_selectedLeftConstant hD hborder hγ hG
  refine ⟨C, hC, fun F hF I h0 h1 => ?_⟩
  have hab : D.a ≤ D.b := hD.choose_spec.1.2.1.le
  have hpart : RadialPartition D := hD.choose_spec.2.1
  have hU := (hbound F hF).1
  have hproj := referenceBasisProjection_outputRealization hab hpart hU h0
  have hFproj := n05_referenceBasisProjection_sourceMember hab hF h0
  obtain ⟨hV, hVbound⟩ := hbound (referenceBasisProjection I F.1, F.2) hFproj
  have hsame := n05_referenceInverse_basisProjection hD hborder hγ hG hF h0 h1
  have hVproj := OutputRealization.congr_ae hab hV hsame
    (referenceBasisProjection_periodic I (G F).1)
    (referenceBasisProjection_even I (G F).1)
  have ha := n05_outputRealization_leftConstant_unique hD hborder hγ hγ hVproj hproj
  refine ⟨hproj, ?_⟩
  have hb := (outputNormSquare_congr_ae hab hV hsame).symm.le.trans hVbound
  simpa only [ha] using hb

end ContinuousFlexibility.Radial
