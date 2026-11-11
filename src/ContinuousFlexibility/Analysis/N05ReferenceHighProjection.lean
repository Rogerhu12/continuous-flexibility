import ContinuousFlexibility.Analysis.N05ReferenceProjection
import ContinuousFlexibility.Radial.ReferenceSmoothCore

/-!
# Uniform high angular blocks of the actual reference inverse

Subtract two projections which retain the mean and the bordered frequency.
This removes both scalar channels and leaves any finite set of higher
frequencies. Linearity and uniqueness identify its inverse with the same
block of the original output. The original estimate has the same constant
and the same coefficient exponents on every such block.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements

theorem n05_referenceBasisProjection_high_sub {I : Finset ℕ}
    (hI : ∀ n ∈ I, 2 ≤ n) (f : PolarPoint → ℝ) :
    referenceBasisProjection ({0, 1} ∪ I) f -
        referenceBasisProjection {0, 1} f = referenceBasisProjection I f := by
  have hd : Disjoint ({0, 1} : Finset ℕ) I := by
    apply Finset.disjoint_left.mpr
    intro n hn hni
    have hn2 := hI n hni
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    omega
  funext x
  simp only [Pi.sub_apply, referenceBasisProjection, angularBasisProjection,
    Finset.sum_union hd, add_sub_cancel_left]

theorem n05_referenceHighProjection_pair_eq {I : Finset ℕ}
    (hI : ∀ n ∈ I, 2 ≤ n) (F : RadialSource) :
    (referenceBasisProjection ({0, 1} ∪ I) F.1, F.2) -
        (referenceBasisProjection {0, 1} F.1, F.2) =
      (referenceBasisProjection I F.1, 0) := by
  apply Prod.ext
  · exact n05_referenceBasisProjection_high_sub hI F.1
  · exact sub_self F.2

theorem n05_referenceHighProjection_sourceMember {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {γ M : ℝ} {F : RadialSource}
    (hF : SourceMember D γ M F) {I : Finset ℕ} (hI : ∀ n ∈ I, 2 ≤ n) :
    SourceMember D γ M (referenceBasisProjection I F.1, 0) := by
  have hab : D.a ≤ D.b := hD.choose_spec.1.2.1.le
  have hbig := n05_referenceBasisProjection_sourceMember hab hF
    (I := {0, 1} ∪ I) (by simp)
  have hcore := n05_referenceBasisProjection_sourceMember hab hF
    (I := {0, 1}) (by simp)
  have hs := referenceSource_sub hD hbig hcore
  rw [n05_referenceHighProjection_pair_eq hI F] at hs
  exact hs

theorem n05_referenceHighProjection_outputRealization {D : ReferenceData}
    (hab : D.a ≤ D.b) (hpart : RadialPartition D)
    {γ M a : ℝ} {U : RadialUnknown} (hU : OutputRealization D γ M a U)
    {I : Finset ℕ} (hI : ∀ n ∈ I, 2 ≤ n) :
    OutputRealization D γ M 0 (referenceBasisProjection I U.1, 0) := by
  have hbig := referenceBasisProjection_outputRealization hab hpart hU
    (I := {0, 1} ∪ I) (by simp)
  have hcore := referenceBasisProjection_outputRealization hab hpart hU
    (I := {0, 1}) (by simp)
  have hd : OutputRealization D γ M 0
      ((referenceBasisProjection ({0, 1} ∪ I) U.1, U.2) -
        (referenceBasisProjection {0, 1} U.1, U.2)) := by
    simpa only [neg_one_mul, add_neg_cancel, neg_one_smul, sub_eq_add_neg] using
      OutputRealization.add hab hbig (OutputRealization.smul hcore (-1))
  rw [n05_referenceHighProjection_pair_eq hI U] at hd
  exact hd

theorem n05_referenceInverse_highProjection {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    {γ M₀ M₁ : ℝ} (hγ : 0 < γ) {G : RadialSource → RadialUnknown}
    (hG : ReferenceInverseProperties D γ M₀ M₁ G)
    {F : RadialSource} (hF : SourceMember D γ M₀ F)
    {I : Finset ℕ} (hI : ∀ n ∈ I, 2 ≤ n) :
    RadialRepresentativeEq D (G (referenceBasisProjection I F.1, 0))
      (referenceBasisProjection I (G F).1, 0) := by
  have hab : D.a ≤ D.b := hD.choose_spec.1.2.1.le
  have hFbig := n05_referenceBasisProjection_sourceMember hab hF
    (I := {0, 1} ∪ I) (by simp)
  have hFcore := n05_referenceBasisProjection_sourceMember hab hF
    (I := {0, 1}) (by simp)
  have hbig := n05_referenceInverse_basisProjection hD hborder hγ hG hF
    (I := {0, 1} ∪ I) (by simp) (by simp)
  have hcore := n05_referenceInverse_basisProjection hD hborder hγ hG hF
    (I := {0, 1}) (by simp) (by simp)
  have hlin : RadialRepresentativeEq D
      (G ((referenceBasisProjection ({0, 1} ∪ I) F.1, F.2) -
        (referenceBasisProjection {0, 1} F.1, F.2)))
      (G (referenceBasisProjection ({0, 1} ∪ I) F.1, F.2) -
        G (referenceBasisProjection {0, 1} F.1, F.2)) := by
    simpa only [one_smul, neg_one_smul, sub_eq_add_neg] using
      hG.2.2.1 _ _ hFbig hFcore 1 (-1)
  have hsame := hlin.trans (referenceRepresentative_sub hbig hcore)
  simpa only [n05_referenceHighProjection_pair_eq hI F,
    n05_referenceHighProjection_pair_eq hI (G F)] using hsame

/-- A single constant controls every finite high angular block. The
left constant and bordered scalar of each such block are both zero. -/
theorem n05_referenceInverse_highProjected_bound {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    {γ M₀ M₁ : ℝ} (hγ : 0 < γ) {G : RadialSource → RadialUnknown}
    (hG : ReferenceInverseProperties D γ M₀ M₁ G) :
    ∃ C : ℝ, 0 < C ∧ ∀ F, SourceMember D γ M₀ F →
      ∀ I : Finset ℕ, (∀ n ∈ I, 2 ≤ n) →
      OutputRealization D γ M₁ 0 (referenceBasisProjection I (G F).1, 0) ∧
      outputNormSquare D γ M₁ 0 (referenceBasisProjection I (G F).1, 0) ≤
        C ^ 2 * sourceNormSquare D γ M₀ (referenceBasisProjection I F.1, 0) := by
  obtain ⟨C, hC, hbound⟩ := n05_referenceInverse_selectedLeftConstant hD hborder hγ hG
  refine ⟨C, hC, fun F hF I hI => ?_⟩
  have hab : D.a ≤ D.b := hD.choose_spec.1.2.1.le
  have hpart : RadialPartition D := hD.choose_spec.2.1
  have hU := (hbound F hF).1
  have hproj := n05_referenceHighProjection_outputRealization hab hpart hU hI
  have hFproj := n05_referenceHighProjection_sourceMember hD hF hI
  obtain ⟨hV, hVbound⟩ := hbound (referenceBasisProjection I F.1, 0) hFproj
  have hsame := n05_referenceInverse_highProjection hD hborder hγ hG hF hI
  have hVproj := OutputRealization.congr_ae hab hV hsame
    (referenceBasisProjection_periodic I (G F).1)
    (referenceBasisProjection_even I (G F).1)
  have ha := n05_outputRealization_leftConstant_unique hD hborder hγ hγ hVproj hproj
  refine ⟨hproj, ?_⟩
  have hb := (outputNormSquare_congr_ae hab hV hsame).symm.le.trans hVbound
  simpa only [ha] using hb

end ContinuousFlexibility.Radial
