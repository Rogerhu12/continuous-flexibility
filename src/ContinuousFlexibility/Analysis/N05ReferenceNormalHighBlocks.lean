import ContinuousFlexibility.Analysis.N05ReferenceNormalProjection
import ContinuousFlexibility.Analysis.N05ReferenceAngularJetEstimate
import ContinuousFlexibility.Analysis.N05ReferenceNormalizerJets

/-!
# High angular blocks of the same physical normal derivative

The first-normal estimate is applied only to compatible even singleton
sources. Physical weak-derivative uniqueness identifies each resulting
normal derivative with the corresponding projection of the original one.
Thus every high normal block costs exactly one angular source derivative.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements

theorem n05_referenceNormal_highBlock_bound {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    {γ M0 M1 MN : ℝ} (hγ : 0 < γ) {G : RadialSource → RadialUnknown}
    (hG : ReferenceInverseProperties D γ M0 M1 G)
    (hN : FirstNormalInverseEstimate D γ M0 MN G) :
    ∃ C : ℝ, 0 < C ∧ ∀ F, SourceMember D γ M0 F →
      ∀ ur : PolarPoint → ℝ, WeakNormalDerivative D (G F).1 ur →
      OutputRealization D γ MN 0 (ur, 0) → ∀ n : ℕ,
      OutputRealization D γ MN 0 (referenceBasisProjection {n + 2} ur, 0) ∧
      n05_referenceHighOutputSquare D γ MN (ur, 0) n ≤
        C ^ 2 * (1 + (((2 * (n + 2) : ℕ) : ℝ) ^ 2)) *
          n05_referenceHighSourceSquare D γ M0 F n := by
  obtain ⟨C, hC, hnormal⟩ := hN
  refine ⟨C, hC, fun F hF ur hur hUr n => ?_⟩
  have hab : D.a ≤ D.b := hD.choose_spec.1.2.1.le
  have hI : ∀ k ∈ ({n + 2} : Finset ℕ), 2 ≤ k := by
    intro k hk
    simp only [Finset.mem_singleton] at hk
    omega
  have hFproj := n05_referenceHighProjection_sourceMember hD hF hI
  obtain ⟨hderMember, hderNorm⟩ := n05_referenceHighAngularJet_source_norm hD hF {n} 1
  have hder : WeakAngularDerivative D (referenceBasisProjection {n + 2} F.1)
      (n05_referenceHighAngularJet {n} 1 F.1) := by
    apply n05_weakAngularDerivative_of_weakReferenceJet
    simpa only [Finset.image_singleton] using n05_referenceHighAngularJet_weak D {n} 1 F.1
  obtain ⟨v, hvweak, hvreal, hvbound⟩ :=
    hnormal (referenceBasisProjection {n + 2} F.1, 0)
      (n05_referenceHighAngularJet {n} 1 F.1) hFproj hder hderMember
  have hULp : MemLp (G F).1 2 (radialPhysicalMeasure D) :=
    r11b_output_memLp hD hborder hγ (hG.1 F hF).1
  have hUrLp : MemLp ur 2 (radialPhysicalMeasure D) :=
    r11b_output_memLp hD hborder hγ ⟨0, hUr⟩
  have hVLp : MemLp (G (referenceBasisProjection {n + 2} F.1, 0)).1 2
      (radialPhysicalMeasure D) :=
    r11b_output_memLp hD hborder hγ (hG.1 _ hFproj).1
  have hvLp : MemLp v 2 (radialPhysicalMeasure D) :=
    r11b_output_memLp hD hborder hγ ⟨0, hvreal⟩
  have hprojULp := n05_referenceBasisProjection_memLp hULp {n + 2}
  have hprojUrLp := n05_referenceBasisProjection_memLp hUrLp {n + 2}
  have hsame := n05_referenceInverse_highProjection hD hborder hγ hG hF hI
  have hvproj := n05_weakNormalDerivative_congr_ae hab hVLp hprojULp hvLp hvLp
    hsame.2 Filter.EventuallyEq.rfl hvweak
  have hurproj := n05_weakNormalDerivative_basisProjection hab hULp hUrLp hur {n + 2}
  have heq : v =ᵐ[radialPhysicalMeasure D] referenceBasisProjection {n + 2} ur :=
    n05_weakNormalDerivative_unique_periodic hab hvLp hprojUrLp hvreal.2.2.1
      (referenceBasisProjection_periodic {n + 2} ur) hvproj hurproj
  have hpairs : RadialRepresentativeEq D (v, 0)
      (referenceBasisProjection {n + 2} ur, 0) := ⟨rfl, heq⟩
  have hreal := OutputRealization.congr_ae hab hvreal hpairs
    (referenceBasisProjection_periodic {n + 2} ur)
    (referenceBasisProjection_even {n + 2} ur)
  refine ⟨hreal, ?_⟩
  have hb := (outputNormSquare_congr_ae hab hvreal hpairs).symm.le.trans hvbound
  have hn : sourceNormSquare D γ M0 (n05_referenceHighAngularJet {n} 1 F.1, 0) =
      (((2 * (n + 2) : ℕ) : ℝ) ^ 2) * n05_referenceHighSourceSquare D γ M0 F n := by
    simpa only [Finset.sum_singleton, Nat.mul_one] using hderNorm
  rw [hn] at hb
  change n05_referenceHighOutputSquare D γ MN (ur, 0) n ≤
    C ^ 2 * (n05_referenceHighSourceSquare D γ M0 F n +
      (((2 * (n + 2) : ℕ) : ℝ) ^ 2) * n05_referenceHighSourceSquare D γ M0 F n) at hb
  calc
    _ ≤ _ := hb
    _ = _ := by ring

end ContinuousFlexibility.Radial
