import ContinuousFlexibility.Analysis.N05CanonicalAngularJetChoice
import ContinuousFlexibility.Analysis.N05CanonicalOutputAngularJets
import ContinuousFlexibility.Analysis.N05CanonicalAngularPairing
import ContinuousFlexibility.Analysis.N05CanonicalInverseDefinition
import ContinuousFlexibility.Analysis.N05CanonicalOutputBlock
import ContinuousFlexibility.Analysis.N05ReferenceZeroRemainder

/-!
# Positive angular jets of the fixed global canonical inverse

The physical derivative furnished at any endpoint represents the unique
canonical weak derivative of the original global inverse. The same choice
therefore has both the genuine reference energy estimate and the local
canonical estimate with its endpoint exponential intact.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory ContinuousFlexibility.Radial

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
  (hD : IsRadialReference D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
  (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
  (hcoordinates : N05ControlledReferenceCoordinates D S C K)
  {γ M0 M1 : ℝ} (hγ : 0 < γ) {G : RadialSource → RadialUnknown}
  (hG : ReferenceInverseProperties D γ M0 M1 G)

include hD hT hS h hcoordinates hγ hG

theorem n05CanonicalGlobalInverse_positive_angularJet :
    ∃ B : ℝ, 0 < B ∧ ∀ F : CanonicalSequence S K,
      SourceMember D γ M0 (n05CanonicalNormalizedSource D S C K F) →
      ∀ j : ℕ, 0 < j → ∀ fder : PolarPoint → ℝ,
      SourceDerivativeMember D γ M0 fder →
      n05_weakReferenceAngularJet D (n05CanonicalNormalizedSource D S C K F).1 fder j →
      ∃ d : PolarPoint → ℝ, Function.Periodic d (0, Real.pi) ∧
        MemLp d 2 (referenceWeightedMeasure D γ (-M1)) ∧
        (∀ m, WeakCanonicalAngularDerivative S K m
          ((n05CanonicalGlobalInverse D S C K G F).1 m)
          (n05CanonicalAngularJetSequence S K (n05CanonicalGlobalInverse D S C K G F).1 j m) j) ∧
        (∀ m, (n05CanonicalAngularJetSequence S K
          (n05CanonicalGlobalInverse D S C K G F).1 j m : PolarPoint → ℝ)
            =ᵐ[canonicalMeasure S K m] canonicalHeight S K (C.referenceState, 0) m d) ∧
        ‖n05CanonicalAngularJetSequence S K (n05CanonicalGlobalInverse D S C K G F).1 j‖ ^ 2 +
          outputNormSquare D γ M1 0 (d, 0) ≤ B *
            (sourceNormSquare D γ M0 (fder, 0) + (2 : ℝ) ^ (2 * j) *
              sourceNormSquare D γ M0 (n05CanonicalNormalizedSource D S C K F)) := by
  obtain ⟨B, hB, hjets⟩ :=
    n05_referenceInverse_canonicalAngularJet_bound hD hT hS h hcoordinates hγ hG
  obtain ⟨_, _, hbase⟩ :=
    n05_outputRealization_canonicalHeight_choice_bound hD hT hS h hcoordinates hγ M1
  refine ⟨B, hB, fun F hF j hj fder hfd hweak => ?_⟩
  let U := G (n05CanonicalNormalizedSource D S C K F)
  let a := n05_referenceLeftConstant D U
  obtain ⟨b, hb⟩ := (hG.1 _ hF).1
  have hU : OutputRealization D γ M1 a U := by
    rw [show a = b from n05_referenceLeftConstant_eq hD.1 hD.2.2.2.1 hγ hb]
    exact hb
  have hrep := (hbase a U hU).1
  obtain ⟨d, hdp, _, hcut, hd, hdrep, hbound⟩ := hjets _ hF j hj fder hfd hweak
  have hab : D.a ≤ D.b := hD.1.choose_spec.1.2.1.le
  have hpart : RadialPartition D := hD.1.choose_spec.2.1
  have hdphys : MemLp d 2 (radialPhysicalMeasure D) :=
    r11b_sourceDerivative_memLp hD.1 hγ ((memLp_referenceWeightedMeasure_iff hab hpart).mp hd)
  have hu : MemLp (fun p => U.1 p - a * S.chiLeft p.1) 2
      (radialPhysicalMeasure D) :=
    (r11b_output_memLp hD.1 hD.2.2.2.1 hγ ⟨a, hU⟩).sub
      ((r11b_continuous_memLp (D := D)
        (hS.2.2.1.1.continuous.comp continuous_fst)).const_mul a)
  have hup : Function.Periodic (fun p => U.1 p - a * S.chiLeft p.1) (0, Real.pi) := by
    intro p
    change U.1 (p + (0, Real.pi)) - a * S.chiLeft (p + (0, Real.pi)).1 =
      U.1 p - a * S.chiLeft p.1
    rw [hU.2.2.1 p]
    simp only [Prod.fst_add, add_zero]
  have hcanonical (m : ℕ) : WeakCanonicalAngularDerivative S K m
      ((n05CanonicalGlobalInverse D S C K G F).1 m)
      (n05CanonicalHeightL2Sequence S C K d m) j :=
    n05_weakCanonicalAngularDerivative_of_physical hab h hcoordinates m j
      hup hdp hu hdphys (hcut a) (hrep m) (hdrep m)
  have he := n05CanonicalAngularJetSequence_eq_of_weak hcanonical
  refine ⟨d, hdp, hd, ?_, ?_, ?_⟩
  · intro m
    rw [he]
    exact hcanonical m
  · simpa only [he] using hdrep
  · simpa only [he] using hbound

/-- The local bound retains the chosen physical endpoint exponent. Its
constant and coefficient power precede every angular order and source. -/
theorem n05CanonicalGlobalInverse_angularJet_endpoint_piece_bound :
    ∃ B A : ℝ, 0 < B ∧ 0 < A ∧ ∀ F : CanonicalSequence S K,
      SourceMember D γ M0 (n05CanonicalNormalizedSource D S C K F) →
      ∀ j : ℕ, 0 < j → ∀ fder : PolarPoint → ℝ,
      SourceDerivativeMember D γ M0 fder →
      n05_weakReferenceAngularJet D (n05CanonicalNormalizedSource D S C K F).1 fder j →
      ∀ k : ℕ,
        Real.exp (2 * γ * radialS (D.cellIndex (K.cell k))) *
          ‖n05CanonicalAngularJetSequence S K (n05CanonicalGlobalInverse D S C K G F).1 j k‖ ^ 2 ≤
        B * radialE (D.cellIndex (K.cell k)) ^ A *
          (sourceNormSquare D γ M0 (fder, 0) + (2 : ℝ) ^ (2 * j) *
            sourceNormSquare D γ M0 (n05CanonicalNormalizedSource D S C K F)) := by
  obtain ⟨Cj, hCj, hjet⟩ :=
    n05CanonicalGlobalInverse_positive_angularJet hD hT hS h hcoordinates hγ hG
  obtain ⟨Cp, A, hCp, hA, hpiece⟩ :=
    n05_canonicalHeight_output_piece_bound hD.1 hT h hcoordinates hγ.le M1
  refine ⟨Cp * Cj, A, mul_pos hCp hCj, hA, fun F hF j hj fder hfd hweak k => ?_⟩
  obtain ⟨d, _, hd, _, hrep, hbound⟩ := hjet F hF j hj fder hfd hweak
  have hab : D.a ≤ D.b := hD.1.choose_spec.1.2.1.le
  obtain ⟨hc, hs⟩ :=
    (memLp_referenceWeightedMeasure_iff hab hD.1.choose_spec.2.1).mp hd
  have hsout : Summable (outputCellSquare D γ M1 d) := by
    simpa only [sourceCellSquare_neg_fun] using hs
  have hout : outputNormSquare D γ M1 0 (d, 0) ≤ Cj *
      (sourceNormSquare D γ M0 (fder, 0) + (2 : ℝ) ^ (2 * j) *
        sourceNormSquare D γ M0 (n05CanonicalNormalizedSource D S C K F)) := by
    nlinarith only [hbound, sq_nonneg
      ‖n05CanonicalAngularJetSequence S K (n05CanonicalGlobalInverse D S C K G F).1 j‖]
  have he : (∑' m, outputCellSquare D γ M1 d m) =
      outputNormSquare D γ M1 0 (d, 0) := by
    simp only [outputNormSquare, n05_outputRemainder_zero,
      zero_pow (by decide : 2 ≠ 0), zero_add]
  have hp := hpiece k d
    (n05CanonicalAngularJetSequence S K (n05CanonicalGlobalInverse D S C K G F).1 j k)
    hc hsout (hrep k)
  rw [he] at hp
  have hEk : 0 < radialE (D.cellIndex (K.cell k)) := Real.exp_pos _
  calc
    _ ≤ Cp * radialE (D.cellIndex (K.cell k)) ^ A * outputNormSquare D γ M1 0 (d, 0) := hp
    _ ≤ Cp * radialE (D.cellIndex (K.cell k)) ^ A * (Cj *
        (sourceNormSquare D γ M0 (fder, 0) + (2 : ℝ) ^ (2 * j) *
          sourceNormSquare D γ M0 (n05CanonicalNormalizedSource D S C K F))) :=
      mul_le_mul_of_nonneg_left hout (by positivity)
    _ = _ := by ring

end ContinuousFlexibility.Statements
