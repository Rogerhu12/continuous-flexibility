module

public import ContinuousFlexibility.Analysis.N05ReferenceZeroRemainder
public import ContinuousFlexibility.Analysis.N05CanonicalInverseNormal
public import ContinuousFlexibility.Analysis.N05CanonicalMixedWeakJets
public import ContinuousFlexibility.Analysis.N05CanonicalOutputAngularJets
public import ContinuousFlexibility.Analysis.N05ReferenceNormalAngularSobolev

/-!
# Positive angular jets of the same canonical normal derivative

The physical first normal derivative is selected before the angular order.
Actual weak derivatives are commuted only on tests. Their canonical radial
derivatives therefore identify the angular jets of the single fixed normal
sequence, irrespective of the representative chosen by a physical estimate.
All material powers and constants precede the angular order and the source.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory ContinuousFlexibility.Radial

theorem n05CanonicalGlobalInverse_normalAngular_of_source
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
    (hD : IsRadialReference D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K) :
    ∃ A : ℝ, 0 < A ∧ ∀ σ : ℝ, 0 < σ → ∀ M0 M1 MN : ℝ,
      ∀ G : RadialSource → RadialUnknown,
      ReferenceInverseProperties D σ M0 M1 G → FirstNormalInverseEstimate D σ M0 MN G →
      ∃ B P : ℝ, 0 < B ∧ 0 < P ∧ ∀ F : CanonicalSequence S K, ∀ fθ : PolarPoint → ℝ,
      SourceMember D σ M0 (n05CanonicalNormalizedSource D S C K F) →
      SourceDerivativeMember D σ M0 fθ →
      WeakAngularDerivative D (n05CanonicalNormalizedSource D S C K F).1 fθ →
      ∀ j : ℕ, 0 < j → ∀ d e : PolarPoint → ℝ,
      SourceDerivativeMember D σ M0 d → SourceDerivativeMember D σ M0 e →
      n05_weakReferenceAngularJet D (n05CanonicalNormalizedSource D S C K F).1 d j →
      n05_weakReferenceAngularJet D (n05CanonicalNormalizedSource D S C K F).1 e (j + 1) →
      let W := n05CanonicalRadialJetSequence S K (n05CanonicalGlobalInverse D S C K G F).1
      let Wj := n05CanonicalAngularJetSequence S K W j
      let Q := sourceNormSquare D σ M0 (d, 0) + sourceNormSquare D σ M0 (e, 0) +
        (2 : ℝ) ^ (2 * j) * (sourceNormSquare D σ M0 (n05CanonicalNormalizedSource D S C K F) +
          sourceNormSquare D σ M0 (fθ, 0))
      ∃ g : PolarPoint → ℝ, Function.Periodic g (0, Real.pi) ∧
        MemLp g 2 (referenceWeightedMeasure D σ (-(max M1 MN + A))) ∧
        (∀ m, WeakCanonicalAngularDerivative S K m (W m) (Wj m) j) ∧
        (∀ m, (Wj m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
          canonicalHeight S K (C.referenceState, 0) m g) ∧
        ‖Wj‖ ^ 2 + outputNormSquare D σ (max M1 MN + A) 0 (g, 0) ≤ B * Q ∧
        ∀ k, Real.exp (2 * σ * radialS (D.cellIndex (K.cell k))) * ‖Wj k‖ ^ 2 ≤
          B * radialE (D.cellIndex (K.cell k)) ^ P * Q := by
  obtain ⟨A, hA, hradial⟩ := n05CanonicalRadialJetSequence_of_physical hD.1 hT h hcoordinates
  obtain ⟨_, _, hbaseAll⟩ := n05CanonicalGlobalInverse_normal_of_source hD hT hS h hcoordinates
  refine ⟨A, hA, fun σ hσ M0 M1 MN G hG hN => ?_⟩
  let M : ℝ := max M1 MN
  obtain ⟨Cr, hCr, hradialBound⟩ := hradial σ hσ M
  obtain ⟨_, _, _, _, hbase⟩ := hbaseAll σ hσ M0 M1 MN G hG hN
  obtain ⟨Cu, hCu, hujets⟩ :=
    n05_referenceInverse_canonicalAngularJet_bound hD hT hS h hcoordinates hσ hG
  obtain ⟨CN, hCN, hnormal⟩ := n05_referenceNormal_allAngular_bound hD.1 hD.2.2.2.1 hσ hG hN
  obtain ⟨_, _, hselected⟩ :=
    n05_referenceInverse_selectedLeftConstant hD.1 hD.2.2.2.1 hσ hG
  obtain ⟨_, _, houtput⟩ :=
    n05_outputRealization_canonicalHeight_choice_bound hD hT hS h hcoordinates hσ M1
  obtain ⟨Cp, P, hCp, hP, hpiece⟩ :=
    n05_canonicalHeight_output_piece_bound hD.1 hT h hcoordinates hσ.le (M + A)
  obtain ⟨_, _, hchoice⟩ :=
    n05_referenceOutput_canonicalHeight_choice_bound hD.1 hT h hcoordinates hσ (M + A)
  let B0 : ℝ := Cr * (Cu + CN ^ 2)
  let B : ℝ := (Cp + 1) * B0
  have hB0 : 0 < B0 := by dsimp only [B0]; positivity
  have hB : 0 < B := by dsimp only [B]; positivity
  have hB0B : B0 ≤ B := by dsimp only [B]; nlinarith only [mul_nonneg hCp.le hB0.le]
  have hCpB : Cp * B0 ≤ B := by dsimp only [B]; linarith only [hB0]
  refine ⟨B, P, hB, hP, fun F fθ hF hfθ hθ => ?_⟩
  let X := n05CanonicalNormalizedSource D S C K F
  let U := G X
  let a := n05_referenceLeftConstant D U
  let u : PolarPoint → ℝ := fun p => U.1 p - a * S.chiLeft p.1
  let W := n05CanonicalRadialJetSequence S K (n05CanonicalGlobalInverse D S C K G F).1
  have hab : D.a ≤ D.b := hD.1.choose_spec.1.2.1.le
  have hpart : RadialPartition D := hD.1.choose_spec.2.1
  obtain ⟨_, _, _, _, hW, _, _, _, _⟩ := hbase F fθ hF hfθ hθ
  obtain ⟨ur, hur, _, _, hnormalJets⟩ := hnormal X hF fθ hfθ hθ
  have hU : OutputRealization D σ M1 a U := (hselected X hF).1
  have hurep := (houtput a U hU).1
  have huLp : MemLp u 2 (radialPhysicalMeasure D) :=
    (r11b_output_memLp hD.1 hD.2.2.2.1 hσ ⟨a, hU⟩).sub
      ((r11b_continuous_memLp (D := D)
        (hS.2.2.1.1.continuous.comp continuous_fst)).const_mul a)
  have hup : Function.Periodic u (0, Real.pi) := by
    intro p
    change U.1 (p + (0, Real.pi)) - a * S.chiLeft (p.1 + 0) = U.1 p - a * S.chiLeft p.1
    rw [hU.2.2.1 p, add_zero]
  intro j hj d e hd he hwd hwe
  let Wj := n05CanonicalAngularJetSequence S K W j
  let Q : ℝ := sourceNormSquare D σ M0 (d, 0) + sourceNormSquare D σ M0 (e, 0) +
    (2 : ℝ) ^ (2 * j) * (sourceNormSquare D σ M0 X + sourceNormSquare D σ M0 (fθ, 0))
  have hnn (f : PolarPoint → ℝ) : 0 ≤ sourceNormSquare D σ M0 (f, 0) :=
    r11b_sourceNormSquare_nonneg hab σ M0 (f, 0)
  have hQ : 0 ≤ Q := add_nonneg (add_nonneg (hnn d) (hnn e))
    (mul_nonneg (by positivity) (add_nonneg (sourceNormSquare_nonneg hab hF) (hnn fθ)))
  have hlow : sourceNormSquare D σ M0 (d, 0) +
      (2 : ℝ) ^ (2 * j) * sourceNormSquare D σ M0 X ≤ Q := by
    dsimp only [Q]
    nlinarith only [hnn e, mul_nonneg (show 0 ≤ (2 : ℝ) ^ (2 * j) by positivity) (hnn fθ)]
  obtain ⟨uj, hujp, hujWeak, hcut, huj, hujrep, hujBound⟩ := hujets X hF j hj d hd hwd
  obtain ⟨urj, hurjWeak, hurj, hurjBound, hurjp⟩ := hnormalJets j hj d e hd he hwd hwe
  have hujPhys : MemLp uj 2 (radialPhysicalMeasure D) :=
    r11b_sourceDerivative_memLp hD.1 hσ ((memLp_referenceWeightedMeasure_iff hab hpart).mp huj)
  have hcanonical (m : ℕ) : WeakCanonicalAngularDerivative S K m
      ((n05CanonicalGlobalInverse D S C K G F).1 m) (n05CanonicalHeightL2Sequence S C K uj m) j :=
    n05_weakCanonicalAngularDerivative_of_physical hab h hcoordinates m j
      hup hujp huLp hujPhys (hcut a) (hurep m) (hujrep m)
  have hnormalj : WeakNormalDerivative D uj urj :=
    n05_weakNormalDerivative_angularJet hur hujWeak hurjWeak
  obtain ⟨hujM, hujMono⟩ := n05_referenceOutput_weighted_mono hab hpart huj (le_max_left M1 MN)
  obtain ⟨hurjM, hurjMono⟩ := n05_referenceOutput_weighted_mono hab hpart hurj (le_max_right M1 MN)
  have hujOut : outputNormSquare D σ M 0 (uj, 0) ≤ Cu * Q := by
    have hb : outputNormSquare D σ M1 0 (uj, 0) ≤ Cu *
        (sourceNormSquare D σ M0 (d, 0) + (2 : ℝ) ^ (2 * j) * sourceNormSquare D σ M0 X) := by
      linarith only [hujBound, sq_nonneg ‖n05CanonicalHeightL2Sequence S C K uj‖]
    exact hujMono.trans (hb.trans (mul_le_mul_of_nonneg_left hlow hCu.le))
  have hurjOut : outputNormSquare D σ M 0 (urj, 0) ≤ CN ^ 2 * Q :=
    hurjMono.trans hurjBound
  let g := n05ReferenceRadialNormalField S C K uj urj
  obtain ⟨hrj, heq, hg, htotal⟩ := hradialBound uj urj hujp hurjp hujM hurjM hnormalj
  have hjet (m : ℕ) : WeakCanonicalAngularDerivative S K m (W m)
      (n05CanonicalRadialJetSequence S K (n05CanonicalHeightL2Sequence S C K uj) m) j :=
    n05WeakCanonicalRadialDerivative_angularJet (hW m) (hcanonical m) (hrj m)
  have hfixed : Wj = n05CanonicalRadialJetSequence S K (n05CanonicalHeightL2Sequence S C K uj) :=
    n05CanonicalAngularJetSequence_eq_of_weak hjet
  have htot : ‖Wj‖ ^ 2 + outputNormSquare D σ (M + A) 0 (g, 0) ≤ B0 * Q := by
    rw [hfixed]
    exact htotal.trans ((mul_le_mul_of_nonneg_left (add_le_add hujOut hurjOut) hCr.le).trans_eq
      (by dsimp only [B0]; ring))
  obtain ⟨hgc, hgs⟩ := (memLp_referenceWeightedMeasure_iff hab hpart).mp hg
  rw [sourceCellSquare_neg_fun] at hgs
  have hrep (m : ℕ) : (Wj m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      canonicalHeight S K (C.referenceState, 0) m g := by
    rw [hfixed, heq]
    exact (hchoice g hgc hgs).1 m
  refine ⟨g, n05ReferenceRadialNormalField_periodic hujp hurjp, hg,
    n05CanonicalAngularJetSequence_weak hjet, hrep,
    htot.trans (mul_le_mul_of_nonneg_right hB0B hQ), fun k => ?_⟩
  have hgBound : outputNormSquare D σ (M + A) 0 (g, 0) ≤ B0 * Q := by
    linarith only [htot, sq_nonneg ‖Wj‖]
  have hp : Real.exp (2 * σ * radialS (D.cellIndex (K.cell k))) * ‖Wj k‖ ^ 2 ≤
      Cp * radialE (D.cellIndex (K.cell k)) ^ P * outputNormSquare D σ (M + A) 0 (g, 0) := by
    simpa only [outputNormSquare, n05_outputRemainder_zero,
      zero_pow (by decide : (2 : ℕ) ≠ 0), zero_add] using hpiece k g (Wj k) hgc hgs (hrep k)
  have hEk : 0 < radialE (D.cellIndex (K.cell k)) := Real.exp_pos _
  calc
    _ ≤ Cp * radialE (D.cellIndex (K.cell k)) ^ P * (B0 * Q) :=
      hp.trans (mul_le_mul_of_nonneg_left hgBound (by positivity))
    _ = (Cp * B0) * radialE (D.cellIndex (K.cell k)) ^ P * Q := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCpB (by positivity)) hQ

end ContinuousFlexibility.Statements
