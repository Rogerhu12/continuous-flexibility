import ContinuousFlexibility.Analysis.N05ReferenceZeroRemainder
import ContinuousFlexibility.Analysis.N05CanonicalRadialField
import ContinuousFlexibility.Analysis.N05ReferenceOutputWeightInclusion
import ContinuousFlexibility.Analysis.N05ReferenceCutoffNormalBounds
import ContinuousFlexibility.Analysis.N05CanonicalOutputReflection
import ContinuousFlexibility.Analysis.N05CanonicalOutputBlock
import ContinuousFlexibility.Radial.R11bAngularFrequencySource

/-!
# The genuine first normal jet of the fixed canonical inverse

The first-normal estimate supplies an actual physical derivative. Both
remainders use the same selected left constant and the prescribed cutoff.
Their true coordinate field realizes the fixed canonical radial derivative,
with one material shift chosen before all endpoint and material exponents.
The local estimate retains its original endpoint exponential.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory ContinuousFlexibility.Radial

def n05CanonicalInverseNormalField (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (K : CanonicalData S)
    (G : RadialSource → RadialUnknown) (F : CanonicalSequence S K)
    (ur : PolarPoint → ℝ) : PolarPoint → ℝ :=
  let U := G (n05CanonicalNormalizedSource D S C K F)
  let a := n05_referenceLeftConstant D U
  n05ReferenceRadialNormalField S C K
    (fun p => U.1 p - a * S.chiLeft p.1)
    (fun p => ur p - a * deriv S.chiLeft p.1)

theorem n05CanonicalGlobalInverse_normal_of_source
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
      ∃ ur : PolarPoint → ℝ,
        let U := n05CanonicalGlobalInverse D S C K G F
        let W := n05CanonicalRadialJetSequence S K U.1
        let g := n05CanonicalInverseNormalField D S C K G F ur
        let Q := sourceNormSquare D σ M0 (n05CanonicalNormalizedSource D S C K F) +
          sourceNormSquare D σ M0 (fθ, 0)
        WeakNormalDerivative D (G (n05CanonicalNormalizedSource D S C K F)).1 ur ∧
        OutputRealization D σ MN 0 (ur, 0) ∧
        MemLp g 2 (referenceWeightedMeasure D σ (-(max M1 MN + A))) ∧
        (∀ m, n05WeakCanonicalRadialDerivative S K m (U.1 m) (W m)) ∧
        (∀ m, (W m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
          canonicalHeight S K (C.referenceState, 0) m g) ∧
        (∀ m, n05CanonicalReflection S K m (W m) = W m) ∧
        ‖W‖ ^ 2 + outputNormSquare D σ (max M1 MN + A) 0 (g, 0) ≤ B * Q ∧
        ∀ k, Real.exp (2 * σ * radialS (D.cellIndex (K.cell k))) * ‖W k‖ ^ 2 ≤
          B * radialE (D.cellIndex (K.cell k)) ^ P * Q := by
  obtain ⟨A, hA, hradial⟩ := n05CanonicalRadialJetSequence_of_physical hD.1 hT h hcoordinates
  refine ⟨A, hA, fun σ hσ M0 M1 MN G hG hN => ?_⟩
  let M : ℝ := max M1 MN
  obtain ⟨Cr, hCr, hradialBound⟩ := hradial σ hσ M
  obtain ⟨Ci, hCi, hinverse⟩ :=
    n05_referenceInverse_selectedLeftConstant hD.1 hD.2.2.2.1 hσ hG
  obtain ⟨CN, hCN, hnormal⟩ := hN
  obtain ⟨Cc, hCc, hcutoff⟩ :=
    n05_outputRemainder_cutoff_bound hD.1 hD.2.2.2.1 hS.2.2.1 σ M1
  obtain ⟨Cd, hCd, hdercutoff⟩ := n05_leftCutoff_normal_weighted_bound hD.1 hS.2.2.1 σ M
  obtain ⟨Cp, P, hCp, hP, hpiece⟩ :=
    n05_canonicalHeight_output_piece_bound hD.1 hT h hcoordinates hσ.le (M + A)
  obtain ⟨_, _, hchoice⟩ :=
    n05_referenceOutput_canonicalHeight_choice_bound hD.1 hT h hcoordinates hσ (M + A)
  let H : ℝ := Cc * Ci ^ 2 + Cd * (CN ^ 2 + Ci ^ 2)
  let B0 : ℝ := Cr * H
  let B : ℝ := (Cp + 1) * B0
  have hH : 0 < H := by dsimp only [H]; positivity
  have hB0 : 0 < B0 := mul_pos hCr hH
  have hB : 0 < B := by dsimp only [B]; positivity
  have hB0B : B0 ≤ B := by dsimp only [B]; nlinarith only [mul_nonneg hCp.le hB0.le]
  have hCpB : Cp * B0 ≤ B := by dsimp only [B]; linarith only [hB0]
  refine ⟨B, P, hB, hP, fun F fθ hF hfθ hθ => ?_⟩
  let X := n05CanonicalNormalizedSource D S C K F
  let U := G X
  let a := n05_referenceLeftConstant D U
  let u : PolarPoint → ℝ := fun p => U.1 p - a * S.chiLeft p.1
  let Q : ℝ := sourceNormSquare D σ M0 X + sourceNormSquare D σ M0 (fθ, 0)
  have hab : D.a ≤ D.b := hD.1.choose_spec.1.2.1.le
  have hpart : RadialPartition D := hD.1.choose_spec.2.1
  have hX : 0 ≤ sourceNormSquare D σ M0 X := sourceNormSquare_nonneg hab hF
  have hθnonneg : 0 ≤ sourceNormSquare D σ M0 (fθ, 0) :=
    r11b_sourceNormSquare_nonneg hab σ M0 (fθ, 0)
  have hQ : 0 ≤ Q := add_nonneg hX hθnonneg
  have hXQ : sourceNormSquare D σ M0 X ≤ Q := le_add_of_nonneg_right hθnonneg
  obtain ⟨hU, hUnorm⟩ := hinverse X hF
  obtain ⟨ur, hur, hUr, hUrnorm⟩ := hnormal X fθ hF hθ hfθ
  let v : PolarPoint → ℝ := fun p => ur p - a * deriv S.chiLeft p.1
  let g : PolarPoint → ℝ := n05ReferenceRadialNormalField S C K u v
  let W := n05CanonicalRadialJetSequence S K (n05CanonicalGlobalInverse D S C K G F).1
  obtain ⟨huc, hus, hunorm⟩ := hcutoff a U hU
  have hu1 : MemLp u 2 (referenceWeightedMeasure D σ (-M1)) :=
    memLp_referenceWeightedMeasure hab hpart huc (by simpa only [sourceCellSquare_neg_fun] using hus)
  obtain ⟨hu, huMono⟩ := n05_referenceOutput_weighted_mono hab hpart hu1 (le_max_left M1 MN)
  have huBound : outputNormSquare D σ M 0 (u, 0) ≤ Cc * Ci ^ 2 * Q := by
    have hb : outputNormSquare D σ M1 0 (u, 0) ≤ Cc * outputNormSquare D σ M1 a U := by
      simpa only [outputNormSquare, n05_outputRemainder_zero,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_add] using hunorm
    exact huMono.trans (hb.trans ((mul_le_mul_of_nonneg_left
      (hUnorm.trans (mul_le_mul_of_nonneg_left hXQ (sq_nonneg Ci))) hCc.le).trans_eq (by ring)))
  have haBound : a ^ 2 ≤ Ci ^ 2 * Q := by
    have ha : a ^ 2 ≤ outputNormSquare D σ M1 a U := by
      have hsum := tsum_nonneg (fun m => outputCellSquare_nonneg hab σ M1 hU.1 m)
      change a ^ 2 ≤ a ^ 2 + U.2 ^ 2 + _
      linarith only [hsum, sq_nonneg U.2]
    exact ha.trans (hUnorm.trans (mul_le_mul_of_nonneg_left hXQ (sq_nonneg Ci)))
  have hurN : MemLp ur 2 (referenceWeightedMeasure D σ (-MN)) := by
    simpa only [n05_outputRemainder_zero] using
      OutputRealization.memLp_weighted hab hpart hUr
  obtain ⟨hurM, hurMono⟩ := n05_referenceOutput_weighted_mono hab hpart hurN (le_max_right M1 MN)
  obtain ⟨hv, hvnorm⟩ := hdercutoff a ur hurM
  have hvBound : outputNormSquare D σ M 0 (v, 0) ≤ Cd * (CN ^ 2 + Ci ^ 2) * Q := by
    exact hvnorm.trans ((mul_le_mul_of_nonneg_left
      (add_le_add (hurMono.trans hUrnorm) haBound) hCd.le).trans_eq (by ring))
  have hup : Function.Periodic u (0, Real.pi) := by
    intro p
    change U.1 (p + (0, Real.pi)) - a * S.chiLeft (p.1 + 0) = U.1 p - a * S.chiLeft p.1
    rw [hU.2.2.1 p, add_zero]
  have hvp : Function.Periodic v (0, Real.pi) := by
    intro p
    change ur (p + (0, Real.pi)) - a * deriv S.chiLeft (p.1 + 0) = ur p - a * deriv S.chiLeft p.1
    rw [hUr.2.2.1 p, add_zero]
  have huv : WeakNormalDerivative D u v := n05_weakNormalDerivative_sub_leftCutoff
    hD.1.choose_spec.1.2.1 hS.2.2.1
    (r11b_output_memLp hD.1 hD.2.2.2.1 hσ ⟨a, hU⟩)
    (r11b_output_memLp hD.1 hD.2.2.2.1 hσ ⟨0, hUr⟩) hur a
  obtain ⟨hweak, heq, hg, htotal⟩ := hradialBound u v hup hvp hu hv huv
  have htot : ‖W‖ ^ 2 + outputNormSquare D σ (M + A) 0 (g, 0) ≤ B0 * Q := by
    exact htotal.trans ((mul_le_mul_of_nonneg_left (add_le_add huBound hvBound) hCr.le).trans_eq
      (by dsimp only [B0, H]; ring))
  obtain ⟨hgc, hgs⟩ := (memLp_referenceWeightedMeasure_iff hab hpart).mp hg
  rw [sourceCellSquare_neg_fun] at hgs
  have hrep (m : ℕ) : (W m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      canonicalHeight S K (C.referenceState, 0) m g := by
    change (n05CanonicalRadialJetSequence S K (n05CanonicalHeightL2Sequence S C K u) m :
      PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m] _
    rw [heq]
    exact (hchoice g hgc hgs).1 m
  have hgp : Function.Periodic g (0, Real.pi) := n05ReferenceRadialNormalField_periodic hup hvp
  have hgeven (r θ : ℝ) : g (r, -θ) = g (r, θ) := by
    dsimp only [g, u, v, n05ReferenceRadialNormalField, n05ReferenceNormalLeading,
      n05ReferenceNormalDrift]
    rw [hUr.2.2.2 r θ, hU.2.2.2 r θ]
  have hz : (C.referenceState, 0) ∈ stateNeighborhood S C base ε :=
    n05_referenceState_mem h.1.1.1.2.1
  have hs : stateSector S C.referenceState := n05_referenceState_sector h.1.1.1.2.2.1
  refine ⟨ur, hur, hUr, hg, hweak, hrep,
    fun m => n05_canonicalL2_reflection_of_height_rep h.2.2.2.2 hz hs hgp hgeven m (hrep m),
    htot.trans (mul_le_mul_of_nonneg_right hB0B hQ), fun k => ?_⟩
  have hgBound : outputNormSquare D σ (M + A) 0 (g, 0) ≤ B0 * Q := by
    linarith only [htot, sq_nonneg ‖W‖]
  have hp : Real.exp (2 * σ * radialS (D.cellIndex (K.cell k))) * ‖W k‖ ^ 2 ≤
      Cp * radialE (D.cellIndex (K.cell k)) ^ P * outputNormSquare D σ (M + A) 0 (g, 0) := by
    simpa only [outputNormSquare, n05_outputRemainder_zero,
      zero_pow (by decide : (2 : ℕ) ≠ 0), zero_add] using hpiece k g (W k) hgc hgs (hrep k)
  have hEk : 0 < radialE (D.cellIndex (K.cell k)) := Real.exp_pos _
  calc
    _ ≤ Cp * radialE (D.cellIndex (K.cell k)) ^ P * (B0 * Q) :=
      hp.trans (mul_le_mul_of_nonneg_left hgBound (by positivity))
    _ = (Cp * B0) * radialE (D.cellIndex (K.cell k)) ^ P * Q := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCpB (by positivity)) hQ

end ContinuousFlexibility.Statements
