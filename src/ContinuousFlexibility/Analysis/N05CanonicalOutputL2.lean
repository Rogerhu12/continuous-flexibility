import ContinuousFlexibility.Analysis.N05CanonicalOutputChange
import ContinuousFlexibility.Analysis.N05CanonicalOutputMultiplier
import ContinuousFlexibility.Analysis.N05CanonicalSourceCoefficient
import ContinuousFlexibility.Analysis.N05ReferenceCutoffChange
import ContinuousFlexibility.Geometry.EuclideanRigidity
import ContinuousFlexibility.Radial.ReferenceGraphNorms

/-!
# Physical reference outputs define canonical L² sequences

The actual output remainder is corrected from the reference cutoff to the
physical-space cutoff. A genuine measurable piece coefficient majorant is
integrable by positive attenuation. Change of variables on the pairwise
disjoint physical pieces gives the square-summable canonical height sequence.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ENNReal
open ContinuousFlexibility.Radial

/-- A positively weighted field has an actual canonical L² height
sequence. No angular parity or compatibility is required of the field,
so this also applies to every actual angular derivative. -/
theorem n05_referenceOutput_canonicalHeight_l2Sequence
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    {γ : ℝ} (hγ : 0 < γ) (M : ℝ) :
    ∃ C0 : ℝ, 0 < C0 ∧ ∀ f : PolarPoint → ℝ,
      RadialCellIntegrable D f → Summable (outputCellSquare D γ M f) →
      ∃ v : CanonicalL2Sequence S K,
        (∀ m, (v m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
          canonicalHeight S K (C.referenceState, 0) m f) ∧
        ‖v‖ ^ 2 ≤ C0 * ∑' m, outputCellSquare D γ M f m := by
  obtain ⟨B, A, hB, hA, hcoefficient⟩ :=
    n05_referenceCanonicalHeight_density_piece_bound h hcoordinates
  obtain ⟨C0, hC0, hmultiplier⟩ :=
    n05CanonicalOutputMajorant_memLp hD hT h.2.2.2.2 hcoordinates hB hA.le hγ M
  refine ⟨C0, hC0, fun f hf hsumf => ?_⟩
  let b : PolarPoint → ℝ := n05CanonicalOutputMajorant D S K B A
  let P : ℕ → Set PolarPoint := fun m =>
    Ioo (K.physicalLeft m) (K.physicalRight m) ×ˢ Ioc (0 : ℝ) Real.pi
  obtain ⟨hbf, hnormbf⟩ := hmultiplier f hf hsumf
  have hfmeas : AEStronglyMeasurable f (radialPhysicalMeasure D) :=
    hf.aestronglyMeasurable hD.choose_spec.2.1
  have h01 := h.1.1.1
  have hz : (C.referenceState, 0) ∈ stateNeighborhood S C base ε :=
    n05_referenceState_mem h01.2.1
  have hs : stateSector S C.referenceState :=
    n05_referenceState_sector h01.2.2.1
  have hangle (m : ℕ) : ∀ p ∈ physicalPieceOpen S K m,
      (K.chart (C.referenceState, 0) m p).2 = p.2 :=
    fun _ hp => n05_controlledReference_chart_second hcoordinates m hp
  have hcharts := h.2.2.2.2
  rcases hcharts with ⟨_, _, _, hpieces, _, _, _, hcharts, _⟩
  have hsub (m : ℕ) : P m ⊆ radialCore D ×ˢ Ioc (0 : ℝ) (2 * Real.pi) := by
    intro p hp
    exact ⟨(hpieces m).2.2 hp.1, hp.2.1,
      hp.2.2.trans (by linarith only [Real.pi_pos])⟩
  have hmeasure (m : ℕ) :
      volume.restrict (P m) ≤ radialPhysicalMeasure D :=
    Measure.restrict_mono (hsub m) le_rfl
  have hlocal (m : ℕ) :
      MemLp (canonicalHeight S K (C.referenceState, 0) m f) 2
        (canonicalMeasure S K m) ∧
      (∫ p, canonicalHeight S K (C.referenceState, 0) m f p ^ 2
        ∂canonicalMeasure S K m) ≤
      ∫ p, (b p * f p) ^ 2 ∂volume.restrict (P m) := by
    obtain ⟨_, _, _, _, hchart, _, hheight, _⟩ :=
      hcharts (C.referenceState, 0) hz hs m
    have hh : AEStronglyMeasurable (K.height (C.referenceState, 0) m)
        (volume.restrict (P m)) :=
      (hheight.continuousOn.mono (fun _ hp => ⟨hp.1, mem_univ _⟩)).aestronglyMeasurable
        (measurableSet_Ioo.prod measurableSet_Ioc)
    have hjcont : ContinuousOn (planeJacobian (K.chart (C.referenceState, 0) m)) (P m) := by
      intro p hp
      exact (contDiffAt_planeJacobian
        (hchart.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds
          ⟨hp.1, mem_univ _⟩))).continuousAt.continuousWithinAt
    have hj : AEStronglyMeasurable
        (fun p => |planeJacobian (K.chart (C.referenceState, 0) m) p|)
        (volume.restrict (P m)) :=
      hjcont.abs.aestronglyMeasurable (measurableSet_Ioo.prod measurableSet_Ioc)
    have hmeas : AEStronglyMeasurable
        (fun p => |planeJacobian (K.chart (C.referenceState, 0) m) p| *
          (f p / K.height (C.referenceState, 0) m p) ^ 2)
        (volume.restrict (P m)) :=
      hj.mul (((hfmeas.mono_measure (hmeasure m)).div₀ hh).pow 2)
    have hmajor : Integrable (fun p => (b p * f p) ^ 2)
        (volume.restrict (P m)) :=
      hbf.integrable_sq.mono_measure (hmeasure m)
    have hdom : ∀ᵐ p ∂volume.restrict (P m),
        |planeJacobian (K.chart (C.referenceState, 0) m) p| *
          (f p / K.height (C.referenceState, 0) m p) ^ 2 ≤ (b p * f p) ^ 2 := by
      filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)] with p hp
      have hpo : p ∈ physicalPieceOpen S K m := ⟨hp.1, mem_univ _⟩
      have hb : |planeJacobian (K.chart (C.referenceState, 0) m) p| *
          (K.height (C.referenceState, 0) m p)⁻¹ ^ 2 ≤ b p ^ 2 := by
        exact (hcoefficient m p hpo).trans_eq
          (n05CanonicalOutputMajorant_sq h.2.2.2.2 hB.le m hpo).symm
      calc
        _ = (|planeJacobian (K.chart (C.referenceState, 0) m) p| *
            (K.height (C.referenceState, 0) m p)⁻¹ ^ 2) * f p ^ 2 := by
          simp only [div_eq_mul_inv]
          ring
        _ ≤ b p ^ 2 * f p ^ 2 := mul_le_mul_of_nonneg_right hb (sq_nonneg _)
        _ = _ := (mul_pow _ _ 2).symm
    have hint : Integrable
        (fun p => |planeJacobian (K.chart (C.referenceState, 0) m) p| *
          (f p / K.height (C.referenceState, 0) m p) ^ 2)
        (volume.restrict (P m)) := by
      apply hmajor.mono' hmeas
      filter_upwards [hdom] with p hp
      change ‖|planeJacobian (K.chart (C.referenceState, 0) m) p| *
        (f p / K.height (C.referenceState, 0) m p) ^ 2‖ ≤ _
      rw [Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg (abs_nonneg (planeJacobian (K.chart (C.referenceState, 0) m) p))
          (sq_nonneg (f p / K.height (C.referenceState, 0) m p)))]
      exact hp
    refine ⟨(memLp_two_iff_integrable_sq
      (n05_canonicalHeight_aestronglyMeasurable h.2.2.2.2 hz hs m (hangle m)
        hfmeas)).mpr
      ((n05_canonicalHeight_sq_integrable_iff h.2.2.2.2 hz hs m (hangle m) f).mpr hint), ?_⟩
    rw [n05_canonicalHeight_sq_integral h.2.2.2.2 hz hs m (hangle m) f]
    exact integral_mono_ae hint hmajor hdom
  have hsubUnion : (⋃ m, P m) ⊆ radialCore D ×ˢ Ioc (0 : ℝ) (2 * Real.pi) := by
    intro p hp
    obtain ⟨m, hm⟩ := mem_iUnion.mp hp
    exact hsub m hm
  have hdisjoint : Pairwise (fun m n => Disjoint (P m) (P n)) := by
    intro m n hmn
    apply Set.disjoint_left.mpr
    intro p hm hn
    exact Set.disjoint_left.mp (n05_physicalPieces_pairwise_disjoint h.2.2.2.2 hmn)
      hm.1 hn.1
  have hUnion : IntegrableOn (fun p => (b p * f p) ^ 2) (⋃ m, P m) volume :=
    hbf.integrable_sq.mono_measure (Measure.restrict_mono hsubUnion le_rfl)
  have hmajorSum := hasSum_integral_iUnion
    (fun _ => measurableSet_Ioo.prod measurableSet_Ioc) hdisjoint hUnion
  have hsum : Summable (fun m => ∫ p,
      canonicalHeight S K (C.referenceState, 0) m f p ^ 2 ∂canonicalMeasure S K m) :=
    Summable.of_nonneg_of_le (fun _ => integral_nonneg (fun _ => sq_nonneg _))
      (fun m => (hlocal m).2) hmajorSum.summable
  let v : CanonicalSequence S K := fun m =>
    (hlocal m).1.toLp (canonicalHeight S K (C.referenceState, 0) m f)
  have hvnorm (m : ℕ) : ‖v m‖ ^ 2 = ∫ p,
      canonicalHeight S K (C.referenceState, 0) m f p ^ 2 ∂canonicalMeasure S K m :=
    reference_memLp_norm_sq_eq_integral (hlocal m).1
  have hvmem : Memℓp v 2 := by
    apply memℓp_gen
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, hvnorm] using hsum
  refine ⟨⟨v, hvmem⟩, fun m => (hlocal m).1.coeFn_toLp, ?_⟩
  have hnorm : ‖(⟨v, hvmem⟩ : CanonicalL2Sequence S K)‖ ^ 2 =
      ∑' m, ∫ p, canonicalHeight S K (C.referenceState, 0) m f p ^ 2
        ∂canonicalMeasure S K m := by
    calc
      _ = ∑' m, ‖v m‖ ^ 2 := by
        simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
          lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ENNReal).toReal)
            (⟨v, hvmem⟩ : CanonicalL2Sequence S K)
      _ = _ := tsum_congr hvnorm
  rw [hnorm]
  calc
    _ ≤ ∑' m, ∫ p, (b p * f p) ^ 2 ∂volume.restrict (P m) :=
      hsum.tsum_le_tsum (fun m => (hlocal m).2) hmajorSum.summable
    _ = ∫ p, (b p * f p) ^ 2 ∂volume.restrict (⋃ m, P m) := hmajorSum.tsum_eq
    _ ≤ ∫ p, (b p * f p) ^ 2 ∂radialPhysicalMeasure D :=
      integral_mono_measure (Measure.restrict_mono hsubUnion le_rfl)
        (Eventually.of_forall (fun _ => sq_nonneg _)) hbf.integrable_sq
    _ ≤ C0 * ∑' m, outputCellSquare D γ M f m := hnormbf

/-- Subtracting the same selected left scalar times the physical-space
cutoff gives the actual canonical sequence of an inverse output. -/
theorem n05_outputRealization_canonicalHeight_l2Sequence
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ}
    (hD : IsRadialReference D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    {γ : ℝ} (hγ : 0 < γ) (M : ℝ) :
    ∃ C0 : ℝ, 0 < C0 ∧ ∀ (a : ℝ) (U : RadialUnknown),
      OutputRealization D γ M a U →
      ∃ v : CanonicalL2Sequence S K,
        (∀ m, (v m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
          canonicalHeight S K (C.referenceState, 0) m
            (fun p => U.1 p - a * S.chiLeft p.1)) ∧
        ‖v‖ ^ 2 ≤ C0 * outputNormSquare D γ M a U := by
  obtain ⟨C0, hC0, houtput⟩ :=
    n05_referenceOutput_canonicalHeight_l2Sequence hD.1 hT h hcoordinates hγ M
  obtain ⟨C1, hC1, hcutoff⟩ :=
    n05_outputRemainder_cutoff_bound hD.1 hD.2.2.2.1 hS.2.2.1 γ M
  refine ⟨C0 * C1, mul_pos hC0 hC1, fun a U hU => ?_⟩
  obtain ⟨hf, hsum, hbound⟩ := hcutoff a U hU
  obtain ⟨v, hrep, hnorm⟩ := houtput _ hf hsum
  refine ⟨v, hrep, ?_⟩
  exact hnorm.trans ((mul_le_mul_of_nonneg_left hbound hC0.le).trans_eq
    (mul_assoc C0 C1 (outputNormSquare D γ M a U)).symm)

end ContinuousFlexibility.Statements
