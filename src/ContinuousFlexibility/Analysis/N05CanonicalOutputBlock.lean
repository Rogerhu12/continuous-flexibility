import ContinuousFlexibility.Analysis.N05CanonicalGeometryAccess
import ContinuousFlexibility.Analysis.N05ReferenceOutputBlock
import ContinuousFlexibility.Analysis.N05CanonicalOutputChange
import ContinuousFlexibility.Analysis.N05CanonicalSourceCoefficient
import ContinuousFlexibility.Analysis.N05ReferenceCutoffChange
import ContinuousFlexibility.Radial.ReferenceGraphNorms

/-!
# The actual canonical output block with its endpoint factor

The square of the actual height transform is integrated with its genuine
Jacobian density. The physical piece estimate then retains the endpoint
factor needed to compare the two bounds for the same inverse output.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open ContinuousFlexibility.Radial

theorem n05_canonicalHeight_output_piece_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε γ : ℝ}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    (hγ : 0 ≤ γ) (M : ℝ) :
    ∃ C0 A : ℝ, 0 < C0 ∧ 0 < A ∧ ∀ (k : ℕ) (f : PolarPoint → ℝ)
      (u : CanonicalL2 S K k), RadialCellIntegrable D f →
      Summable (outputCellSquare D γ M f) →
      ((u : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K k]
        canonicalHeight S K (C.referenceState, 0) k f) →
      Real.exp (2 * γ * radialS (D.cellIndex (K.cell k))) * ‖u‖ ^ 2 ≤
        C0 * radialE (D.cellIndex (K.cell k)) ^ A *
          ∑' j, outputCellSquare D γ M f j := by
  obtain ⟨C0, A0, hC0, hA0, hpiece⟩ :=
    n05_referenceOutput_piece_square_bound hD hT h.2.2.2.2.1 hcoordinates hγ M
  obtain ⟨B, A, hB, hA, hdensity⟩ :=
    n05_referenceCanonicalHeight_density_piece_bound h hcoordinates
  refine ⟨B * C0, A + A0, mul_pos hB hC0, add_pos hA hA0, ?_⟩
  intro k f u hf hsum hrep
  obtain ⟨hfP, hbound⟩ := hpiece k f hf hsum
  have h01 := h.1.1.1
  have hz : (C.referenceState, 0) ∈ stateNeighborhood S C base ε :=
    n05_referenceState_mem h01.2.1
  have hs : stateSector S C.referenceState := n05_referenceState_sector h01.2.2.1
  have hangle : ∀ p ∈ referencePhysicalPieceOpen S K k,
      (K.chart (C.referenceState, 0) k p).2 = p.2 :=
    fun _ hp => n05_controlledReference_chart_second hcoordinates k hp
  let n : ℕ := D.cellIndex (K.cell k)
  have hE : 0 < radialE n := Real.exp_pos _
  let P : Set PolarPoint :=
    Ioo (K.physicalLeft k) (K.physicalRight k) ×ˢ Ioc (0 : ℝ) Real.pi
  let q : PolarPoint → ℝ := fun p =>
    |planeJacobian (K.chart (C.referenceState, 0) k) p| *
      (f p / K.height (C.referenceState, 0) k p) ^ 2
  have hu : MemLp (canonicalHeight S K (C.referenceState, 0) k f) 2
      (canonicalMeasure S K k) := MemLp.ae_eq hrep (Lp.memLp u)
  have hq : Integrable q (volume.restrict P) :=
    (n05_referenceCanonicalHeight_sq_integrable_iff h.2.2.2.2.1 hz hs k hangle f).mp hu.integrable_sq
  have hnorm : ‖u‖ ^ 2 = ∫ p, q p ∂volume.restrict P := by
    calc
      _ = ∫ p, u p ^ 2 ∂canonicalMeasure S K k := by
        simpa only [Lp.toLp_coeFn] using reference_memLp_norm_sq_eq_integral (Lp.memLp u)
      _ = ∫ p, canonicalHeight S K (C.referenceState, 0) k f p ^ 2
          ∂canonicalMeasure S K k := by
        apply integral_congr_ae
        filter_upwards [hrep] with p hp
        exact congrArg (fun x : ℝ => x ^ 2) hp
      _ = _ := n05_referenceCanonicalHeight_sq_integral h.2.2.2.2.1 hz hs k hangle f
  have hlocal : ‖u‖ ^ 2 ≤ B * radialE n ^ A *
      ∫ p, f p ^ 2 ∂volume.restrict P := by
    rw [hnorm, ← integral_const_mul]
    apply integral_mono_ae hq (hfP.integrable_sq.const_mul _)
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)] with p hp
    have hc := mul_le_mul_of_nonneg_right
      (hdensity k p ⟨hp.1, mem_univ _⟩) (sq_nonneg (f p))
    convert hc using 1 <;> dsimp only [q, n] <;> simp only [div_eq_mul_inv] <;> ring
  calc
    _ ≤ Real.exp (2 * γ * radialS n) *
        (B * radialE n ^ A * ∫ p, f p ^ 2 ∂volume.restrict P) :=
      mul_le_mul_of_nonneg_left hlocal (Real.exp_pos _).le
    _ = (B * radialE n ^ A) *
        (Real.exp (2 * γ * radialS n) * ∫ p, f p ^ 2 ∂volume.restrict P) := by ring
    _ ≤ (B * radialE n ^ A) *
        (C0 * radialE n ^ A0 * ∑' j, outputCellSquare D γ M f j) :=
      mul_le_mul_of_nonneg_left hbound
        (mul_nonneg hB.le (Real.rpow_nonneg hE.le A))
    _ = _ := by rw [Real.rpow_add hE]; ring

/-- The same estimate uses the left scalar selected for the physical
inverse, with the actual physical-space cutoff in its canonical output. -/
theorem n05_outputRealization_canonical_piece_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε γ : ℝ}
    (hD : IsRadialReference D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    (hγ : 0 ≤ γ) (M : ℝ) :
    ∃ C0 A : ℝ, 0 < C0 ∧ 0 < A ∧ ∀ (k : ℕ) (a : ℝ) (U : RadialUnknown)
      (u : CanonicalL2 S K k), OutputRealization D γ M a U →
      ((u : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K k]
        canonicalHeight S K (C.referenceState, 0) k
          (fun p => U.1 p - a * S.chiLeft p.1)) →
      Real.exp (2 * γ * radialS (D.cellIndex (K.cell k))) * ‖u‖ ^ 2 ≤
        C0 * radialE (D.cellIndex (K.cell k)) ^ A * outputNormSquare D γ M a U := by
  obtain ⟨C0, A, hC0, hA, hpiece⟩ :=
    n05_canonicalHeight_output_piece_bound hD.1 hT h hcoordinates hγ M
  obtain ⟨C1, hC1, hcutoff⟩ :=
    n05_outputRemainder_cutoff_bound hD.1 hD.2.2.2.1 hS.2.2.1 γ M
  refine ⟨C0 * C1, A, mul_pos hC0 hC1, hA, fun k a U u hU hrep => ?_⟩
  obtain ⟨hf, hsum, hbound⟩ := hcutoff a U hU
  have hE : 0 < radialE (D.cellIndex (K.cell k)) := Real.exp_pos _
  calc
    _ ≤ C0 * radialE (D.cellIndex (K.cell k)) ^ A *
        ∑' j, outputCellSquare D γ M (fun p => U.1 p - a * S.chiLeft p.1) j :=
      hpiece k _ u hf hsum hrep
    _ ≤ C0 * radialE (D.cellIndex (K.cell k)) ^ A *
        (C1 * outputNormSquare D γ M a U) :=
      mul_le_mul_of_nonneg_left hbound
        (mul_nonneg hC0.le (Real.rpow_nonneg hE.le A))
    _ = _ := by ring

end ContinuousFlexibility.Statements
