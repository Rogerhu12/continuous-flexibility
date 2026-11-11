import ContinuousFlexibility.Analysis.N05ReferenceOutputWeightWindow
import ContinuousFlexibility.Analysis.N05ReferencePieceIndexBounds
import ContinuousFlexibility.Radial.R11bPhysicalMultiplier
import ContinuousFlexibility.Radial.ReferenceCellAlgebra

/-!
# A physical output bound on one actual canonical piece

The physical partition controls a genuine piece indicator. The endpoint
factor of that piece is retained on the left, so this estimate can be used
at both reference exponents for the same output. No endpoint attenuation
is spent in passing from the localized physical norms to the piece.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open ContinuousFlexibility.Radial

theorem n05_referenceOutput_piece_square_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε γ : ℝ}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (h04 : N04Properties D T S C L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    (hγ : 0 ≤ γ) (M : ℝ) :
    ∃ C0 A : ℝ, 0 < C0 ∧ 0 < A ∧ ∀ (k : ℕ) (f : PolarPoint → ℝ),
      RadialCellIntegrable D f → Summable (outputCellSquare D γ M f) →
      MemLp f 2 (volume.restrict
        (Ioo (K.physicalLeft k) (K.physicalRight k) ×ˢ Ioc (0 : ℝ) Real.pi)) ∧
      Real.exp (2 * γ * radialS (D.cellIndex (K.cell k))) *
        (∫ p, f p ^ 2 ∂volume.restrict
          (Ioo (K.physicalLeft k) (K.physicalRight k) ×ˢ Ioc (0 : ℝ) Real.pi)) ≤
        C0 * radialE (D.cellIndex (K.cell k)) ^ A *
          ∑' j, outputCellSquare D γ M f j := by
  obtain ⟨window, hwindow, hindex⟩ := n05_referencePiece_cell_index_bound hT hcoordinates
  obtain ⟨C0, A, hC0, hA, hweight⟩ :=
    n05_referenceOutputWeight_index_window hwindow.le hγ M
  have hpart := hD.choose_spec.2.1
  have hab := hD.choose_spec.1.2.1.le
  obtain ⟨B, hB⟩ := hpart.2.2.2.2.2
  let C1 : ℝ := (B : ℝ) * C0 * (2 * Real.pi)
  have hC1 : 0 ≤ C1 := by dsimp only [C1]; positivity
  refine ⟨C1 + 1, A, by positivity, hA, ?_⟩
  intro k f hf hsum
  let n : ℕ := D.cellIndex (K.cell k)
  let e : ℝ := Real.exp (2 * γ * radialS n)
  let E : ℝ := radialE n ^ A
  let P : Set PolarPoint :=
    Ioo (K.physicalLeft k) (K.physicalRight k) ×ˢ Ioc (0 : ℝ) Real.pi
  let a : PolarPoint → ℝ := (physicalPieceOpen S K k).indicator
    (fun _ => Real.sqrt e)
  let weights : ℕ → ℝ := fun j => C0 * E *
    Real.exp (-2 * M * radialQ (D.cellIndex j) + 2 * γ * radialS (D.cellIndex j))
  have he : 0 < e := Real.exp_pos _
  have hE : 0 < E := Real.rpow_pos_of_pos (Real.exp_pos _) _
  have ha : AEStronglyMeasurable a (radialPhysicalMeasure D) :=
    (measurable_const.indicator (measurableSet_Ioo.prod MeasurableSet.univ)).aestronglyMeasurable
  have hbound (j : ℕ) : ∀ᵐ p ∂radialPhysicalMeasure D,
      D.localizer j p.1 ≠ 0 → |a p| ^ 2 ≤ weights j := by
    apply Eventually.of_forall
    intro p hpj
    by_cases hp : p ∈ physicalPieceOpen S K k
    · have hrj : p.1 ∈ D.cells j := hpart.2.2.1 j hpj
      dsimp only [a]
      rw [indicator_of_mem hp, sq_abs, Real.sq_sqrt he.le]
      exact hweight (D.cellIndex j) n (hindex k j p.1 hp.1 hrj)
    · dsimp only [a]
      rw [indicator_of_notMem hp, abs_zero, zero_pow (by decide : 2 ≠ 0)]
      dsimp only [weights]
      positivity
  have hterm (j : ℕ) : weights j *
      (∫ p, (D.localizer j p.1 * f p) ^ 2 ∂radialPhysicalMeasure D) =
      (C0 * E * (2 * Real.pi)) * outputCellSquare D γ M f j := by
    rw [outputCellSquare, referenceCellSquare_eq_integral hab j hf]
    dsimp only [weights]
    field_simp [Real.pi_ne_zero] <;> ring
  have hsumI : Summable (fun j => weights j *
      ∫ p, (D.localizer j p.1 * f p) ^ 2 ∂radialPhysicalMeasure D) :=
    (hsum.mul_left (C0 * E * (2 * Real.pi))).congr (fun j => (hterm j).symm)
  have hpartition : ∀ᵐ p ∂radialPhysicalMeasure D,
      (∑' j, D.localizer j p.1) = 1 := by
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)] with p hp
    exact (hpart.2.2.2.2.1 p.1 hp.1).2
  obtain ⟨haf, hI⟩ := r11b_memLp_mul_of_localized_square_bound
    (fun (j : ℕ) (p : PolarPoint) => D.localizer j p.1) f a weights hf ha
    (fun j => by dsimp only [weights]; positivity) hbound
    (Eventually.of_forall (fun p => (hB p.1).1))
    (Eventually.of_forall (fun p => (hB p.1).2)) hpartition hsumI
  have hsumEq : (∑' j, weights j *
      ∫ p, (D.localizer j p.1 * f p) ^ 2 ∂radialPhysicalMeasure D) =
      (C0 * E * (2 * Real.pi)) * ∑' j, outputCellSquare D γ M f j := by
    simp_rw [hterm]
    exact tsum_mul_left
  rw [hsumEq] at hI
  have hpieces := h04
  rcases hpieces with ⟨_, _, _, hpieces, _⟩
  have hsub : P ⊆ radialCore D ×ˢ Ioc (0 : ℝ) (2 * Real.pi) := by
    intro p hp
    exact ⟨(hpieces k).2.2 hp.1, hp.2.1,
      hp.2.2.trans (by linarith only [Real.pi_pos])⟩
  have hmeasure : volume.restrict P ≤ radialPhysicalMeasure D :=
    Measure.restrict_mono hsub le_rfl
  have heq : (fun p => a p * f p) =ᵐ[volume.restrict P]
      (fun p => Real.sqrt e * f p) := by
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)] with p hp
    change a p * f p = Real.sqrt e * f p
    dsimp only [a]
    rw [indicator_of_mem (show p ∈ physicalPieceOpen S K k from ⟨hp.1, mem_univ _⟩)]
  have hscaled : MemLp (fun p => Real.sqrt e * f p) 2 (volume.restrict P) :=
    MemLp.ae_eq heq (haf.mono_measure hmeasure)
  have hlocal : MemLp f 2 (volume.restrict P) := by
    apply MemLp.ae_eq _ (hscaled.const_mul (Real.sqrt e)⁻¹)
    exact Eventually.of_forall fun p => by
      change (Real.sqrt e)⁻¹ * (Real.sqrt e * f p) = f p
      rw [← mul_assoc, inv_mul_cancel₀ (Real.sqrt_pos.mpr he).ne', one_mul]
  refine ⟨hlocal, ?_⟩
  have hnonneg : 0 ≤ ∑' j, outputCellSquare D γ M f j :=
    tsum_nonneg (fun j => outputCellSquare_nonneg hab γ M hf j)
  change e * (∫ p, f p ^ 2 ∂volume.restrict P) ≤ (C1 + 1) * E * _
  calc
    _ = ∫ p, (a p * f p) ^ 2 ∂volume.restrict P := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [heq] with p hp
      change e * f p ^ 2 = (a p * f p) ^ 2
      rw [hp, mul_pow, Real.sq_sqrt he.le]
    _ ≤ ∫ p, (a p * f p) ^ 2 ∂radialPhysicalMeasure D :=
      integral_mono_measure hmeasure (Eventually.of_forall (fun _ => sq_nonneg _))
        haf.integrable_sq
    _ ≤ (B : ℝ) * ((C0 * E * (2 * Real.pi)) *
        ∑' j, outputCellSquare D γ M f j) := hI
    _ = C1 * E * ∑' j, outputCellSquare D γ M f j := by dsimp only [C1]; ring
    _ ≤ (C1 + 1) * E * ∑' j, outputCellSquare D γ M f j :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith) hE.le) hnonneg

end ContinuousFlexibility.Statements
