import ContinuousFlexibility.Radial.PositiveBufferActualInverse
import ContinuousFlexibility.Radial.PositiveBufferCorrectedAlgebra
import ContinuousFlexibility.Radial.PositiveBufferEnergyGlobalData
import ContinuousFlexibility.Radial.PositiveBufferPoissonColumnsActual
import ContinuousFlexibility.Radial.PositiveBufferQuantitative

/-!
# Exact positive-buffer compression from the constructed Green data

This assembly retains every frozen clause: the actual interval form
graph, its unique bounded inverse, both variational endpoint profiles,
the genuine Poisson fields, and the physical conormal estimates.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory Matrix
open ContinuousFlexibility.Statements
open scoped Topology ContDiff InnerProductSpace

theorem positiveBuffer_compression_of_corrected_data {B : BufferData}
    (hB : BufferHypotheses B) (D : PositiveBufferProfileData B)
    {P K D₀ C : ℝ} (hP : 0 < P) (hK : 0 ≤ K) (hD₀ : 0 ≤ D₀)
    (hC : 0 < C) (hC1 : 1 ≤ C) (hPC : P ≤ C)
    (hKC : 8 * K ≤ C) (hKsqC : 8 * K ^ 2 ≤ C) (hDC : 2 * D₀ ≤ C)
    (hPin : ∀ i, D.alphaIn i ≤ P * B.mass i)
    (hPout : ∀ i, D.alphaOut i ≤ P * B.mass i)
    (E : PositiveBufferCorrectedData B D.A D.alphaOut K (D₀ * B.B₀))
    (hsmall : (D₀ * B.B₀) * (∑ i, (B.mass i * exp (-B.action i)) ^ 2) ≤ 1 / 4)
    (hquad : (2 * (D₀ * B.B₀)) * (∑ i, (B.mass i * exp (-B.action i)) ^ 2) ≤
      (1 / (2 * P)) / 2) :
    BufferCompressionConclusion B C := by
  have hHyp := hB
  rcases hHyp with ⟨hlh, hwalls, hB₀, hlayer, hV, hreal, hbf, hbc, hbae, hbs,
    hm, hborder, hlo, hup, H, hHnorm, hH, hHunique⟩
  have hA : ∀ i, 0 < D.A i := D.A_pos hB
  let g : Fin 2 → RadialL2 × ℝ :=
    fun i => positiveBufferBorderedState B.potential B.bordered (E.column i)
  let M := positiveBufferCutMatrix (bufferCut B) D.A E.column
  let Q : Matrix (Fin 2) (Fin 2) ℝ := M⁻¹
  have hinv := positiveBufferCorrected_inverse_matrix E hlh.le
    (fun i => (hm i).1.le) (mul_nonneg hD₀ hB₀.le) hsmall
  have hMQ : positiveBufferPoissonTraceMatrix B D.A E.representative * Q = 1 := by
    have htrace : positiveBufferPoissonTraceMatrix B D.A E.representative = M := by
      ext i j
      exact (positiveBufferCorrected_cutMatrix_eq E hlh.le i j).symm
    rw [htrace]
    exact Matrix.mul_nonsing_inv M hinv.1
  obtain ⟨G, hGnorm, hGsolve, hGunique⟩ :=
    positiveBuffer_actual_dirichlet_inverse B hlh hreal hV.continuous hborder H hHnorm hH
      D.A hA E.column (positiveBufferCorrected_form E hV.continuous) hinv.1 hinv.2.1
  let p : Fin 2 → ℝ → ℝ := positiveBufferPoissonRepresentative D.A Q E.representative
  let fields : Fin 2 → RadialL2 := positiveBufferPoissonColumnField B D.A Q E.column
  let scalars : Fin 2 → ℝ := positiveBufferPoissonColumnScalar B D.A Q E.column
  have hcols (j : Fin 2) : (fields j, scalars j) =
      positiveBufferPoissonMap B g Q D.A (Pi.single j 1) :=
    positiveBufferPoissonColumns_map_column B D.A Q E.column j
  have hdn (i j : Fin 2) :
      bufferSign i * deriv (p j) (bufferCut B i) =
        positiveBufferPhysicalConormal D.A D.alphaOut Q i j :=
    positiveBufferPoissonRepresentative_conormal E hA Q hMQ i j
  refine ⟨G, ?_, hGsolve, hGunique, D.pin, D.pout, p, fields, scalars,
    D.alphaIn, D.alphaOut, ?_, ?_, ?_, ?_, ?_⟩
  · have hs := positiveBuffer_columns_square_norm g B.mass (fun i => (hm i).1) hK E.norm_bound
    have hmass : 0 ≤ ∑ i, (B.mass i)⁻¹ ^ 2 :=
      Finset.sum_nonneg (fun i _ => sq_nonneg _)
    calc
      ‖G‖ ≤ B.B₀ + 8 * ∑ i, ‖g i‖ ^ 2 := hGnorm
      _ ≤ B.B₀ + 8 * (K ^ 2 * ∑ i, (B.mass i)⁻¹ ^ 2) :=
        add_le_add_left (mul_le_mul_of_nonneg_left hs (by norm_num)) _
      _ = B.B₀ + (8 * K ^ 2) * ∑ i, (B.mass i)⁻¹ ^ 2 := by ring
      _ ≤ B.B₀ + C * ∑ i, (B.mass i)⁻¹ ^ 2 :=
        add_le_add_left (mul_le_mul_of_nonneg_right hKsqC hmass) _
  · intro i
    have hm0 := (hm i).1
    have hdiv : B.mass i / C ≤ B.mass i := by
      apply (div_le_iff₀ hC).mpr
      nlinarith
    refine ⟨(D.pin_smooth i).contDiffOn.of_le (by simp),
      (D.pout_smooth i).contDiffOn.of_le (by simp),
      D.inner_energy_integrable i, D.outer_energy_integrable i,
      (D.pin_smooth i).contDiffAt, (D.pout_smooth i).contDiffAt,
      D.pin_cut i, D.pin_wall i, D.pout_cut i, D.pout_memLp i,
      D.pin_equation i, D.pout_equation i, D.alphaIn_conormal i,
      D.alphaOut_conormal i, D.alphaIn_energy i, D.alphaOut_energy i,
      hdiv.trans (D.alphaIn_lower i), ?_, hdiv.trans (D.alphaOut_lower i), ?_⟩
    · exact (hPin i).trans (mul_le_mul_of_nonneg_right hPC hm0.le)
    · exact (hPout i).trans (mul_le_mul_of_nonneg_right hPC hm0.le)
  · exact positiveBufferPoissonColumns_spec hB E hA Q hMQ
  · intro z
    have hnorm := positiveBufferPoissonMap_mass_bound B g Q hinv.2.1 D.A
      (fun i => (hA i).le) (fun i => (hm i).1) hK E.norm_bound z
    have heq := positiveBufferPoissonMap_columns B g Q D.A fields scalars hcols z
    rw [← heq] at hnorm
    calc
      _ ≤ (8 * K) * sqrt (∑ i, (B.mass i)⁻¹ ^ 2) *
          sqrt (∑ i, D.A i * z i ^ 2) := hnorm
      _ ≤ C * sqrt (∑ i, (B.mass i)⁻¹ ^ 2) *
          sqrt (∑ i, D.A i * z i ^ 2) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hKC (sqrt_nonneg _)) (sqrt_nonneg _)
  · intro z hz
    have hpos := positiveBufferPhysicalConormal_positive D.A D.alphaIn D.alphaOut B.mass
      (fun i => B.mass i * exp (-B.action i)) hA (fun _ => rfl) hP
      (show 0 ≤ 2 * (D₀ * B.B₀) by positivity) (fun i => (hm i).1)
      D.alphaIn_lower D.alphaOut_lower hPin hPout
      (fun i => mul_nonneg (hm i).1.le (exp_pos _).le) Q hinv.2.2 hquad z hz
    have heq : (∑ i, ∑ j, z i * bufferSign i * deriv (p j) (bufferCut B i) * z j) =
        ∑ i, ∑ j, z i * positiveBufferPhysicalConormal D.A D.alphaOut Q i j * z j := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      calc
        _ = z i * (bufferSign i * deriv (p j) (bufferCut B i)) * z j := by ring
        _ = _ := by rw [hdn]
    rw [heq]
    exact hpos
  · intro i j
    rw [hdn]
    change |(positiveBufferPhysicalConormal D.A D.alphaOut Q i j -
      (if i = j then D.alphaIn i else 0)) / sqrt (D.A i * D.A j)| ≤ _
    rw [positiveBufferPhysicalConormal_normalized_error D.A D.alphaIn D.alphaOut hA (fun _ => rfl)]
    exact positiveBuffer_attenuated_entry_bound hDC hB₀.le B.mass B.action
      (fun i => (hm i).1.le) i j (hinv.2.2 i j)

end ContinuousFlexibility.Radial
