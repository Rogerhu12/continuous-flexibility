module

public import ContinuousFlexibility.Radial.PositiveBufferCompression
public import ContinuousFlexibility.Radial.PositiveBufferCorrectedConstruction

/-!
# Cutting a full inverse inside a positive buffer

The constants are chosen before the buffer data. Actual variational
profiles and actual Green columns supply every hypothesis of the exact
compression assembly.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open ContinuousFlexibility.Statements
open scoped Topology ContDiff InnerProductSpace

theorem r09Statement : R09Statement := by
  intro C₀ hC₀
  obtain ⟨Ccut, hCcut, hcut⟩ := positiveBufferCutoff_derivative_bounds
  let P : ℝ := 4 * (morseCutoffDerivativeConstant ^ 2 + C₀ + 1)
  let F : ℝ := 6 * Ccut + 1
  let K : ℝ := positiveBufferColumnConstant P F
  let D₀ : ℝ := positiveBufferErrorConstant P F
  have hP : 1 ≤ P := by
    dsimp only [P]
    nlinarith [sq_nonneg morseCutoffDerivativeConstant]
  have hF : 1 ≤ F := by dsimp only [F]; linarith
  have hK : 0 ≤ K := by
    dsimp only [K, positiveBufferColumnConstant]
    have hP0 : 0 ≤ P := by linarith
    have hF0 : 0 ≤ F := by linarith
    positivity
  have hD₀ : 0 ≤ D₀ := by
    dsimp only [D₀, positiveBufferErrorConstant]
    have hP0 : 0 ≤ P := by linarith
    have hF0 : 0 ≤ F := by linarith
    positivity
  obtain ⟨C, ε, hC, hε, hε1, hPC, hKC, hKsqC, hDC, hsmallC, hquadC⟩ :=
    positiveBuffer_choose_constants hP hF
  refine ⟨C, ε, hC, hε, ?_⟩
  intro B hLayer hB hsmall
  obtain ⟨D⟩ := positiveBuffer_greenData_nonempty hB hCcut
    (fun i t => hcut (B.action i) t)
  have hHyp := hB
  rcases hHyp with ⟨hlh, hwalls, hB₀, hlayer, hV, hreal, hbf, hbc, hbae, hbs,
    hm, hborder, hlo, hup, H, hHnorm, hH, hHunique⟩
  have hsmall1 : ∀ i, B.B₀ * B.mass i ^ 2 * exp (-B.action i) ≤ 1 :=
    fun i => (hsmall i).le.trans hε1
  obtain ⟨Eraw⟩ := D.correctedData_nonempty_of_layerBound hB H hH hHnorm
    hCcut hC₀ hLayer hsmall1
  let E : PositiveBufferCorrectedData B D.profiles.A D.profiles.alphaOut K (D₀ * B.B₀) := Eraw
  have hsum : (D₀ * B.B₀) * (∑ i, (B.mass i * exp (-B.action i)) ^ 2) ≤ 2 * D₀ * ε :=
    positiveBuffer_attenuated_weights_sum hB₀.le hD₀ B.mass B.action
      (fun i => (hm i).2.le) (fun i => (hsmall i).le)
  have hquad : (2 * (D₀ * B.B₀)) * (∑ i, (B.mass i * exp (-B.action i)) ^ 2) ≤
      (1 / (2 * P)) / 2 := by
    calc
      _ = 2 * ((D₀ * B.B₀) * ∑ i, (B.mass i * exp (-B.action i)) ^ 2) := by ring
      _ ≤ 2 * (2 * D₀ * ε) := mul_le_mul_of_nonneg_left hsum (by norm_num)
      _ = 4 * D₀ * ε := by ring
      _ ≤ _ := hquadC
  apply positiveBuffer_compression_of_corrected_data hB D.profiles
    (P := P) (K := K) (D₀ := D₀) (C := C) (by linarith) hK hD₀ hC
    (hP.trans hPC) hPC hKC hKsqC hDC
  · intro i
    apply (D.profiles.alphaIn_upper i).trans
    apply mul_le_mul_of_nonneg_right _ (hm i).1.le
    dsimp only [P]
    linarith
  · intro i
    apply (D.profiles.alphaOut_upper i).trans
    apply mul_le_mul_of_nonneg_right _ (hm i).1.le
    dsimp only [P]
    linarith
  · exact E
  · exact hsum.trans hsmallC
  · exact hquad

end ContinuousFlexibility.Radial
