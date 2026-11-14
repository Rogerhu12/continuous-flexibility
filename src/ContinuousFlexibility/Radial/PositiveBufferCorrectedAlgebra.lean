module

public import ContinuousFlexibility.Radial.PositiveBufferCorrectedData
public import ContinuousFlexibility.Radial.PositiveBufferGreenAlgebra

/-!
# The actual cut matrix of the constructed corrected columns
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory Matrix
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

theorem positiveBufferCut_mem_Icc {B : BufferData} (hlh : B.l ≤ B.h) (i : Fin 2) :
    bufferCut B i ∈ Icc B.l B.h := by
  by_cases hi : i = 0
  · simp only [bufferCut, if_pos hi]
    exact ⟨le_rfl, hlh⟩
  · simp only [bufferCut, if_neg hi]
    exact ⟨hlh, le_rfl⟩

theorem positiveBufferCorrected_cutMatrix_eq {B : BufferData}
    {A αout : Fin 2 → ℝ} {K η : ℝ} (D : PositiveBufferCorrectedData B A αout K η)
    (hlh : B.l ≤ B.h) (i j : Fin 2) :
    positiveBufferCutMatrix (bufferCut B) A D.column i j =
      sqrt (A i) * D.representative j (bufferCut B i) := by
  have he : D.representative j (bufferCut B i) =
      positiveBufferEnergyRepresentative B.potential
        (positiveBufferBorderedField B.potential B.bordered (D.column j)) (bufferCut B i) := by
    apply D.representative_eq j
    exact positiveBufferCut_mem_Icc hlh i
  change sqrt (A i) * positiveBufferTraceAt B.potential (bufferCut B i)
    (D.column j).val.1 = _
  rw [positiveBufferTraceAt_apply]
  exact congrArg (fun x : ℝ => sqrt (A i) * x) he.symm

theorem positiveBufferCorrected_form {B : BufferData} {A αout : Fin 2 → ℝ}
    {K η : ℝ} (D : PositiveBufferCorrectedData B A αout K η)
    (hV : Continuous B.potential) (j : Fin 2)
    (W : PositiveBufferBorderedEnergy B.potential B.bordered) :
    positiveBufferBorderedForm B.potential hV B.border B.bordered (D.column j) W =
      positiveBufferNormalizedTrace B.potential B.bordered (bufferCut B) A W j := by
  rw [positiveBufferNormalizedTrace_apply]
  exact D.delta_form hV j W

theorem positiveBufferCorrected_inverse_matrix {B : BufferData}
    {A αout : Fin 2 → ℝ} {K η : ℝ} (D : PositiveBufferCorrectedData B A αout K η)
    (hlh : B.l ≤ B.h) (hm : ∀ i, 0 ≤ B.mass i) (hη : 0 ≤ η)
    (hsmall : η * (∑ i, (B.mass i * exp (-B.action i)) ^ 2) ≤ 1 / 4) :
    IsUnit (positiveBufferCutMatrix (bufferCut B) A D.column).det ∧
      (∀ z : Fin 2 → ℝ, ‖(positiveBufferCutMatrix (bufferCut B) A D.column)⁻¹ *ᵥ z‖ ≤ 2 * ‖z‖) ∧
      (∀ i j, |((positiveBufferCutMatrix (bufferCut B) A D.column)⁻¹ - 1) i j| ≤
        2 * η * (B.mass i * exp (-B.action i)) * (B.mass j * exp (-B.action j))) := by
  let M := positiveBufferCutMatrix (bufferCut B) A D.column
  let E := M - 1
  let w : Fin 2 → ℝ := fun i => B.mass i * exp (-B.action i)
  have hw : ∀ i, 0 ≤ w i := fun i => mul_nonneg (hm i) (exp_pos _).le
  have hE : ∀ i j, |E i j| ≤ η * w i * w j := by
    intro i j
    simpa only [E, M, Matrix.sub_apply, Matrix.one_apply,
      positiveBufferCorrected_cutMatrix_eq D hlh i j, w] using D.trace_error i j
  have hsum : 1 + E = M := by dsimp only [E]; abel
  have hinv := positiveBufferMatrix_inverse_weighted_error E w hη hw hE hsmall
  have hop := (positiveBufferMatrix_inverse_bound E
    (positiveBufferMatrix_weighted_operator_bound E w hη hw hE hsmall)).2
  rw [hsum] at hinv hop
  exact ⟨hinv.1, hop, hinv.2⟩

end ContinuousFlexibility.Radial
