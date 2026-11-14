module

public import ContinuousFlexibility.Radial.PositiveBufferCorrectedIdentities
public import ContinuousFlexibility.Radial.PositiveBufferCorrectedData

/-!
# Quantitative construction of the corrected Green data

The actual inverse bound and the exponentially localized commutator
sources control the column norms. The sharp cut estimate supplies the
product of the two buffer exponentials in every cut-matrix entry.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory Real
open ContinuousFlexibility.Statements
open scoped Topology ContDiff RealInnerProductSpace InnerProductSpace

theorem positiveBuffer_sqrt_mass_bound {A m Q : ℝ}
    (hA : 0 ≤ A) (hm : 0 ≤ m) (hQ : 0 ≤ Q) (hAm : A ≤ Q * m) :
    sqrt A * sqrt m ≤ sqrt Q * m := by
  calc
    sqrt A * sqrt m ≤ sqrt (Q * m) * sqrt m :=
      mul_le_mul_of_nonneg_right (sqrt_le_sqrt hAm) (sqrt_nonneg m)
    _ = (sqrt Q * sqrt m) * sqrt m := by rw [sqrt_mul hQ]
    _ = sqrt Q * (sqrt m) ^ 2 := by ring
    _ = sqrt Q * m := by rw [sq_sqrt hm]

theorem positiveBuffer_corrected_scalar_norm_bound {A m P F B₀ σ : ℝ}
    (hA : 0 < A) (hm : 0 < m) (hP : 1 ≤ P) (hF : 0 ≤ F) (hB₀ : 0 ≤ B₀)
    (hAm : A ≤ 2 * P * m) (hsmall : B₀ * m ^ 2 * exp (-σ) ≤ 1) :
    sqrt A * (1 / (m * sqrt A) + B₀ * (F * sqrt m * exp (-σ))) ≤
      (2 * P * (1 + F)) / m := by
  have hQ : 0 ≤ 2 * P := by linarith
  have hroot : sqrt (2 * P) ≤ 2 * P := by
    calc
      sqrt (2 * P) ≤ sqrt ((2 * P) ^ 2) := sqrt_le_sqrt (by nlinarith)
      _ = 2 * P := by rw [sqrt_sq_eq_abs, abs_of_nonneg hQ]
  have hmass : sqrt A * sqrt m ≤ 2 * P * m :=
    (positiveBuffer_sqrt_mass_bound hA.le hm.le hQ hAm).trans
      (mul_le_mul_of_nonneg_right hroot hm.le)
  have hsmall' : B₀ * m * exp (-σ) ≤ 1 / m := by
    apply (le_div_iff₀ hm).mpr
    nlinarith [hsmall]
  calc
    _ = 1 / m + (sqrt A * sqrt m) * (F * B₀ * exp (-σ)) := by
      field_simp [hm.ne', (sqrt_pos.mpr hA).ne']
      <;> ring
    _ ≤ 1 / m + (2 * P * m) * (F * B₀ * exp (-σ)) :=
      add_le_add le_rfl
        (mul_le_mul_of_nonneg_right hmass
          (show 0 ≤ F * B₀ * exp (-σ) from mul_nonneg (mul_nonneg hF hB₀) (exp_pos _).le))
    _ = 1 / m + (2 * P * F) * (B₀ * m * exp (-σ)) := by ring
    _ ≤ 1 / m + (2 * P * F) * (1 / m) :=
      add_le_add le_rfl
        (mul_le_mul_of_nonneg_left hsmall' (show 0 ≤ 2 * P * F from mul_nonneg hQ hF))
    _ = (1 + 2 * P * F) / m := by ring
    _ ≤ (2 * P * (1 + F)) / m := by
      apply (div_le_div_iff_of_pos_right hm).mpr
      nlinarith

theorem positiveBuffer_corrected_scalar_trace_bound {Ai Aj mi mj P F B₀ σi σj : ℝ}
    (hAi : 0 ≤ Ai) (hAj : 0 ≤ Aj) (hmi : 0 ≤ mi) (hmj : 0 ≤ mj)
    (hP : 0 ≤ P) (hF : 0 ≤ F) (hB₀ : 0 ≤ B₀)
    (hAiM : Ai ≤ 2 * P * mi) (hAjM : Aj ≤ 2 * P * mj) :
    sqrt Ai * sqrt Aj *
        (sqrt mi * exp (-σi) * (B₀ * (F * sqrt mj * exp (-σj)))) ≤
      (2 * P * F * B₀) * (mi * exp (-σi)) * (mj * exp (-σj)) := by
  have hQ : 0 ≤ 2 * P := by positivity
  have hi := positiveBuffer_sqrt_mass_bound hAi hmi hQ hAiM
  have hj := positiveBuffer_sqrt_mass_bound hAj hmj hQ hAjM
  have hprod : (sqrt Ai * sqrt mi) * (sqrt Aj * sqrt mj) ≤ 2 * P * mi * mj := by
    calc
      _ ≤ (sqrt (2 * P) * mi) * (sqrt (2 * P) * mj) :=
        mul_le_mul hi hj (by positivity) (by positivity)
      _ = (sqrt (2 * P)) ^ 2 * mi * mj := by ring
      _ = _ := by rw [sq_sqrt hQ]
  calc
    _ = ((sqrt Ai * sqrt mi) * (sqrt Aj * sqrt mj)) *
        (F * B₀ * exp (-σi) * exp (-σj)) := by ring
    _ ≤ (2 * P * mi * mj) * (F * B₀ * exp (-σi) * exp (-σj)) :=
      mul_le_mul_of_nonneg_right hprod (by positivity)
    _ = _ := by ring

namespace PositiveBufferGreenData

variable {B : BufferData} {Ccut : ℝ}
variable (D : PositiveBufferGreenData B Ccut) (hB : BufferHypotheses B)
variable (H : (RadialL2 × ℝ) →L[ℝ] (RadialL2 × ℝ))
variable (hH : ∀ F, (B.bordered = false → F.2 = 0) →
  BorderedFullGraph B.potential B.border B.bordered (H F) F)
variable (hHnorm : ‖H‖ ≤ B.B₀)
variable {P F : ℝ} (hP : 1 ≤ P) (hF : 0 ≤ F)
variable (hAupper : ∀ i, D.profiles.A i ≤ 2 * P * B.mass i)
variable (hsource : ∀ j, ‖D.source j‖ ≤ F * sqrt (B.mass j) * exp (-B.action j))

include hHnorm hP hF hAupper hsource in
theorem corrected_norm_bound
    (hsmall : ∀ i, B.B₀ * B.mass i ^ 2 * exp (-B.action i) ≤ 1) (j : Fin 2) :
    ‖positiveBufferBorderedState B.potential B.bordered (D.correctedColumn hB H hH j)‖ ≤
      (2 * P * (1 + F)) / B.mass j := by
  have hB₀ : 0 ≤ B.B₀ := hB.2.2.1.le
  have hK : ‖positiveBufferBorderedState B.potential B.bordered (D.zeroScalar j)‖ ≤
      1 / (B.mass j * sqrt (D.profiles.A j)) := by
    simpa only [zeroScalar_state, Prod.norm_def, norm_zero, max_eq_left (norm_nonneg _)] using
      D.norm_bound j
  have hU : ‖positiveBufferBorderedState B.potential B.bordered (D.correction hB H hH j)‖ ≤
      B.B₀ * (F * sqrt (B.mass j) * exp (-B.action j)) :=
    (D.correction_state_bound hB H hH hHnorm j).trans
      (mul_le_mul_of_nonneg_left (hsource j) hB₀)
  simp only [correctedColumn, map_smul, map_sub, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (sqrt_nonneg _)]
  calc
    _ ≤ sqrt (D.profiles.A j) *
        (‖positiveBufferBorderedState B.potential B.bordered (D.zeroScalar j)‖ +
          ‖positiveBufferBorderedState B.potential B.bordered (D.correction hB H hH j)‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) (sqrt_nonneg _)
    _ ≤ sqrt (D.profiles.A j) *
        (1 / (B.mass j * sqrt (D.profiles.A j)) +
          B.B₀ * (F * sqrt (B.mass j) * exp (-B.action j))) :=
      mul_le_mul_of_nonneg_left (add_le_add hK hU) (sqrt_nonneg _)
    _ ≤ _ := positiveBuffer_corrected_scalar_norm_bound (D.profiles.A_pos hB j)
      (buffer_mass_pos hB j) hP hF hB₀ (hAupper j) (hsmall j)

include hHnorm hP hF hAupper hsource in
theorem corrected_trace_error (i j : Fin 2) :
    |sqrt (D.profiles.A i) * D.correctedRepresentative hB H hH j (bufferCut B i) -
        (if i = j then 1 else 0)| ≤
      (2 * P * F * B.B₀) * (B.mass i * exp (-B.action i)) *
        (B.mass j * exp (-B.action j)) := by
  have hB₀ : 0 ≤ B.B₀ := hB.2.2.1.le
  calc
    _ = sqrt (D.profiles.A i) * sqrt (D.profiles.A j) *
        |D.correctionRepresentative hB H hH j (bufferCut B i)| := by
      rw [D.corrected_trace_difference hB H hH, abs_neg, abs_mul, abs_mul,
        abs_of_nonneg (sqrt_nonneg _), abs_of_nonneg (sqrt_nonneg _)]
    _ ≤ sqrt (D.profiles.A i) * sqrt (D.profiles.A j) *
        (sqrt (B.mass i) * exp (-B.action i) * (B.B₀ * ‖D.source j‖)) :=
      mul_le_mul_of_nonneg_left (D.correction_cut_bound hB H hH hHnorm i j) (by positivity)
    _ ≤ sqrt (D.profiles.A i) * sqrt (D.profiles.A j) *
        (sqrt (B.mass i) * exp (-B.action i) *
          (B.B₀ * (F * sqrt (B.mass j) * exp (-B.action j)))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hsource j) hB₀) (by positivity)) (by positivity)
    _ ≤ _ := positiveBuffer_corrected_scalar_trace_bound (D.profiles.A_pos hB i).le
      (D.profiles.A_pos hB j).le (buffer_mass_pos hB i).le (buffer_mass_pos hB j).le
      (by linarith) hF hB₀ (hAupper i) (hAupper j)

include hB H hH hHnorm hP hF hAupper hsource in
/-- All corrected data are supplied by the actual Green columns and the
given full inverse. -/
theorem correctedData_nonempty
    (hsmall : ∀ i, B.B₀ * B.mass i ^ 2 * exp (-B.action i) ≤ 1) :
    Nonempty (PositiveBufferCorrectedData B D.profiles.A D.profiles.alphaOut
      (2 * P * (1 + F)) (2 * P * F * B.B₀)) := by
  exact ⟨
    { column := D.correctedColumn hB H hH
      representative := D.correctedRepresentative hB H hH
      smooth := D.corrected_smooth hB H hH
      representative_eq := D.corrected_representative_eq hB H hH
      equation := fun j x hx => D.corrected_equation hB H hH j hx
      border_row := D.corrected_border_row hB H hH
      conormal := D.corrected_conormal hB H hH
      delta_form := D.corrected_delta_form hB H hH
      norm_bound := D.corrected_norm_bound hB H hH hHnorm hP hF hAupper hsource hsmall
      trace_error := D.corrected_trace_error hB H hH hHnorm hP hF hAupper hsource }⟩

include hB H hH hHnorm in
theorem correctedData_nonempty_of_layerBound
    (hCcut : 0 ≤ Ccut) {C₀ : ℝ} (hC₀ : 0 < C₀) (hLayer : B.layerBound ≤ C₀)
    (hsmall : ∀ i, B.B₀ * B.mass i ^ 2 * exp (-B.action i) ≤ 1) :
    Nonempty (PositiveBufferCorrectedData B D.profiles.A D.profiles.alphaOut
      (2 * (4 * (morseCutoffDerivativeConstant ^ 2 + C₀ + 1)) * (1 + (6 * Ccut + 1)))
      (2 * (4 * (morseCutoffDerivativeConstant ^ 2 + C₀ + 1)) * (6 * Ccut + 1) * B.B₀)) := by
  apply D.correctedData_nonempty hB H hH hHnorm
    (P := 4 * (morseCutoffDerivativeConstant ^ 2 + C₀ + 1)) (F := 6 * Ccut + 1)
  · nlinarith [sq_nonneg morseCutoffDerivativeConstant]
  · linarith
  · exact D.profiles.A_upper hB hLayer
  · intro j
    apply (D.source_norm_bound j).trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith : 6 * Ccut ≤ 6 * Ccut + 1)
        (sqrt_nonneg _)) (exp_pos _).le
  · exact hsmall

end PositiveBufferGreenData

end ContinuousFlexibility.Radial
