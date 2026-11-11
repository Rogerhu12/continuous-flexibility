import ContinuousFlexibility.Radial.PositiveBufferGreenCorrection
import ContinuousFlexibility.Radial.PositiveBufferComparisonGreenBoundary

/-!
# Exact identities of the normalized corrected Green columns

The corrected columns have the true bordered energy delta identity,
globally smooth retained representatives, and the physical exterior
conormal correction at both cuts.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory Real
open ContinuousFlexibility.Statements
open scoped Topology ContDiff RealInnerProductSpace InnerProductSpace

theorem positiveBuffer_schrodinger_smul_sub {u v V : ℝ → ℝ}
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) (c x : ℝ) :
    -deriv (deriv (fun y => c * (u y - v y))) x +
      V x * (c * (u x - v x)) =
    c * ((-deriv (deriv u) x + V x * u x) -
      (-deriv (deriv v) x + V x * v x)) := by
  have hd : deriv (fun y => c * (u y - v y)) =
      fun y => c * (deriv u y - deriv v y) := by
    funext y
    exact ((((hu.differentiable (by simp) y).hasDerivAt).fun_sub
      ((hv.differentiable (by simp) y).hasDerivAt)).const_mul c).deriv
  have hdu := (contDiff_infty_iff_deriv.mp hu).2
  have hdv := (contDiff_infty_iff_deriv.mp hv).2
  have hdd : deriv (fun y => c * (deriv u y - deriv v y)) x =
      c * (deriv (deriv u) x - deriv (deriv v) x) :=
    ((((hdu.differentiable (by simp) x).hasDerivAt).fun_sub
      ((hdv.differentiable (by simp) x).hasDerivAt)).const_mul c).deriv
  rw [hd, hdd]
  ring

namespace PositiveBufferGreenData

variable {B : BufferData} {Ccut : ℝ}
variable (D : PositiveBufferGreenData B Ccut) (hB : BufferHypotheses B)
variable (H : (RadialL2 × ℝ) →L[ℝ] (RadialL2 × ℝ))
variable (hH : ∀ F, (B.bordered = false → F.2 = 0) →
  BorderedFullGraph B.potential B.border B.bordered (H F) F)

theorem corrected_smooth (j : Fin 2) :
    ContDiff ℝ ∞ (D.correctedRepresentative hB H hH j) :=
  ((D.interiorKernel_smooth j).sub (D.correction_smooth_equation hB H hH j).1).const_mul _

theorem corrected_representative_eq (j : Fin 2) :
    EqOn (D.correctedRepresentative hB H hH j)
      (positiveBufferEnergyRepresentative B.potential
        (positiveBufferBorderedField B.potential B.bordered
          (D.correctedColumn hB H hH j))) (Icc B.l B.h) := by
  intro x hx
  have he := D.interiorKernel_eq_representative hB j hx
  change sqrt (D.profiles.A j) *
      (D.profiles.interiorKernel j x - D.correctionRepresentative hB H hH j x) =
    positiveBufferTraceAt B.potential x
      (positiveBufferBorderedField B.potential B.bordered (D.correctedColumn hB H hH j))
  rw [he]
  change sqrt (D.profiles.A j) *
      (positiveBufferTraceAt B.potential x (D.energy j) -
        positiveBufferTraceAt B.potential x
          (positiveBufferBorderedField B.potential B.bordered (D.correction hB H hH j))) =
    positiveBufferTraceAt B.potential x
      (positiveBufferBorderedField B.potential B.bordered (D.correctedColumn hB H hH j))
  simp only [correctedColumn, map_smul, map_sub, zeroScalar_field, smul_eq_mul]

theorem corrected_equation (j : Fin 2) {x : ℝ} (hx : x ∈ Ioo B.l B.h) :
    -deriv (deriv (D.correctedRepresentative hB H hH j)) x +
      B.potential x * D.correctedRepresentative hB H hH j x +
      positiveBufferBorderedScalar B.potential B.bordered
        (D.correctedColumn hB H hH j) * B.borderFunction x = 0 := by
  dsimp only [correctedRepresentative]
  rw [positiveBuffer_schrodinger_smul_sub (D.interiorKernel_smooth j)
    (D.correction_smooth_equation hB H hH j).1]
  rw [D.interiorKernel_equation hB j x hx,
    (D.correction_smooth_equation hB H hH j).2 x]
  simp only [correctedColumn, map_smul, map_sub, zeroScalar_scalar, smul_eq_mul]
  ring

theorem corrected_border_row (j : Fin 2) :
    if B.bordered then
      ⟪B.border, (positiveBufferBorderedState B.potential B.bordered
        (D.correctedColumn hB H hH j)).1⟫_ℝ = 0
    else (positiveBufferBorderedState B.potential B.bordered
      (D.correctedColumn hB H hH j)).2 = 0 := by
  cases hb : B.bordered with
  | false =>
    simp only [hb, Bool.false_eq_true, ite_false]
    exact (D.correctedColumn hB H hH j).property hb
  | true =>
    simp only [hb, ite_true]
    have hg := D.correction_graph hB H hH j
    simp only [BorderedFullGraph, hb, ite_true] at hg
    simp only [correctedColumn, map_smul, map_sub, Prod.smul_fst, Prod.fst_sub,
      zeroScalar_state, inner_smul_right, inner_sub_right, smul_eq_mul,
      D.border_orthogonal j, hg.2, sub_zero, mul_zero]

theorem corrected_delta_form (hV : Continuous B.potential) (j : Fin 2)
    (W : PositiveBufferBorderedEnergy B.potential B.bordered) :
    positiveBufferBorderedForm B.potential hV B.border B.bordered
      (D.correctedColumn hB H hH j) W =
    sqrt (D.profiles.A j) * positiveBufferTraceAt B.potential (bufferCut B j)
      (positiveBufferBorderedField B.potential B.bordered W) := by
  have hK :
      positiveBufferBorderedForm B.potential hV B.border B.bordered (D.zeroScalar j) W =
        ⟪D.source j, positiveBufferEnergyCoordinate B.potential 0 W.val.1⟫_ℝ +
          positiveBufferTraceAt B.potential (bufferCut B j) W.val.1 := by
    simp only [positiveBufferBorderedForm, zeroScalar, D.border_orthogonal j,
      zero_mul, mul_zero, add_zero]
    exact D.form_identity hV j W.val.1
  have hU := positiveBufferLiftedInverse_form hB.2.2.2.2.2.1 hV B.border B.bordered
    H hH (D.source j, 0) W
  change positiveBufferBorderedForm B.potential hV B.border B.bordered
      (D.correction hB H hH j) W = _ at hU
  simp only [positiveBufferStatePairing_apply, positiveBufferBorderedState_apply,
    zero_mul, add_zero] at hU
  change positiveBufferBorderedFormLinear B.potential hV B.border B.bordered
    (D.correctedColumn hB H hH j) W = _
  simp only [correctedColumn, map_smul, map_sub, LinearMap.smul_apply, LinearMap.sub_apply,
    smul_eq_mul, positiveBufferBorderedFormLinear_apply]
  rw [hK, hU]
  ring

theorem alphaIn_normalized (j : Fin 2) :
    D.profiles.alphaIn j = -B.mass j * deriv (D.profiles.normalizedIn j) 0 := by
  change D.profiles.alphaIn j =
    -B.mass j * deriv (fun t => D.profiles.pin j (positiveBufferPoint B j t)) 0
  rw [positiveBuffer_normalized_inner_deriv_zero j (D.profiles.pin_smooth j),
    D.profiles.alphaIn_conormal j]
  field_simp [(buffer_mass_pos hB j).ne']
  <;> ring

theorem corrected_conormal (i j : Fin 2) :
    bufferSign i * deriv (D.correctedRepresentative hB H hH j) (bufferCut B i) =
      (if i = j then sqrt (D.profiles.A i) else 0) -
        D.profiles.alphaOut i * D.correctedRepresentative hB H hH j (bufferCut B i) := by
  have hKcut := positiveBufferGreenInterior_cut_values hB D.profiles.A
    D.profiles.normalizedIn D.profiles.normalizedIn_zero
  have hKcon := positiveBufferGreenInterior_conormals hB D.profiles.A
    D.profiles.alphaIn D.profiles.normalizedIn D.profiles.normalizedIn_smooth
    (D.alphaIn_normalized hB)
  have hcon := positiveBuffer_corrected_conormal_identity B D.profiles.A
    D.profiles.alphaIn D.profiles.alphaOut D.profiles.interiorKernel
    (D.correctionRepresentative hB H hH) D.interiorKernel_smooth
    (fun k => (D.correction_smooth_equation hB H hH k).1)
    hKcut hKcon (D.correction_exterior_conormal hB H hH)
    (fun k => (D.profiles.A_pos hB k).ne') (fun _ => rfl)
  have hdiff : Differentiable ℝ (fun x =>
      D.profiles.interiorKernel j x - D.correctionRepresentative hB H hH j x) :=
    ((D.interiorKernel_smooth j).differentiable (by simp)).sub
      ((D.correction_smooth_equation hB H hH j).1.differentiable (by simp))
  have hd : deriv (D.correctedRepresentative hB H hH j) (bufferCut B i) =
      sqrt (D.profiles.A j) *
        deriv (fun x => D.profiles.interiorKernel j x -
          D.correctionRepresentative hB H hH j x) (bufferCut B i) :=
    ((hdiff (bufferCut B i)).hasDerivAt.const_mul (sqrt (D.profiles.A j))).deriv
  rw [hd]
  calc
    _ = sqrt (D.profiles.A j) *
        (bufferSign i * deriv (fun x => D.profiles.interiorKernel j x -
          D.correctionRepresentative hB H hH j x) (bufferCut B i)) := by ring
    _ = sqrt (D.profiles.A j) * ((if i = j then 1 else 0) -
        D.profiles.alphaOut i * (D.profiles.interiorKernel j (bufferCut B i) -
          D.correctionRepresentative hB H hH j (bufferCut B i))) := by rw [hcon]
    _ = _ := by
      by_cases hij : i = j
      · subst j
        simp only [ite_true, correctedRepresentative]
        ring
      · simp only [if_neg hij, correctedRepresentative]
        ring

theorem corrected_trace_difference (i j : Fin 2) :
    sqrt (D.profiles.A i) * D.correctedRepresentative hB H hH j (bufferCut B i) -
        (if i = j then 1 else 0) =
      -(sqrt (D.profiles.A i) * sqrt (D.profiles.A j) *
        D.correctionRepresentative hB H hH j (bufferCut B i)) := by
  have hcut := positiveBufferGreenInterior_cut_values hB D.profiles.A
    D.profiles.normalizedIn D.profiles.normalizedIn_zero i j
  change D.profiles.interiorKernel j (bufferCut B i) =
    (if i = j then (D.profiles.A j)⁻¹ else 0) at hcut
  dsimp only [correctedRepresentative]
  rw [hcut]
  by_cases hij : i = j
  · subst j
    simp only [ite_true]
    calc
      _ = (sqrt (D.profiles.A i)) ^ 2 * (D.profiles.A i)⁻¹ - 1 -
          sqrt (D.profiles.A i) * sqrt (D.profiles.A i) *
            D.correctionRepresentative hB H hH i (bufferCut B i) := by ring
      _ = _ := by
        rw [sq_sqrt (D.profiles.A_pos hB i).le,
          mul_inv_cancel₀ (D.profiles.A_pos hB i).ne']
        ring
  · simp only [if_neg hij]
    ring

end PositiveBufferGreenData

end ContinuousFlexibility.Radial
