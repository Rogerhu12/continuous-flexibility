import ContinuousFlexibility.Radial.PositiveBufferSurgeryNorm
import ContinuousFlexibility.Radial.PositiveBufferRestrictionForm

/-!
# The actual interval inverse from the normalized Green subtraction

The finite-rank formula acts on the frozen L² × ℝ space. Both source and
output restrictions are actual indicator operators.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory Matrix
open ContinuousFlexibility.Statements
open scoped Topology InnerProductSpace

def positiveBufferDirichletMap (B : BufferData)
    (H : (RadialL2 × ℝ) →L[ℝ] (RadialL2 × ℝ))
    (g : Fin 2 → RadialL2 × ℝ) (J : Matrix (Fin 2) (Fin 2) ℝ) :
    (RadialL2 × ℝ) →L[ℝ] (RadialL2 × ℝ) :=
  (positiveBufferRetainedProjection B.l B.h).comp
    (((H.comp (positiveBufferSourceProjection B.bordered)) -
      positiveBufferFiniteRank g J).comp (positiveBufferRetainedProjection B.l B.h))

@[simp] theorem positiveBufferDirichletMap_apply (B : BufferData)
    (H : (RadialL2 × ℝ) →L[ℝ] (RadialL2 × ℝ))
    (g : Fin 2 → RadialL2 × ℝ) (J : Matrix (Fin 2) (Fin 2) ℝ) (F : RadialL2 × ℝ) :
    positiveBufferDirichletMap B H g J F =
      positiveBufferRetainedProjection B.l B.h
        (H (positiveBufferSourceProjection B.bordered (positiveBufferRetainedProjection B.l B.h F)) -
          positiveBufferFiniteRank g J (positiveBufferRetainedProjection B.l B.h F)) := by
  simp only [positiveBufferDirichletMap, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply]

theorem positiveBufferDirichletMap_norm_bound (B : BufferData)
    (H : (RadialL2 × ℝ) →L[ℝ] (RadialL2 × ℝ)) (hH : ‖H‖ ≤ B.B₀)
    (g : Fin 2 → RadialL2 × ℝ) (J : Matrix (Fin 2) (Fin 2) ℝ)
    (hJ : ∀ z : Fin 2 → ℝ, ‖J *ᵥ z‖ ≤ 2 * ‖z‖) :
    ‖positiveBufferDirichletMap B H g J‖ ≤ B.B₀ + 8 * ∑ i, ‖g i‖ ^ 2 := by
  have hB : 0 ≤ B.B₀ := (norm_nonneg H).trans hH
  have hK : 0 ≤ 8 * ∑ i, ‖g i‖ ^ 2 := by positivity
  apply ContinuousLinearMap.opNorm_le_bound _ (add_nonneg hB hK)
  intro F
  rw [positiveBufferDirichletMap_apply]
  calc
    _ ≤ ‖H (positiveBufferSourceProjection B.bordered
          (positiveBufferRetainedProjection B.l B.h F)) -
        positiveBufferFiniteRank g J (positiveBufferRetainedProjection B.l B.h F)‖ :=
      positiveBufferRetainedProjection_norm_le _ _ _
    _ ≤ ‖H (positiveBufferSourceProjection B.bordered
          (positiveBufferRetainedProjection B.l B.h F))‖ +
        ‖positiveBufferFiniteRank g J (positiveBufferRetainedProjection B.l B.h F)‖ :=
      norm_sub_le _ _
    _ ≤ B.B₀ * ‖F‖ + (8 * ∑ i, ‖g i‖ ^ 2) * ‖F‖ := by
      apply add_le_add
      · exact (H.le_opNorm _).trans (mul_le_mul hH
          ((positiveBufferSourceProjection_norm_le _ _).trans
            (positiveBufferRetainedProjection_norm_le _ _ _)) (norm_nonneg _) hB)
      · exact (positiveBufferFiniteRank_bound g J hJ _).trans
          (mul_le_mul_of_nonneg_left (positiveBufferRetainedProjection_norm_le _ _ _) hK)
    _ = _ := by ring

theorem positiveBufferDirichletCorrection_state (B : BufferData)
    (hreal : ActualClosedFormRealization B.potential) (hV : Continuous B.potential)
    (H : (RadialL2 × ℝ) →L[ℝ] (RadialL2 × ℝ))
    (hH : ∀ F, (B.bordered = false → F.2 = 0) →
      BorderedFullGraph B.potential B.border B.bordered (H F) F)
    (A : Fin 2 → ℝ)
    (g : Fin 2 → PositiveBufferBorderedEnergy B.potential B.bordered)
    (hg : ∀ i W, positiveBufferBorderedForm B.potential hV B.border B.bordered (g i) W =
      positiveBufferNormalizedTrace B.potential B.bordered (bufferCut B) A W i)
    (hM : IsUnit (positiveBufferCutMatrix (bufferCut B) A g).det)
    (F : RadialL2 × ℝ) :
    positiveBufferBorderedState B.potential B.bordered
        (positiveBufferDirichletCorrection
          (positiveBufferLiftedInverse hreal B.border B.bordered H hH)
          (positiveBufferNormalizedTrace B.potential B.bordered (bufferCut B) A)
          (positiveBufferColumnLinear g)
          (positiveBufferCutEquiv (positiveBufferCutMatrix (bufferCut B) A g) hM) F) =
      H (positiveBufferSourceProjection B.bordered F) -
        positiveBufferFiniteRank
          (fun i => positiveBufferBorderedState B.potential B.bordered (g i))
          (positiveBufferCutMatrix (bufferCut B) A g)⁻¹ F := by
  have ht : positiveBufferNormalizedTrace B.potential B.bordered (bufferCut B) A
      (positiveBufferLiftedInverse hreal B.border B.bordered H hH F) =
      positiveBufferStateAnalysis
        (fun i => positiveBufferBorderedState B.potential B.bordered (g i)) F := by
    ext i
    exact positiveBuffer_green_inverse_trace hreal hV B.border B.bordered H hH
      (bufferCut B) A g hg F i
  rw [positiveBufferDirichletCorrection_apply, map_sub, positiveBufferLiftedInverse_state,
    ht, positiveBufferCutEquiv_symm_apply, positiveBufferColumnLinear_apply, map_sum]
  simp only [map_smul, positiveBufferFiniteRank, ContinuousLinearMap.comp_apply,
    positiveBufferMatrixCLM_apply, positiveBufferStateSynthesis_apply]

theorem positiveBufferStatePairing_retained_test (l h : ℝ) (F W : RadialL2 × ℝ)
    (hF : (F.1 : ℝ → ℝ) =ᵐ[volume.restrict ((Ioo l h)ᶜ)] (fun _ => 0)) :
    positiveBufferStatePairing F (positiveBufferRetainedProjection l h W) =
      positiveBufferStatePairing F W := by
  rw [positiveBufferStatePairing_apply, positiveBufferRetainedProjection_apply,
    positiveBufferStatePairing_apply, ← positiveBuffer_indicator_inner,
    bufferL2Indicator_eq_self_of_supported _ _ _ hF]

/-- A genuine Green system with invertible cut values produces precisely
the frozen interval operator, including uniqueness for exterior source values. -/
theorem positiveBuffer_actual_dirichlet_inverse (B : BufferData)
    (hlh : B.l < B.h) (hreal : ActualClosedFormRealization B.potential)
    (hV : Continuous B.potential)
    (hborder : (B.border : ℝ → ℝ) =ᵐ[
      volume.restrict ((Ioo B.l B.h)ᶜ)] (fun _ => 0))
    (H : (RadialL2 × ℝ) →L[ℝ] (RadialL2 × ℝ)) (hHnorm : ‖H‖ ≤ B.B₀)
    (hH : ∀ F, (B.bordered = false → F.2 = 0) →
      BorderedFullGraph B.potential B.border B.bordered (H F) F)
    (A : Fin 2 → ℝ) (hA : ∀ i, 0 < A i)
    (g : Fin 2 → PositiveBufferBorderedEnergy B.potential B.bordered)
    (hg : ∀ i W, positiveBufferBorderedForm B.potential hV B.border B.bordered (g i) W =
      positiveBufferNormalizedTrace B.potential B.bordered (bufferCut B) A W i)
    (hM : IsUnit (positiveBufferCutMatrix (bufferCut B) A g).det)
    (hJ : ∀ z : Fin 2 → ℝ,
      ‖(positiveBufferCutMatrix (bufferCut B) A g)⁻¹ *ᵥ z‖ ≤ 2 * ‖z‖) :
    ∃ G : (RadialL2 × ℝ) →L[ℝ] (RadialL2 × ℝ),
      ‖G‖ ≤ B.B₀ + 8 * ∑ i, ‖positiveBufferBorderedState B.potential B.bordered (g i)‖ ^ 2 ∧
      (∀ F : RadialL2 × ℝ, (B.bordered = false → F.2 = 0) →
        ((F.1 : ℝ → ℝ) =ᵐ[volume.restrict ((Ioo B.l B.h)ᶜ)] (fun _ => 0)) →
        BorderedIntervalGraph B.potential B.border B.bordered B.l B.h (G F) F) ∧
      (∀ U F, BorderedIntervalGraph B.potential B.border B.bordered B.l B.h U F → G F = U) := by
  let L := positiveBufferLiftedInverse hreal B.border B.bordered H hH
  let t := positiveBufferNormalizedTrace B.potential B.bordered (bufferCut B) A
  let C := positiveBufferColumnLinear g
  let Γ := positiveBufferCutEquiv (positiveBufferCutMatrix (bufferCut B) A g) hM
  let J := (positiveBufferBorderedState B.potential B.bordered).toLinearMap
  let a := positiveBufferBorderedFormLinear B.potential hV B.border B.bordered
  let corr := positiveBufferDirichletCorrection L t C Γ
  let R := positiveBufferRetainedProjection B.l B.h
  let G := positiveBufferDirichletMap B H
    (fun i => positiveBufferBorderedState B.potential B.bordered (g i))
    (positiveBufferCutMatrix (bufferCut B) A g)⁻¹
  have hΓ : ∀ z, t (C z) = Γ z := fun z =>
    positiveBuffer_trace_columns (bufferCut B) A g z
  have hL : ∀ F W, a (L F) W = positiveBufferStatePairing F (J W) :=
    positiveBufferLiftedInverse_form hreal hV B.border B.bordered H hH
  have hC : ∀ z W, a (C z) W = positiveBufferBoundaryPairing z (t W) :=
    positiveBuffer_green_columns_form hV B.border B.bordered (bufferCut B) A g hg
  have hsymm : ∀ U W, a U W = a W U :=
    positiveBufferBorderedForm_symm B.potential hV B.border B.bordered
  have htzero : ∀ F, t (corr F) = 0 :=
    positiveBufferDirichletCorrection_trace L t C Γ hΓ
  have hcform : ∀ F W, t W = 0 → a (corr F) W = positiveBufferStatePairing F (J W) :=
    positiveBufferDirichletCorrection_form a positiveBufferStatePairing
      positiveBufferBoundaryPairing J L t C Γ hL hC
  have hcstate (F : RadialL2 × ℝ) :
      J (corr F) = H (positiveBufferSourceProjection B.bordered F) -
        positiveBufferFiniteRank
          (fun i => positiveBufferBorderedState B.potential B.bordered (g i))
          (positiveBufferCutMatrix (bufferCut B) A g)⁻¹ F :=
    positiveBufferDirichletCorrection_state B hreal hV H hH A g hg hM F
  have hG (F : RadialL2 × ℝ) : G F = R (J (corr (R F))) := by
    rw [hcstate]
    exact positiveBufferDirichletMap_apply B H _ _ F
  refine ⟨G, positiveBufferDirichletMap_norm_bound B H hHnorm _ _ hJ, ?_, ?_⟩
  · intro F hF _
    let u := corr (R F)
    have hut : positiveBufferTraceAt B.potential B.l u.val.1 = 0 ∧
        positiveBufferTraceAt B.potential B.h u.val.1 = 0 :=
      (positiveBufferNormalizedTrace_zero_iff B A hA u).mp (htzero (R F))
    let v := positiveBufferBorderedEnergyRestrict hV hreal hlh u hut.1 hut.2
    have hvs := positiveBufferBorderedEnergyRestrict_supported hV hreal hlh u hut.1 hut.2
    have hvstate : positiveBufferBorderedState B.potential B.bordered v = G F := by
      rw [hG]
      exact positiveBufferBorderedEnergyRestrict_state hV hreal hlh u hut.1 hut.2
    rw [← hvstate]
    apply (positiveBuffer_borderedIntervalGraph_iff_zero_trace_form
      hV hreal hlh B.border B.bordered v F hborder hvs hF).mpr
    intro W hWl hWh
    have hWt := positiveBufferBorderedEnergyRestrict_zero_trace hV hreal hlh W hWl hWh
    have hWzero : t (positiveBufferBorderedEnergyRestrict hV hreal hlh W hWl hWh) = 0 :=
      (positiveBufferNormalizedTrace_zero_iff B A hA _).mpr hWt
    change positiveBufferBorderedForm B.potential hV B.border B.bordered
      (positiveBufferBorderedEnergyRestrict hV hreal hlh u hut.1 hut.2) W = _
    rw [positiveBufferBorderedForm_restrict_adjoint hV hreal hlh B.border
      B.bordered hborder u W hut.1 hut.2 hWl hWh]
    change a (corr (R F)) (positiveBufferBorderedEnergyRestrict hV hreal hlh W hWl hWh) = _
    rw [hcform _ _ hWzero]
    change positiveBufferStatePairing (R F)
      (positiveBufferBorderedState B.potential B.bordered
        (positiveBufferBorderedEnergyRestrict hV hreal hlh W hWl hWh)) = _
    rw [positiveBufferBorderedEnergyRestrict_state]
    exact positiveBufferStatePairing_retained_test B.l B.h (R F)
      (positiveBufferBorderedState B.potential B.bordered W)
      (positiveBufferRetainedProjection_supported B.l B.h F)
  · intro U F hUF
    have hF : B.bordered = false → F.2 = 0 := by
      intro hb
      simp only [BorderedIntervalGraph, hb, Bool.false_eq_true, ite_false] at hUF
      exact hUF.2.2
    obtain ⟨u, hu, hus, hul, huh⟩ :=
      positiveBuffer_exists_bordered_energy_of_intervalGraph hreal B.border B.bordered
        B.l B.h U F hUF
    have hgraph : BorderedIntervalGraph B.potential B.border B.bordered B.l B.h
        (positiveBufferBorderedState B.potential B.bordered u) F := by
      rw [hu]
      exact hUF
    have huf := (positiveBuffer_borderedIntervalGraph_iff_zero_trace_form
      hV hreal hlh B.border B.bordered u F hborder hus hF).mp hgraph
    have hut : t u = 0 := (positiveBufferNormalizedTrace_zero_iff B A hA u).mpr ⟨hul, huh⟩
    have heq : u = corr (R F) := by
      apply positiveBufferDirichletCorrection_unique a positiveBufferStatePairing
        positiveBufferBoundaryPairing J positiveBufferStatePairing_self_eq_zero
        (positiveBufferBorderedState_injective B.potential B.bordered)
        L t C Γ hΓ hsymm hL hC (R F) u hut
      intro W hW
      have hWt := (positiveBufferNormalizedTrace_zero_iff B A hA W).mp hW
      exact huf W hWt.1 hWt.2
    rw [hG, ← heq]
    change positiveBufferRetainedProjection B.l B.h
      (positiveBufferBorderedState B.potential B.bordered u) = U
    rw [positiveBufferRetainedProjection_eq_self B.l B.h _ hus, hu]

end ContinuousFlexibility.Radial
