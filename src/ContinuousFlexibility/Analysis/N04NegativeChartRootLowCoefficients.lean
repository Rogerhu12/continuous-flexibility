import ContinuousFlexibility.Analysis.N04NegativeChartFieldPowerControl
import ContinuousFlexibility.Analysis.CylinderMixedJets
import ContinuousFlexibility.Analysis.OneSidedOrdinaryJets
import ContinuousFlexibility.Analysis.MaterialEnvelopeNormalization

/-! The actual two coefficient jets needed by the positive root band.
The fixed low state order is chosen once; no extension has a numerical cost. -/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency true

private theorem endpointUnit_closed_representative_low
    {X I : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
    {p : ℕ → Seminorm ℝ X} (hp : Monotone p) {center : X} {base loss : ℕ}
    {U : Set X} {width E : I → ℝ} {H : I → PolarPoint → ℝ}
    {f : I → X → PolarPoint → ℝ}
    (A : EndpointPowerControl p center base loss U
      (fun i => Ioo (0 : ℝ) (width i) ×ˢ univ) (fun _ _ => 1) H
      (fun i _ => E i) f) (hw : ∀ i, 0 < width i) (hE : ∀ i, 1 ≤ E i) (s : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ i x, x ∈ U →
      p (max base (s + loss)) (x - center) ≤ 1 →
      ∀ g : PolarPoint → ℝ, ContDiff ℝ ∞ g →
      EqOn g (f i x) (Ioo (0 : ℝ) (width i) ×ˢ univ) →
      ∀ j, j ≤ s → ∀ q : PolarPoint, q.1 ∈ Icc (0 : ℝ) (width i) →
        ‖iteratedFDeriv ℝ j g q‖ ≤ B * E i ^ B := by
  obtain ⟨C, a, hC, ha, hb⟩ := A.bounds 0 s
  obtain ⟨B, hB, hpack⟩ := coefficientEnvelope_pack ((2 : ℝ) ^ s * C) a
  refine ⟨B, hB, ?_⟩
  intro i x hx hlow g hg heq j hj q hq
  have ho (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) (width i)) :
      ‖iteratedFDeriv ℝ j g (r, q.2)‖ ≤ B * E i ^ B := by
    have hpoint : (r, q.2) ∈ Ioo (0 : ℝ) (width i) ×ˢ (univ : Set ℝ) :=
      ⟨hr, mem_univ _⟩
    rw [iteratedFDeriv_eqOn_of_isOpen (isOpen_Ioo.prod isOpen_univ) heq j hpoint]
    have hCe : 0 ≤ C * E i ^ a := mul_nonneg (zero_le_one.trans hC)
      (Real.rpow_nonneg (zero_le_one.trans (hE i)) _)
    have hjet := norm_iteratedFDeriv_le_of_mixedDerivative
      (isOpen_Ioo.prod isOpen_univ) ((A.regular i).spatial x hx) j hpoint hCe
      (fun a b hab => by
        let J := (A.regular i).parameter a b (r, q.2) hpoint
        have hh := hb i 0 le_rfl a b (hab.trans_le hj) (r, q.2) hpoint J x hx
          ((hp (le_max_left _ _) _).trans hlow) (fun a => Fin.elim0 a)
          (fun a => Fin.elim0 a) 1 le_rfl
          ((hp (le_max_right _ _) _).trans hlow) (fun a => Fin.elim0 a)
        simpa only [smoothDirections_D_zero_apply J hx, one_pow, one_mul,
          parameterHeightWeight, ↓reduceIte, Real.one_rpow, mul_one] using hh)
    exact hjet.trans ((mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hj) hCe).trans
      ((mul_assoc ((2 : ℝ) ^ s) C (E i ^ a)).symm.trans_le (hpack (E i) (hE i))))
  exact le_on_closure ho
    (((hg.continuous_iteratedFDeriv (by simp : (j : ℕ∞ω) ≤ ∞)).comp
      (continuous_id.prodMk continuous_const)).norm.continuousOn)
    continuousOn_const (by simpa only [closure_Ioo (hw i).ne] using hq)

namespace N04RealizationStart.NegativeOpticalFactors

variable {W : N04RealizationStart} {e : ℕ ≃ N04PieceIndex W.D}
  {F : NegativeOpticalFactors W e} {base loss : ℕ}

/-- Both literal coefficient representatives have the same material
bound through order two on the closed physical half. -/
theorem FullHalfFieldPowerControl.root_low_coefficients
    (A : F.FullHalfFieldPowerControl base loss) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ z ∈ stateNeighborhood W.S W.C base W.negativeHalfStateRadius,
      pairGrading (stateGrading W.S) realGrading (max base (2 + loss))
        (z - (W.C.referenceState, 0)) ≤ 1 → ∀ m side,
      ∀ d c : PolarPoint → ℝ, ContDiff ℝ ∞ d → ContDiff ℝ ∞ c →
      EqOn d (F.fullHalfDrift z m side)
        (Ioo (0 : ℝ) (W.negativeOpticalWidth m side) ×ˢ univ) →
      EqOn c (F.fullHalfSpeed z m side)
        (Ioo (0 : ℝ) (W.negativeOpticalWidth m side) ×ˢ univ) →
      ∀ j, j ≤ 2 → ∀ p : PolarPoint,
        p.1 ∈ Icc (0 : ℝ) (W.negativeOpticalWidth m side) →
        ‖iteratedFDeriv ℝ j d p‖ ≤ B * W.T.E0 (W.negativeHalfSample e m side) ^ B ∧
        ‖iteratedFDeriv ℝ j c p‖ ≤ B * W.T.E0 (W.negativeHalfSample e m side) ^ B := by
  have hd := endpointUnit_closed_representative_low
    (jointStateGrading_monotone W.S) A.1
    (fun i => W.negativeOpticalWidth_pos i.1 i.2) (fun _ => W.floor _) 2
  have hc := endpointUnit_closed_representative_low
    (jointStateGrading_monotone W.S) A.2
    (fun i => W.negativeOpticalWidth_pos i.1 i.2) (fun _ => W.floor _) 2
  let Bd : ℝ := hd.choose
  let Bc : ℝ := hc.choose
  let B := max 1 (max Bd Bc)
  have hB : 1 ≤ B := le_max_left _ _
  have hmono {a E : ℝ} (ha : a ≤ B) (hE : 1 ≤ E) : a * E ^ a ≤ B * E ^ B :=
    mul_le_mul ha (Real.rpow_le_rpow_of_exponent_le hE ha)
      (Real.rpow_nonneg (zero_le_one.trans hE) _) (zero_le_one.trans hB)
  refine ⟨B, hB, fun z hz hlow m side d c hds hcs heqD heqC j hj p hp => ?_⟩
  exact ⟨(hd.choose_spec.2 (m, side) z hz hlow d hds heqD j hj p hp).trans
      (hmono ((le_max_left _ _).trans (le_max_right _ _)) (W.floor _)),
    (hc.choose_spec.2 (m, side) z hz hlow c hcs heqC j hj p hp).trans
      (hmono ((le_max_right _ _).trans (le_max_right _ _)) (W.floor _))⟩

end N04RealizationStart.NegativeOpticalFactors
end ContinuousFlexibility.Analysis
