import ContinuousFlexibility.Analysis.OneHighCircleFourierCompositionCalculus

/-!
# The high-order step in tame circle composition

One differentiation leaves an actual binary product. The derivative trade
between the outer function and the lift defect removes the apparently
uncontrolled product of two high norms.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Function MeasureTheory
open scoped ContDiff

variable {P : ℝ} [Fact (0 < P)]

def circleLiftCompositionStepConstant (P : ℝ) (r : ℕ) (c M K : ℝ) : ℝ :=
  (2 : ℝ) ^ (r + 4) * ((Real.sqrt c)⁻¹ + (2 : ℝ) ^ (r + 3) *
    (K * circleLiftLowBound P M * (1 + M) + circleSobolevEmbeddingConstant P *
      circleLiftCompositionLowConstant P 1 c M))

/-- The induction step only assumes the preceding composition estimate
for the actual outer derivative; its conclusion is the next Sobolev order. -/
theorem circleLift_sobolev_comp_le_step (u : ℝ → ℝ) (hp : Periodic u P)
    (hu : ContDiff ℝ ∞ u) (h : ℝ → ℝ) (hh : ContDiff ℝ ∞ h)
    (hlift : ∀ x, h (x + P) = h x + P) {c M K : ℝ} (hc : 0 < c)
    (hM : 0 ≤ M) (hK : 0 ≤ K) (hlower : ∀ x, c ≤ deriv h x)
    (hlow : circleRealSobolevNorm 3 (circleLiftDefectJet h hh hlift 0) ≤ M)
    (r : ℕ)
    (hprev : circleRealSobolevNorm ((r + 3 : ℕ) : ℝ)
        (periodicCircleJet ((deriv u) ∘ h)
          (periodic_comp_circleLift (periodic_circle_deriv hp) hlift)
          ((contDiff_infty_iff_deriv.mp hu).2.comp hh) 0) ≤ K *
      (circleRealSobolevNorm ((r + 3 : ℕ) : ℝ)
          (periodicCircleJet (deriv u) (periodic_circle_deriv hp)
            (contDiff_infty_iff_deriv.mp hu).2 0) +
        circleRealSobolevNorm 3
          (periodicCircleJet (deriv u) (periodic_circle_deriv hp)
            (contDiff_infty_iff_deriv.mp hu).2 0) *
          circleRealSobolevNorm ((r + 2 : ℕ) : ℝ) (circleLiftDefectJet h hh hlift 0))) :
    circleRealSobolevNorm ((r + 4 : ℕ) : ℝ)
        (periodicCircleJet (u ∘ h) (periodic_comp_circleLift hp hlift) (hu.comp hh) 0) ≤
      circleLiftCompositionStepConstant P r c M K *
        (circleRealSobolevNorm ((r + 4 : ℕ) : ℝ) (periodicCircleJet u hp hu 0) +
          circleRealSobolevNorm 3 (periodicCircleJet u hp hu 0) *
            circleRealSobolevNorm ((r + 3 : ℕ) : ℝ) (circleLiftDefectJet h hh hlift 0)) := by
  let U := periodicCircleJet u hp hu
  let DU := periodicCircleJet (deriv u) (periodic_circle_deriv hp)
    (contDiff_infty_iff_deriv.mp hu).2
  let W := periodicCircleJet (u ∘ h) (periodic_comp_circleLift hp hlift) (hu.comp hh)
  let F := periodicCircleJet ((deriv u) ∘ h)
    (periodic_comp_circleLift (periodic_circle_deriv hp) hlift)
    ((contDiff_infty_iff_deriv.mp hu).2.comp hh)
  let H := circleLiftDerivativeJet h hh hlift
  let Q := circleLiftDefectJet h hh hlift
  have hU := periodicCircleJet_hasDerivAt u hp hu
  have hF := periodicCircleJet_hasDerivAt ((deriv u) ∘ h)
    (periodic_comp_circleLift (periodic_circle_deriv hp) hlift)
    ((contDiff_infty_iff_deriv.mp hu).2.comp hh)
  have hH := circleLiftDerivativeJet_hasDerivAt h hh hlift
  have hQ := circleLiftDefectJet_hasDerivAt h hh hlift
  let A := circleRealSobolevNorm ((r + 4 : ℕ) : ℝ) (U 0)
  let Y := circleRealSobolevNorm 3 (U 0)
  let Z := circleRealSobolevNorm ((r + 3 : ℕ) : ℝ) (Q 0)
  let T := A + Y * Z
  let E := circleSobolevEmbeddingConstant P
  let B := circleLiftLowBound P M
  let K₁ := circleLiftCompositionLowConstant P 1 c M
  let D := K * B * (1 + M) + E * K₁
  have hA : 0 ≤ A := circle_real_sobolevNorm_nonneg _ _
  have hY : 0 ≤ Y := circle_real_sobolevNorm_nonneg _ _
  have hZ : 0 ≤ Z := circle_real_sobolevNorm_nonneg _ _
  have hT : 0 ≤ T := add_nonneg hA (mul_nonneg hY hZ)
  have hE : 0 ≤ E := (by positivity : (0 : ℝ) ≤ 1).trans
    (circleSobolevEmbeddingConstant_one_le P)
  have hB : 0 ≤ B := (by positivity : (0 : ℝ) ≤ 1).trans (circleLiftLowBound_one_le hM)
  have hK₁ : 0 ≤ K₁ := (by positivity : (0 : ℝ) ≤ 1).trans
    (circleLiftCompositionLowConstant_one_le P 1 c M)
  have hL : 0 ≤ (Real.sqrt c)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg c)
  have hDUzero : DU 0 = U 1 := periodicCircleJet_deriv_zero u hp hu
  have hDUhigh : circleRealSobolevNorm ((r + 3 : ℕ) : ℝ) (DU 0) ≤ A := by
    rw [hDUzero]
    simpa only [show r + 3 + 1 = r + 4 by omega] using
      circle_real_sobolevNorm_derivative_le U hU (r + 3) 1
  have hDU3 : circleRealSobolevNorm 3 (DU 0) ≤ circleRealSobolevNorm 4 (U 0) := by
    rw [hDUzero]
    exact circle_real_sobolevNorm_derivative_le U hU 3 1
  have hDU1 : circleRealSobolevNorm 1 (DU 0) ≤ Y := by
    rw [hDUzero]
    simpa only [Nat.cast_one] using
      (circle_real_sobolevNorm_derivative_le U hU 1 1).trans
        (circle_real_sobolevNorm_mono_of_derivatives U hU (show 2 ≤ 3 by omega))
  have hYle : Y ≤ A :=
    circle_real_sobolevNorm_mono_of_derivatives U hU (show 3 ≤ r + 4 by omega)
  have hQ2 : circleRealSobolevNorm 2 (Q 0) ≤ M :=
    (circle_real_sobolevNorm_mono_of_derivatives Q hQ (show 2 ≤ 3 by omega)).trans hlow
  have htrade := circle_real_sobolevNorm_trade_one_derivative U Q hU hQ r
  change circleRealSobolevNorm 4 (U 0) *
      circleRealSobolevNorm ((r + 2 : ℕ) : ℝ) (Q 0) ≤
        Y * Z + A * circleRealSobolevNorm 2 (Q 0) at htrade
  have hFhigh : circleRealSobolevNorm ((r + 3 : ℕ) : ℝ) (F 0) ≤
      K * ((1 + M) * A + Y * Z) := by
    apply hprev.trans
    apply mul_le_mul_of_nonneg_left _ hK
    calc
      _ ≤ A + circleRealSobolevNorm 4 (U 0) *
          circleRealSobolevNorm ((r + 2 : ℕ) : ℝ) (Q 0) :=
        add_le_add hDUhigh (mul_le_mul_of_nonneg_right hDU3
          (circle_real_sobolevNorm_nonneg _ _))
      _ ≤ A + (Y * Z + A * circleRealSobolevNorm 2 (Q 0)) := add_le_add le_rfl htrade
      _ ≤ A + (Y * Z + A * M) :=
        add_le_add le_rfl (add_le_add le_rfl (mul_le_mul_of_nonneg_left hQ2 hA))
      _ = (1 + M) * A + Y * Z := by ring
  have hFhigh' : circleRealSobolevNorm ((r + 3 : ℕ) : ℝ) (F 0) ≤
      K * (1 + M) * T := by
    apply hFhigh.trans
    have hinside : (1 + M) * A + Y * Z ≤ (1 + M) * T := by
      dsimp only [T]
      nlinarith only [mul_nonneg hM (mul_nonneg hY hZ)]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hinside hK
  have hFone : circleRealSobolevNorm 1 (F 0) ≤ K₁ * Y := by
    have hcomp := circleLift_sobolev_comp_le_low (deriv u) (periodic_circle_deriv hp)
      (contDiff_infty_iff_deriv.mp hu).2 h hh hlift hc hM hlower hlow 1 (by omega)
    simp only [Nat.cast_one] at hcomp
    exact hcomp.trans (mul_le_mul_of_nonneg_left hDU1 hK₁)
  have hFlow : circleRealFourierL1Norm (F 0) ≤ (E * K₁) * Y := by
    have hf := (circle_real_fourierL1Norm_le_sobolev_one_of_derivatives F hF 0).trans
      (mul_le_mul_of_nonneg_left hFone hE)
    simpa only [mul_assoc] using hf
  have hHhigh : circleRealSobolevNorm ((r + 3 : ℕ) : ℝ) (H 0) ≤ 1 + Z :=
    circleLiftDerivativeJet_sobolev_le h hh hlift (r + 3)
  have hHlow : circleRealFourierL1Norm (H 0) ≤ B :=
    circleLiftDerivativeJet_fourierL1_le_lowBound h hh hlift hlow
  have hfirst : circleRealSobolevNorm ((r + 3 : ℕ) : ℝ) (F 0) *
      circleRealFourierL1Norm (H 0) ≤ K * B * (1 + M) * T := by
    calc
      _ ≤ (K * (1 + M) * T) * circleRealFourierL1Norm (H 0) :=
        mul_le_mul_of_nonneg_right hFhigh' ENNReal.toReal_nonneg
      _ ≤ (K * (1 + M) * T) * B :=
        mul_le_mul_of_nonneg_left hHlow (by positivity)
      _ = _ := by ring
  have hsecond : circleRealFourierL1Norm (F 0) *
      circleRealSobolevNorm ((r + 3 : ℕ) : ℝ) (H 0) ≤ (E * K₁) * T := by
    have hYZ : Y * (1 + Z) ≤ T := by dsimp only [T]; nlinarith only [hYle]
    calc
      _ ≤ ((E * K₁) * Y) * circleRealSobolevNorm ((r + 3 : ℕ) : ℝ) (H 0) :=
        mul_le_mul_of_nonneg_right hFlow (circle_real_sobolevNorm_nonneg _ _)
      _ ≤ ((E * K₁) * Y) * (1 + Z) :=
        mul_le_mul_of_nonneg_left hHhigh (by positivity)
      _ = (E * K₁) * (Y * (1 + Z)) := by ring
      _ ≤ (E * K₁) * T := mul_le_mul_of_nonneg_left hYZ (mul_nonneg hE hK₁)
  have hproduct : circleRealSobolevNorm ((r + 3 : ℕ) : ℝ) (F 0 * H 0) ≤
      (2 : ℝ) ^ (r + 3) * D * T := by
    apply (circle_real_sobolevNorm_mul_le_of_derivatives F H hF hH (r + 3)).trans
    have hsum := add_le_add hfirst hsecond
    have hsum' : circleRealSobolevNorm ((r + 3 : ℕ) : ℝ) (F 0) *
          circleRealFourierL1Norm (H 0) + circleRealFourierL1Norm (F 0) *
          circleRealSobolevNorm ((r + 3 : ℕ) : ℝ) (H 0) ≤ D * T := by
      dsimp only [D]
      convert hsum using 1 <;> ring
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hsum' (by positivity : 0 ≤ (2 : ℝ) ^ (r + 3))
  have hWone : W 1 = F 0 * H 0 := periodicCircleJet_comp_one u hp hu h hh hlift
  have hWtop : circleRealSobolevNorm ((r + 3 : ℕ) : ℝ) (W 1) ≤
      (2 : ℝ) ^ (r + 3) * D * T := by rw [hWone]; exact hproduct
  have hWzero : (eLpNorm (W 0) 2 AddCircle.haarAddCircle).toReal ≤
      (Real.sqrt c)⁻¹ * A :=
    (periodicCircleJet_l2_comp_le u hp hu h hh hlift hc hlower).trans
      (mul_le_mul_of_nonneg_left
        (circle_real_derivative_l2_le_sobolev U hU (show 0 ≤ r + 4 by omega)) hL)
  have hbase : A ≤ T := by dsimp only [T]; nlinarith only [mul_nonneg hY hZ]
  have hrec := circle_real_sobolevNorm_succ_le_l2_add_derivative W
    (periodicCircleJet_hasDerivAt (u ∘ h) (periodic_comp_circleLift hp hlift) (hu.comp hh))
    (r + 3)
  rw [show r + 3 + 1 = r + 4 by omega] at hrec
  calc
    _ ≤ (2 : ℝ) ^ (r + 4) * ((eLpNorm (W 0) 2 AddCircle.haarAddCircle).toReal +
        circleRealSobolevNorm ((r + 3 : ℕ) : ℝ) (W 1)) := hrec
    _ ≤ (2 : ℝ) ^ (r + 4) * ((Real.sqrt c)⁻¹ * T +
        (2 : ℝ) ^ (r + 3) * D * T) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (hWzero.trans (mul_le_mul_of_nonneg_left hbase hL)) hWtop) (by positivity)
    _ = _ := by dsimp only [circleLiftCompositionStepConstant, D, B, E, K₁, T, A, Y, Z]; ring

end ContinuousFlexibility.Analysis
