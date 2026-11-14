module

public import ContinuousFlexibility.Analysis.OneHighCircleFourierInverseBasic

/-!
# Derived low Sobolev geometry of the actual inverse

The inverse H³ bound uses only the forward H³ derivative defect and the
positive forward Jacobian lower bound. In particular it is proved before
the high-order inverse induction and is not assumed as additional geometry.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Function MeasureTheory
open scoped ContDiff BigOperators

variable {P : ℝ} [Fact (0 < P)]

def circleInverseCompositionLowConstant (P c M : ℝ) : ℝ :=
  max 1 ((2 : ℝ) ^ 3 * (Real.sqrt ((circleLiftLowBound P M)⁻¹))⁻¹ *
    (1 + ∑ q : OrderedFinpartition 3,
      circleInverseLowBound c (circleLiftLowBound P M) ^ q.length))

theorem circleInverseCompositionLowConstant_one_le (P c M : ℝ) :
    1 ≤ circleInverseCompositionLowConstant P c M := le_max_left _ _

def circleInverseGeometrySobolevBound (P c M : ℝ) : ℝ :=
  circleInverseCompositionLowConstant P c M *
    circleReciprocalSobolevConstant c (circleLiftLowBound P M) 3 * M

theorem circleInverseGeometrySobolevBound_nonneg {c M : ℝ} (hc : 0 < c) (hM : 0 ≤ M) :
    0 ≤ circleInverseGeometrySobolevBound P c M :=
  mul_nonneg (mul_nonneg
    (zero_le_one.trans (circleInverseCompositionLowConstant_one_le P c M))
    (circleReciprocalSobolevConstant_nonneg c (circleLiftLowBound P M) 3 hc
      (zero_le_one.trans (circleLiftLowBound_one_le hM)))) hM

/-- The actual inverse defect has a uniform low H³ bound derived from
the original assumptions on the forward lift. -/
theorem circleInverse_defect_h3_le (h ι : ℝ → ℝ) (hh : ContDiff ℝ ∞ h)
    (hi : ContDiff ℝ ∞ ι) (hι : ∀ x, h (ι x) = x) (ιh : ∀ x, ι (h x) = x)
    (hlift : ∀ x, h (x + P) = h x + P) {c M : ℝ} (hc : 0 < c) (hM : 0 ≤ M)
    (hlower : ∀ x, c ≤ deriv h x)
    (hlow : circleRealSobolevNorm 3 (circleLiftDefectJet h hh hlift 0) ≤ M) :
    circleRealSobolevNorm 3
        (circleLiftDefectJet ι hi (circleInverse_lift hι ιh hlift) 0) ≤
      circleInverseGeometrySobolevBound P c M := by
  let B := circleLiftLowBound P M
  let ilift := circleInverse_lift hι ιh hlift
  let R := circleLiftReciprocalDefect h
  have hpR := periodic_circleLiftReciprocalDefect h hlift
  have hR := contDiff_circleLiftReciprocalDefect hh hc hlower
  have hB : 1 ≤ B := circleLiftLowBound_one_le hM
  have hBpos : 0 < B := zero_lt_one.trans_le hB
  have hupper := circleLift_deriv_le_lowBound h hh hlift hM hlow
  have hilower : ∀ x, B⁻¹ ≤ deriv ι x := circleInverse_deriv_lower hh hi hι hc hlower hupper
  have hibound (j : ℕ) (hj : 1 ≤ j) (hj3 : j ≤ 3) (x : ℝ) :
      ‖iteratedDeriv j ι x‖ ≤ circleInverseLowBound c B :=
    circleInverse_iteratedDeriv_norm_le hh hi hι hc hB hlower
      (circleLift_iteratedDeriv_norm_le_lowBound h hh hlift hM hlow) hj hj3 x
  have hraw := circleLift_sobolev_comp_le_of_derivative_bound R hpR hR ι hi ilift
    (inv_pos.mpr hBpos) (circleInverseLowBound_nonneg c B) hilower 3 hibound
  have hK : 0 ≤ circleReciprocalSobolevConstant c B 3 :=
    circleReciprocalSobolevConstant_nonneg c B 3 hc (zero_le_one.trans hB)
  have hRnorm : circleRealSobolevNorm 3 (circleLiftReciprocalJet h hh hlift hc hlower 0) ≤
      circleReciprocalSobolevConstant c B 3 * M :=
    (circleLiftReciprocalJet_sobolev_le h hh hlift hc hM hlower hlow 3).trans
      (mul_le_mul_of_nonneg_left hlow hK)
  have hid := circleInverse_defectJet_zero_eq h ι hh hi hι hlift ilift hc hlower
  calc
    _ ≤ circleInverseCompositionLowConstant P c M *
        circleRealSobolevNorm 3 (circleLiftReciprocalJet h hh hlift hc hlower 0) := by
      rw [hid]
      exact hraw.trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
        (circle_real_sobolevNorm_nonneg _ _))
    _ ≤ circleInverseCompositionLowConstant P c M *
        (circleReciprocalSobolevConstant c B 3 * M) :=
      mul_le_mul_of_nonneg_left hRnorm
        (zero_le_one.trans (circleInverseCompositionLowConstant_one_le P c M))
    _ = _ := by dsimp only [circleInverseGeometrySobolevBound, B]; ring

/-- The order-zero inverse-defect estimate uses genuine change of
variables and the first-derivative scalar Moser bound. -/
theorem circleInverse_defect_h0_le (h ι : ℝ → ℝ) (hh : ContDiff ℝ ∞ h)
    (hi : ContDiff ℝ ∞ ι) (hι : ∀ x, h (ι x) = x) (ιh : ∀ x, ι (h x) = x)
    (hlift : ∀ x, h (x + P) = h x + P) {c M : ℝ} (hc : 0 < c) (hM : 0 ≤ M)
    (hlower : ∀ x, c ≤ deriv h x)
    (hlow : circleRealSobolevNorm 3 (circleLiftDefectJet h hh hlift 0) ≤ M) :
    circleRealSobolevNorm 0
        (circleLiftDefectJet ι hi (circleInverse_lift hι ιh hlift) 0) ≤
      ((Real.sqrt ((circleLiftLowBound P M)⁻¹))⁻¹ *
        circleReciprocalSobolevConstant c (circleLiftLowBound P M) 0) *
          circleRealSobolevNorm 0 (circleLiftDefectJet h hh hlift 0) := by
  let B := circleLiftLowBound P M
  let ilift := circleInverse_lift hι ιh hlift
  let R := circleLiftReciprocalDefect h
  have hpR := periodic_circleLiftReciprocalDefect h hlift
  have hR := contDiff_circleLiftReciprocalDefect hh hc hlower
  have hBpos : 0 < B := zero_lt_one.trans_le (circleLiftLowBound_one_le hM)
  have hilower : ∀ x, B⁻¹ ≤ deriv ι x :=
    circleInverse_deriv_lower hh hi hι hc hlower
      (circleLift_deriv_le_lowBound h hh hlift hM hlow)
  have hcov := periodicCircleJet_l2_comp_le R hpR hR ι hi ilift (inv_pos.mpr hBpos) hilower
  have hzero : circleRealSobolevNorm 0 (circleLiftDefectJet ι hi ilift 0) ≤
      (Real.sqrt (B⁻¹))⁻¹ *
        circleRealSobolevNorm 0 (circleLiftReciprocalJet h hh hlift hc hlower 0) := by
    rw [circleInverse_defectJet_zero_eq h ι hh hi hι hlift ilift hc hlower]
    simpa only [circle_real_sobolevNorm_zero_eq_l2, circleLiftReciprocalJet, R] using hcov
  have hRzero := circleLiftReciprocalJet_sobolev_le h hh hlift hc hM hlower hlow 0
  simp only [Nat.cast_zero] at hRzero
  have hout := hzero.trans (mul_le_mul_of_nonneg_left hRzero
    (inv_nonneg.mpr (Real.sqrt_nonneg (B⁻¹))))
  simpa only [mul_assoc] using hout

end ContinuousFlexibility.Analysis
