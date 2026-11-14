module

public import ContinuousFlexibility.Analysis.OneHighCircleFourierInverseLow

/-!
# Uniform tame inversion of genuine circle lifts

The low geometry of the inverse is first derived from the forward geometry.
The high-order induction then composes the reciprocal forward defect with
the actual inverse, using the previously proved tame composition theorem.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Function
open scoped ContDiff

variable {P : ℝ} [Fact (0 < P)]

def circleInverseSobolevConstant (P c M : ℝ) : ℕ → ℝ
  | 0 => max 1 ((Real.sqrt ((circleLiftLowBound P M)⁻¹))⁻¹ *
      circleReciprocalSobolevConstant c (circleLiftLowBound P M) 0)
  | n + 1 => max 1 (circleLiftCompositionConstant P (circleLiftLowBound P M)⁻¹
      (circleInverseGeometrySobolevBound P c M) (n + 1) *
    (circleReciprocalSobolevConstant c (circleLiftLowBound P M) (n + 1) +
      circleReciprocalSobolevConstant c (circleLiftLowBound P M) 3 * M *
        circleInverseSobolevConstant P c M n))

theorem circleInverseSobolevConstant_one_le (P c M : ℝ) (s : ℕ) :
    1 ≤ circleInverseSobolevConstant P c M s := by
  cases s <;> exact le_max_left _ _

/-- At every order, the actual inverse defect is bounded by the forward
defect with a constant uniform over all lifts satisfying the fixed low data. -/
theorem circleInverse_defect_sobolev_le (s : ℕ) {c M : ℝ} (hc : 0 < c) (hM : 0 ≤ M) :
    ∀ (h ι : ℝ → ℝ) (hh : ContDiff ℝ ∞ h) (hi : ContDiff ℝ ∞ ι)
      (hι : ∀ x, h (ι x) = x) (ιh : ∀ x, ι (h x) = x)
      (hlift : ∀ x, h (x + P) = h x + P),
      (∀ x, c ≤ deriv h x) →
      circleRealSobolevNorm 3 (circleLiftDefectJet h hh hlift 0) ≤ M →
      circleRealSobolevNorm (s : ℝ)
          (circleLiftDefectJet ι hi (circleInverse_lift hι ιh hlift) 0) ≤
        circleInverseSobolevConstant P c M s *
          circleRealSobolevNorm (s : ℝ) (circleLiftDefectJet h hh hlift 0) := by
  induction s with
  | zero =>
    intro h ι hh hi hι ιh hlift hlower hlow
    have hbase := circleInverse_defect_h0_le h ι hh hi hι ιh hlift hc hM hlower hlow
    have hbound := hbase.trans
      (mul_le_mul_of_nonneg_right (le_max_right (1 : ℝ) _)
        (circle_real_sobolevNorm_nonneg 0 (circleLiftDefectJet h hh hlift 0)))
    simpa only [Nat.cast_zero, circleInverseSobolevConstant] using hbound
  | succ n ih =>
    intro h ι hh hi hι ιh hlift hlower hlow
    let B := circleLiftLowBound P M
    let MI := circleInverseGeometrySobolevBound P c M
    let ilift := circleInverse_lift hι ιh hlift
    let Q := circleLiftDefectJet h hh hlift
    let QI := circleLiftDefectJet ι hi ilift
    let R := circleLiftReciprocalDefect h
    let RJ := circleLiftReciprocalJet h hh hlift hc hlower
    have hpR := periodic_circleLiftReciprocalDefect h hlift
    have hR := contDiff_circleLiftReciprocalDefect hh hc hlower
    have hB : 1 ≤ B := circleLiftLowBound_one_le hM
    have hBpos : 0 < B := zero_lt_one.trans_le hB
    have hMI : 0 ≤ MI := circleInverseGeometrySobolevBound_nonneg hc hM
    have hilower : ∀ x, B⁻¹ ≤ deriv ι x :=
      circleInverse_deriv_lower hh hi hι hc hlower
        (circleLift_deriv_le_lowBound h hh hlift hM hlow)
    have hilow : circleRealSobolevNorm 3 (QI 0) ≤ MI :=
      circleInverse_defect_h3_le h ι hh hi hι ιh hlift hc hM hlower hlow
    have hcomp := circleLift_sobolev_comp_le (n + 1) (inv_pos.mpr hBpos) hMI
      R hpR hR ι hi ilift hilower hilow
    have hid := circleInverse_defectJet_zero_eq h ι hh hi hι hlift ilift hc hlower
    rw [← hid] at hcomp
    change circleRealSobolevNorm ((n + 1 : ℕ) : ℝ) (QI 0) ≤
      circleLiftCompositionConstant P B⁻¹ MI (n + 1) *
        (circleRealSobolevNorm ((n + 1 : ℕ) : ℝ) (RJ 0) +
          circleRealSobolevNorm 3 (RJ 0) * circleRealSobolevNorm (n : ℝ) (QI 0)) at hcomp
    have hK3 : 0 ≤ circleReciprocalSobolevConstant c B 3 :=
      circleReciprocalSobolevConstant_nonneg c B 3 hc (zero_le_one.trans hB)
    have hRhigh : circleRealSobolevNorm ((n + 1 : ℕ) : ℝ) (RJ 0) ≤
        circleReciprocalSobolevConstant c B (n + 1) *
          circleRealSobolevNorm ((n + 1 : ℕ) : ℝ) (Q 0) :=
      circleLiftReciprocalJet_sobolev_le h hh hlift hc hM hlower hlow (n + 1)
    have hR3 : circleRealSobolevNorm 3 (RJ 0) ≤ circleReciprocalSobolevConstant c B 3 * M :=
      (circleLiftReciprocalJet_sobolev_le h hh hlift hc hM hlower hlow 3).trans
        (mul_le_mul_of_nonneg_left hlow hK3)
    have hJ : 0 ≤ circleInverseSobolevConstant P c M n :=
      zero_le_one.trans (circleInverseSobolevConstant_one_le P c M n)
    have hprevious : circleRealSobolevNorm (n : ℝ) (QI 0) ≤
        circleInverseSobolevConstant P c M n *
          circleRealSobolevNorm ((n + 1 : ℕ) : ℝ) (Q 0) :=
      (ih h ι hh hi hι ιh hlift hlower hlow).trans
        (mul_le_mul_of_nonneg_left
          (circle_real_sobolevNorm_mono_of_derivatives Q
            (circleLiftDefectJet_hasDerivAt h hh hlift) (Nat.le_succ n)) hJ)
    have hterms : circleRealSobolevNorm ((n + 1 : ℕ) : ℝ) (RJ 0) +
          circleRealSobolevNorm 3 (RJ 0) * circleRealSobolevNorm (n : ℝ) (QI 0) ≤
        (circleReciprocalSobolevConstant c B (n + 1) +
          circleReciprocalSobolevConstant c B 3 * M * circleInverseSobolevConstant P c M n) *
            circleRealSobolevNorm ((n + 1 : ℕ) : ℝ) (Q 0) := by
      calc
        _ ≤ circleReciprocalSobolevConstant c B (n + 1) *
              circleRealSobolevNorm ((n + 1 : ℕ) : ℝ) (Q 0) +
            (circleReciprocalSobolevConstant c B 3 * M) *
              (circleInverseSobolevConstant P c M n *
                circleRealSobolevNorm ((n + 1 : ℕ) : ℝ) (Q 0)) :=
          add_le_add hRhigh (mul_le_mul hR3 hprevious
            (circle_real_sobolevNorm_nonneg _ _) (mul_nonneg hK3 hM))
        _ = _ := by ring
    have hC : 0 ≤ circleLiftCompositionConstant P B⁻¹ MI (n + 1) :=
      zero_le_one.trans (circleLiftCompositionConstant_one_le P B⁻¹ MI (n + 1))
    have hout := hcomp.trans (mul_le_mul_of_nonneg_left hterms hC)
    change circleRealSobolevNorm ((n + 1 : ℕ) : ℝ) (QI 0) ≤
      circleInverseSobolevConstant P c M (n + 1) *
        circleRealSobolevNorm ((n + 1 : ℕ) : ℝ) (Q 0)
    rw [circleInverseSobolevConstant]
    refine le_trans ?_ (mul_le_mul_of_nonneg_right (le_max_right _ _)
      (circle_real_sobolevNorm_nonneg _ _))
    simpa only [mul_assoc] using hout

/-- The inverse statement in the manuscript's H^(s-1) indexing. -/
theorem exists_circleLift_inverse_constant (s : ℕ) (c M : ℝ) (hc : 0 < c) (hM : 0 ≤ M) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (h ι : ℝ → ℝ) (hh : ContDiff ℝ ∞ h) (hi : ContDiff ℝ ∞ ι)
      (hι : ∀ x, h (ι x) = x) (ιh : ∀ x, ι (h x) = x)
      (hlift : ∀ x, h (x + P) = h x + P),
      (∀ x, c ≤ deriv h x) →
      circleRealSobolevNorm 3 (circleLiftDefectJet h hh hlift 0) ≤ M →
      circleRealSobolevNorm ((s - 1 : ℕ) : ℝ)
          (circleLiftDefectJet ι hi (circleInverse_lift hι ιh hlift) 0) ≤
        C * circleRealSobolevNorm ((s - 1 : ℕ) : ℝ) (circleLiftDefectJet h hh hlift 0) :=
  ⟨circleInverseSobolevConstant P c M (s - 1),
    circleInverseSobolevConstant_one_le P c M (s - 1),
    circleInverse_defect_sobolev_le (s - 1) hc hM⟩

end ContinuousFlexibility.Analysis
