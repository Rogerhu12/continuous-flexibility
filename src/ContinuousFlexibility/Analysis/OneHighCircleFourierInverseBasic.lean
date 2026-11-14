module

public import ContinuousFlexibility.Analysis.OneHighCircleFourierComposition
public import ContinuousFlexibility.Analysis.OneHighCircleInverseBounds
public import ContinuousFlexibility.Analysis.OneHighCircleReciprocal

/-!
# The genuine inverse defect as a reciprocal composition

The derivative defect of the actual inverse is identified pointwise with
the reciprocal function of the forward defect, composed with that inverse.
The scalar Moser estimate then applies uniformly to the outer function.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Function
open scoped ContDiff

variable {P : ℝ} [Fact (0 < P)]

theorem circleLiftDerivativeDefect_lower {h : ℝ → ℝ} {c : ℝ}
    (hlower : ∀ x, c ≤ deriv h x) (x : ℝ) : c - 1 ≤ circleLiftDerivativeDefect h x := by
  dsimp only [circleLiftDerivativeDefect]
  linarith only [hlower x]

def circleLiftReciprocalDefect (h : ℝ → ℝ) : ℝ → ℝ :=
  circleReciprocalDefect ∘ circleLiftDerivativeDefect h

theorem periodic_circleLiftReciprocalDefect (h : ℝ → ℝ)
    (hlift : ∀ x, h (x + P) = h x + P) : Periodic (circleLiftReciprocalDefect h) P :=
  periodic_circleReciprocal_comp (periodic_circleLiftDerivativeDefect h hlift)

theorem contDiff_circleLiftReciprocalDefect {h : ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h) {c : ℝ} (hc : 0 < c) (hlower : ∀ x, c ≤ deriv h x) :
    ContDiff ℝ ∞ (circleLiftReciprocalDefect h) :=
  contDiff_circleReciprocal_comp (contDiff_circleLiftDerivativeDefect hh) hc
    (circleLiftDerivativeDefect_lower hlower)

def circleLiftReciprocalJet (h : ℝ → ℝ) (hh : ContDiff ℝ ∞ h)
    (hlift : ∀ x, h (x + P) = h x + P) {c : ℝ} (hc : 0 < c)
    (hlower : ∀ x, c ≤ deriv h x) (n : ℕ) : C(AddCircle P, ℝ) :=
  periodicCircleJet (circleLiftReciprocalDefect h) (periodic_circleLiftReciprocalDefect h hlift)
    (contDiff_circleLiftReciprocalDefect hh hc hlower) n

/-- Uniform control of the actual reciprocal forward defect. -/
theorem circleLiftReciprocalJet_sobolev_le (h : ℝ → ℝ) (hh : ContDiff ℝ ∞ h)
    (hlift : ∀ x, h (x + P) = h x + P) {c M : ℝ} (hc : 0 < c) (hM : 0 ≤ M)
    (hlower : ∀ x, c ≤ deriv h x)
    (hlow : circleRealSobolevNorm 3 (circleLiftDefectJet h hh hlift 0) ≤ M) (s : ℕ) :
    circleRealSobolevNorm (s : ℝ) (circleLiftReciprocalJet h hh hlift hc hlower 0) ≤
      circleReciprocalSobolevConstant c (circleLiftLowBound P M) s *
        circleRealSobolevNorm (s : ℝ) (circleLiftDefectJet h hh hlift 0) :=
  circle_reciprocal_sobolev_le s c (circleLiftLowBound P M) hc
    (zero_le_one.trans (circleLiftLowBound_one_le hM))
    (circleLiftDerivativeDefect h) (periodic_circleLiftDerivativeDefect h hlift)
    (contDiff_circleLiftDerivativeDefect hh) (circleLiftDerivativeDefect_lower hlower)
    (circleLiftDefectJet_fourierL1_le_lowBound h hh hlift hlow)

theorem circleInverse_defect_eq_reciprocal_comp {h ι : ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h) (hi : ContDiff ℝ ∞ ι) (hι : ∀ x, h (ι x) = x)
    {c : ℝ} (hc : 0 < c) (hlower : ∀ x, c ≤ deriv h x) :
    circleLiftDerivativeDefect ι = circleLiftReciprocalDefect h ∘ ι := by
  funext x
  change deriv ι x - 1 = circleReciprocalDefect (deriv h (ι x) - 1)
  exact circleInverse_deriv_sub_one_eq_reciprocal hh hi hι x (hc.trans_le (hlower (ι x))).ne'

/-- This equality is between the actual continuous circle functions, so
all their Fourier coefficients and Sobolev norms agree. -/
theorem circleInverse_defectJet_zero_eq (h ι : ℝ → ℝ) (hh : ContDiff ℝ ∞ h)
    (hi : ContDiff ℝ ∞ ι) (hι : ∀ x, h (ι x) = x)
    (hlift : ∀ x, h (x + P) = h x + P) (ilift : ∀ x, ι (x + P) = ι x + P)
    {c : ℝ} (hc : 0 < c) (hlower : ∀ x, c ≤ deriv h x) :
    circleLiftDefectJet ι hi ilift 0 =
      periodicCircleJet (circleLiftReciprocalDefect h ∘ ι)
        (periodic_comp_circleLift (periodic_circleLiftReciprocalDefect h hlift) ilift)
        ((contDiff_circleLiftReciprocalDefect hh hc hlower).comp hi) 0 := by
  ext θ
  induction θ using QuotientAddGroup.induction_on
  rename_i x
  simp only [circleLiftDefectJet_coe_apply, periodicCircleJet_coe_apply, iteratedDeriv_zero]
  exact congrFun (circleInverse_defect_eq_reciprocal_comp hh hi hι hc hlower) x

end ContinuousFlexibility.Analysis
