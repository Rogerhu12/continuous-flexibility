import ContinuousFlexibility.Analysis.OneHighCircleFourierLiftBounds
import ContinuousFlexibility.Analysis.OneHighCircleFourierInterpolation

/-!
# Actual chain rule and uniform low composition constants

The circle functions below are descended from ordinary smooth periodic
functions. The chain-rule factorization and every derivative tower therefore
come from the actual functions, with no auxiliary jet hypotheses.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Function MeasureTheory
open scoped ContDiff BigOperators

variable {P : ℝ} [Fact (0 < P)]

theorem periodic_circle_deriv {u : ℝ → ℝ} (hp : Periodic u P) :
    Periodic (deriv u) P := by
  simpa only [iteratedDeriv_one] using periodic_iteratedDeriv hp 1

theorem periodicCircleJet_deriv_zero (u : ℝ → ℝ) (hp : Periodic u P)
    (hu : ContDiff ℝ ∞ u) :
    periodicCircleJet (deriv u) (periodic_circle_deriv hp)
      (contDiff_infty_iff_deriv.mp hu).2 0 = periodicCircleJet u hp hu 1 := by
  ext θ
  induction θ using QuotientAddGroup.induction_on
  simp only [periodicCircleJet_coe_apply, iteratedDeriv_zero, iteratedDeriv_one]

/-- The first actual derivative of a composition is the product of the
composed outer derivative and the actual lift derivative. -/
theorem periodicCircleJet_comp_one (u : ℝ → ℝ) (hp : Periodic u P)
    (hu : ContDiff ℝ ∞ u) (h : ℝ → ℝ) (hh : ContDiff ℝ ∞ h)
    (hlift : ∀ x, h (x + P) = h x + P) :
    periodicCircleJet (u ∘ h) (periodic_comp_circleLift hp hlift) (hu.comp hh) 1 =
      periodicCircleJet ((deriv u) ∘ h)
        (periodic_comp_circleLift (periodic_circle_deriv hp) hlift)
        ((contDiff_infty_iff_deriv.mp hu).2.comp hh) 0 *
          circleLiftDerivativeJet h hh hlift 0 := by
  ext θ
  induction θ using QuotientAddGroup.induction_on
  rename_i x
  simp only [ContinuousMap.mul_apply, periodicCircleJet_coe_apply,
    circleLiftDerivativeJet_coe_apply, iteratedDeriv_one, iteratedDeriv_zero,
    Function.comp_apply]
  exact deriv_comp x (hu.differentiable (by simp) (h x))
    (hh.differentiable (by simp) x)

/-- A uniform constant for the first three Sobolev orders. -/
def circleLiftCompositionLowConstant (P : ℝ) (s : ℕ) (c M : ℝ) : ℝ :=
  max 1 ((2 : ℝ) ^ s * (Real.sqrt c)⁻¹ *
    (1 + ∑ q : OrderedFinpartition s, circleLiftLowBound P M ^ q.length))

theorem circleLiftCompositionLowConstant_one_le (P : ℝ) (s : ℕ) (c M : ℝ) :
    1 ≤ circleLiftCompositionLowConstant P s c M := le_max_left _ _

theorem circleLift_sobolev_comp_le_low (u : ℝ → ℝ) (hp : Periodic u P)
    (hu : ContDiff ℝ ∞ u) (h : ℝ → ℝ) (hh : ContDiff ℝ ∞ h)
    (hlift : ∀ x, h (x + P) = h x + P) {c M : ℝ} (hc : 0 < c) (hM : 0 ≤ M)
    (hlower : ∀ x, c ≤ deriv h x)
    (hlow : circleRealSobolevNorm 3 (circleLiftDefectJet h hh hlift 0) ≤ M)
    (s : ℕ) (hs : s ≤ 3) :
    circleRealSobolevNorm (s : ℝ)
        (periodicCircleJet (u ∘ h) (periodic_comp_circleLift hp hlift) (hu.comp hh) 0) ≤
      circleLiftCompositionLowConstant P s c M *
        circleRealSobolevNorm (s : ℝ) (periodicCircleJet u hp hu 0) := by
  have hB : 0 ≤ circleLiftLowBound P M :=
    (by positivity : (0 : ℝ) ≤ 1).trans (circleLiftLowBound_one_le hM)
  have hraw := circleLift_sobolev_comp_le_of_derivative_bound u hp hu h hh hlift
    hc hB hlower s (fun j hj hjs x =>
      circleLift_iteratedDeriv_norm_le_lowBound h hh hlift hM hlow j hj (hjs.trans hs) x)
  exact hraw.trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
    (circle_real_sobolevNorm_nonneg _ _))

end ContinuousFlexibility.Analysis
