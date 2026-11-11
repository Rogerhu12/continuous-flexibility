import ContinuousFlexibility.Analysis.OneHighCircleFourierLiftGeometry
import ContinuousFlexibility.Analysis.OneHighCircleFourierRealAlgebra

/-!
# Low geometry controlled by the actual derivative defect

The prescribed `H³` bound on `h' - 1` controls the first three pointwise
derivatives of a circle lift and the Fourier `L¹` norm of `h'`. These are
the uniform low-order inputs to the tame composition induction.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Function MeasureTheory
open scoped ContDiff

variable {P : ℝ} [Fact (0 < P)]

theorem periodic_circleLift_deriv (h : ℝ → ℝ)
    (hlift : ∀ x, h (x + P) = h x + P) : Periodic (deriv h) P := by
  intro x
  have hx := periodic_circleLiftDerivativeDefect h hlift x
  change deriv h (x + P) - 1 = deriv h x - 1 at hx
  linarith

/-- The canonical circle jets of the actual lift derivative. -/
def circleLiftDerivativeJet (h : ℝ → ℝ) (hh : ContDiff ℝ ∞ h)
    (hlift : ∀ x, h (x + P) = h x + P) (n : ℕ) : C(AddCircle P, ℝ) :=
  periodicCircleJet (deriv h) (periodic_circleLift_deriv h hlift)
    (contDiff_infty_iff_deriv.mp hh).2 n

@[simp] theorem circleLiftDerivativeJet_coe_apply (h : ℝ → ℝ)
    (hh : ContDiff ℝ ∞ h) (hlift : ∀ x, h (x + P) = h x + P) (n : ℕ) (x : ℝ) :
    circleLiftDerivativeJet h hh hlift n (x : AddCircle P) =
      iteratedDeriv n (deriv h) x := periodicCircleJet_coe_apply _ _ _ n x

theorem circleLiftDerivativeJet_hasDerivAt (h : ℝ → ℝ) (hh : ContDiff ℝ ∞ h)
    (hlift : ∀ x, h (x + P) = h x + P) (n : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => circleLiftDerivativeJet h hh hlift n (y : AddCircle P))
      (circleLiftDerivativeJet h hh hlift (n + 1) (x : AddCircle P)) x :=
  periodicCircleJet_hasDerivAt _ _ _ n x

theorem circleLiftDerivativeJet_zero_eq_one_add_defect (h : ℝ → ℝ)
    (hh : ContDiff ℝ ∞ h) (hlift : ∀ x, h (x + P) = h x + P) :
    circleLiftDerivativeJet h hh hlift 0 = 1 + circleLiftDefectJet h hh hlift 0 := by
  ext θ
  induction θ using QuotientAddGroup.induction_on
  simp only [circleLiftDerivativeJet_coe_apply, iteratedDeriv_zero,
    ContinuousMap.add_apply, ContinuousMap.one_apply, circleLiftDefectJet_zero_coe_apply]
  ring

theorem circleLiftDerivativeJet_sobolev_le (h : ℝ → ℝ) (hh : ContDiff ℝ ∞ h)
    (hlift : ∀ x, h (x + P) = h x + P) (s : ℕ) :
    circleRealSobolevNorm (s : ℝ) (circleLiftDerivativeJet h hh hlift 0) ≤
      1 + circleRealSobolevNorm (s : ℝ) (circleLiftDefectJet h hh hlift 0) := by
  rw [circleLiftDerivativeJet_zero_eq_one_add_defect]
  have hone : MemLp (frequencyWeighted (circleFrequencyWeight P) (s : ℝ)
      (fourierCoeff (circleComplexify (1 : C(AddCircle P, ℝ))))) 2 Measure.count := by
    rw [circleComplexify_one]
    exact circle_frequencyWeighted_memLp_const (s : ℝ) (1 : ℂ)
  have hq := circle_frequencyWeighted_memLp_of_derivatives
    (fun k => circleComplexify (circleLiftDefectJet h hh hlift k))
    (circleComplexify_hasDerivAt _ (circleLiftDefectJet_hasDerivAt h hh hlift)) s
  simpa only [circle_real_sobolevNorm_one] using
    circle_real_sobolevNorm_add_le 1 (circleLiftDefectJet h hh hlift 0) (s : ℝ) hone hq

/-- A single low bound depending only on period and the prescribed geometry norm. -/
def circleLiftLowBound (P M : ℝ) : ℝ := circleSobolevEmbeddingConstant P * (1 + M)

theorem circleLiftLowBound_one_le {M : ℝ} (hM : 0 ≤ M) :
    1 ≤ circleLiftLowBound P M := by
  have hE := circleSobolevEmbeddingConstant_one_le P
  dsimp only [circleLiftLowBound]
  nlinarith only [hE, mul_nonneg ((by positivity : (0 : ℝ) ≤ 1).trans hE) hM]

/-- The first three actual derivatives of a lift are uniformly bounded
by its prescribed low `H³` geometry. -/
theorem circleLift_iteratedDeriv_norm_le_lowBound (h : ℝ → ℝ)
    (hh : ContDiff ℝ ∞ h) (hlift : ∀ x, h (x + P) = h x + P) {M : ℝ}
    (hM : 0 ≤ M)
    (hlow : circleRealSobolevNorm 3 (circleLiftDefectJet h hh hlift 0) ≤ M)
    (j : ℕ) (hj : 1 ≤ j) (hj3 : j ≤ 3) (x : ℝ) :
    ‖iteratedDeriv j h x‖ ≤ circleLiftLowBound P M := by
  let Q := circleLiftDefectJet h hh hlift
  have hQ := circleLiftDefectJet_hasDerivAt h hh hlift
  have hE : 0 ≤ circleSobolevEmbeddingConstant P :=
    (by positivity : (0 : ℝ) ≤ 1).trans (circleSobolevEmbeddingConstant_one_le P)
  cases j with
  | zero => omega
  | succ n =>
    have hn : 1 + n ≤ 3 := by omega
    have hQnorm : circleRealSobolevNorm 1 (Q n) ≤ M :=
      (circle_real_sobolevNorm_derivative_le Q hQ 1 n).trans
        ((circle_real_sobolevNorm_mono_of_derivatives Q hQ hn).trans hlow)
    have hpoint : ‖Q n (x : AddCircle P)‖ ≤ circleSobolevEmbeddingConstant P * M :=
      (circle_real_norm_apply_le_sobolev_one_of_derivatives Q hQ n (x : AddCircle P)).trans
        (mul_le_mul_of_nonneg_left hQnorm hE)
    have heq : iteratedDeriv (n + 1) h x =
        Q n (x : AddCircle P) + if n = 0 then 1 else 0 := by
      have he := circleLiftDefectJet_coe_apply_eq h hh hlift n x
      change Q n (x : AddCircle P) = _ at he
      exact (eq_sub_iff_add_eq.mp he).symm
    have hcorr : ‖(if n = 0 then (1 : ℝ) else 0)‖ ≤ 1 := by
      split_ifs <;> norm_num
    calc
      ‖iteratedDeriv (n + 1) h x‖ =
          ‖Q n (x : AddCircle P) + if n = 0 then 1 else 0‖ := congrArg norm heq
      _ ≤ ‖Q n (x : AddCircle P)‖ + ‖(if n = 0 then (1 : ℝ) else 0)‖ := norm_add_le _ _
      _ ≤ circleSobolevEmbeddingConstant P * M + 1 := add_le_add hpoint hcorr
      _ ≤ circleLiftLowBound P M := by
        dsimp only [circleLiftLowBound]
        nlinarith only [circleSobolevEmbeddingConstant_one_le P]

/-- The Fourier `L¹` norm of the actual lift derivative has the same
uniform low bound. -/
theorem circleLiftDerivativeJet_fourierL1_le_lowBound (h : ℝ → ℝ)
    (hh : ContDiff ℝ ∞ h) (hlift : ∀ x, h (x + P) = h x + P) {M : ℝ}
    (hlow : circleRealSobolevNorm 3 (circleLiftDefectJet h hh hlift 0) ≤ M) :
    circleRealFourierL1Norm (circleLiftDerivativeJet h hh hlift 0) ≤
      circleLiftLowBound P M := by
  have hq : circleRealSobolevNorm 1 (circleLiftDefectJet h hh hlift 0) ≤ M :=
    (circle_real_sobolevNorm_mono_of_derivatives (circleLiftDefectJet h hh hlift)
      (circleLiftDefectJet_hasDerivAt h hh hlift) (show 1 ≤ 3 by omega)).trans hlow
  have hderiv := (circleLiftDerivativeJet_sobolev_le h hh hlift 1).trans
    (add_le_add le_rfl hq)
  exact (circle_real_fourierL1Norm_le_sobolev_one_of_derivatives
    (circleLiftDerivativeJet h hh hlift) (circleLiftDerivativeJet_hasDerivAt h hh hlift) 0).trans
      (mul_le_mul_of_nonneg_left hderiv
        ((by positivity : (0 : ℝ) ≤ 1).trans (circleSobolevEmbeddingConstant_one_le P)))

/-- The defect itself has a uniform Fourier `L¹` bound as well. -/
theorem circleLiftDefectJet_fourierL1_le_lowBound (h : ℝ → ℝ)
    (hh : ContDiff ℝ ∞ h) (hlift : ∀ x, h (x + P) = h x + P) {M : ℝ}
    (hlow : circleRealSobolevNorm 3 (circleLiftDefectJet h hh hlift 0) ≤ M) :
    circleRealFourierL1Norm (circleLiftDefectJet h hh hlift 0) ≤
      circleLiftLowBound P M := by
  have hq : circleRealSobolevNorm 1 (circleLiftDefectJet h hh hlift 0) ≤ M :=
    (circle_real_sobolevNorm_mono_of_derivatives (circleLiftDefectJet h hh hlift)
      (circleLiftDefectJet_hasDerivAt h hh hlift) (show 1 ≤ 3 by omega)).trans hlow
  have hE : 0 ≤ circleSobolevEmbeddingConstant P :=
    (by positivity : (0 : ℝ) ≤ 1).trans (circleSobolevEmbeddingConstant_one_le P)
  exact (circle_real_fourierL1Norm_le_sobolev_one_of_derivatives
    (circleLiftDefectJet h hh hlift) (circleLiftDefectJet_hasDerivAt h hh hlift) 0).trans
      ((mul_le_mul_of_nonneg_left hq hE).trans
        (mul_le_mul_of_nonneg_left (by linarith : M ≤ 1 + M) hE))

theorem circleLift_deriv_le_lowBound (h : ℝ → ℝ)
    (hh : ContDiff ℝ ∞ h) (hlift : ∀ x, h (x + P) = h x + P) {M : ℝ}
    (hM : 0 ≤ M)
    (hlow : circleRealSobolevNorm 3 (circleLiftDefectJet h hh hlift 0) ≤ M) (x : ℝ) :
    deriv h x ≤ circleLiftLowBound P M := by
  have hn := circleLift_iteratedDeriv_norm_le_lowBound h hh hlift hM hlow 1 le_rfl
    (by omega) x
  rw [iteratedDeriv_one, Real.norm_eq_abs] at hn
  exact (le_abs_self _).trans hn

end ContinuousFlexibility.Analysis
