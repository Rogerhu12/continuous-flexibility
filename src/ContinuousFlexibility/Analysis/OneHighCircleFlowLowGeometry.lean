import ContinuousFlexibility.Analysis.OneHighCircleFlowLowGeometryBasic
import ContinuousFlexibility.Analysis.OneHighCircleFlowJetBounds
import ContinuousFlexibility.Analysis.OneHighCircleFourierLiftGeometry

/-!
# The genuine low `H³` geometry bound for a circle flow

The first four actual flow jets are controlled by the common speed
envelope supplied by `H⁴(Gθ)`. The existing endpoint-derivative comparison
then bounds the actual `H³` norm of `Θθ - 1`. The resulting explicit
constant depends only on the period and `Λ₄`.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open scoped ContDiff ENNReal

/-- A uniform low-geometry constant depending only on the period and `Λ₄`. -/
def circleFlowLowGeometryBound (P L : ℝ) : ℝ :=
  16 * (circleFlowJetBound 4 (circleSobolevEmbeddingConstant P * L) + 1)

theorem circleFlowLowGeometryBound_nonneg (P : ℝ) {L : ℝ} (hL : 0 ≤ L) :
    0 ≤ circleFlowLowGeometryBound P L := by
  have hE : 0 ≤ circleSobolevEmbeddingConstant P :=
    zero_le_one.trans (circleSobolevEmbeddingConstant_one_le P)
  have hK : 0 ≤ circleFlowJetBound 4 (circleSobolevEmbeddingConstant P * L) :=
    zero_le_one.trans (circleFlowJetBound_one_le 4 (mul_nonneg hE hL))
  exact mul_nonneg (by norm_num) (add_nonneg hK zero_le_one)

variable {P : ℝ} [hP : Fact (0 < P)]

/-- The actual low Sobolev geometry of the genuine flow is bounded using
only `Λ₄`; it is never supplied as a hypothesis for the flow estimates. -/
theorem circleFlow_defect_h3_le {G Θ : PolarPoint → ℝ} {a b : ℝ}
    (hG : ContDiff ℝ ∞ G)
    (hperiod : ∀ t : ℝ, Function.Periodic (fun θ => G (t, θ)) P)
    (hΘ : ∀ θ : ℝ, ContinuousOn (fun r => Θ (r, θ)) (Icc a b))
    (hinit : ∀ θ : ℝ, Θ (a, θ) = θ)
    (hflow : ∀ t ∈ Ioo a b, ∀ θ : ℝ,
      HasDerivAt (fun r => Θ (r, θ)) (G (t, Θ (t, θ))) t)
    {t : ℝ} (ht : t ∈ Icc a b) :
    circleRealSobolevNorm 3
        (circleLiftDefectJet (fun θ => Θ (t, θ))
          (circleFlow_contDiff_angle hG hP.out hperiod hΘ hinit hflow ht)
          (circleFlow_lift_add hG hperiod hΘ hinit hflow ht) 0) ≤
      circleFlowLowGeometryBound P (circleFlowLambda G hG hperiod 4 a b) := by
  let J : ℕ → C(AddCircle P, ℝ) :=
    circleLiftDefectJet (fun θ => Θ (t, θ))
      (circleFlow_contDiff_angle hG hP.out hperiod hΘ hinit hflow ht)
      (circleFlow_lift_add hG hperiod hΘ hinit hflow ht)
  let K : ℝ := circleFlowJetBound 4
    (circleSobolevEmbeddingConstant P * circleFlowLambda G hG hperiod 4 a b)
  have hE : 0 ≤ circleSobolevEmbeddingConstant P :=
    zero_le_one.trans (circleSobolevEmbeddingConstant_one_le P)
  have hL := circleFlowLambda_nonneg G hG hperiod 4 (ht.1.trans ht.2)
  have hK : 0 ≤ K :=
    zero_le_one.trans (circleFlowJetBound_one_le 4 (mul_nonneg hE hL))
  have hB : Continuous (fun r => circleSobolevEmbeddingConstant P *
      circleRealSobolevNorm 4 (circleFlowSpeedJet G hG hperiod r 1)) :=
    continuous_const.mul (continuous_circleFlowSpeedSobolevNorm G hG hperiod 4 1)
  have hbound := circleFlow_angularJets_le_bound (ht.1.trans ht.2) hG hP.out hperiod
    hΘ hinit hflow hB.continuousOn (fun _ _ => mul_nonneg hE ENNReal.toReal_nonneg) 4
    (fun r _ j hj hj4 θ => circleFlow_speedDerivative_le_h4 G hG hperiod r hj hj4 θ)
  have hjetBound (j : ℕ) (hj : 1 ≤ j) (hj4 : j ≤ 4) (θ : ℝ) :
      |iteratedDeriv j (fun η => Θ (t, η)) θ| ≤ K := by
    simpa only [intervalIntegral.integral_const_mul, circleFlowLambda] using hbound t ht j hj hj4 θ
  have hsup (n : ℕ) (hn : n ≤ 3) : ‖J n‖ ≤ K + 1 := by
    apply ((J n).norm_le (add_nonneg hK zero_le_one)).mpr
    intro x
    induction x using QuotientAddGroup.induction_on
    rename_i x
    simp only [J, circleLiftDefectJet_coe_apply_eq, Real.norm_eq_abs]
    have hconst : |if n = 0 then (1 : ℝ) else 0| ≤ 1 := by split_ifs <;> norm_num
    calc
      |iteratedDeriv (n + 1) (fun θ => Θ (t, θ)) x - if n = 0 then 1 else 0| ≤
          |iteratedDeriv (n + 1) (fun θ => Θ (t, θ)) x| + |if n = 0 then 1 else 0| := by
        simpa only [Real.norm_eq_abs] using norm_sub_le
          (iteratedDeriv (n + 1) (fun θ => Θ (t, θ)) x) (if n = 0 then (1 : ℝ) else 0)
      _ ≤ K + 1 := add_le_add (hjetBound (n + 1) (by omega) (by omega) x) hconst
  have hzero := (circle_l2_le_supNorm (J 0)).trans (hsup 0 (by norm_num))
  have hthree := (circle_l2_le_supNorm (J 3)).trans (hsup 3 le_rfl)
  calc
    circleRealSobolevNorm 3 (J 0) ≤ (2 : ℝ) ^ (3 : ℕ) *
        ((eLpNorm (J 0) 2 AddCircle.haarAddCircle).toReal +
          (eLpNorm (J 3) 2 AddCircle.haarAddCircle).toReal) :=
      circle_real_sobolevNorm_le_derivative_endpoints J
        (circleLiftDefectJet_hasDerivAt (fun θ => Θ (t, θ))
          (circleFlow_contDiff_angle hG hP.out hperiod hΘ hinit hflow ht)
          (circleFlow_lift_add hG hperiod hΘ hinit hflow ht)) 3
    _ ≤ (2 : ℝ) ^ (3 : ℕ) * ((K + 1) + (K + 1)) :=
      mul_le_mul_of_nonneg_left (add_le_add hzero hthree) (by positivity)
    _ = circleFlowLowGeometryBound P (circleFlowLambda G hG hperiod 4 a b) := by
      dsimp only [circleFlowLowGeometryBound, K]
      ring

end ContinuousFlexibility.Analysis
