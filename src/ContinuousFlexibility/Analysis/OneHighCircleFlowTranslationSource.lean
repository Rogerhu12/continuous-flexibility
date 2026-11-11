import ContinuousFlexibility.Analysis.OneHighCircleFlowSobolevBounds
import ContinuousFlexibility.Analysis.OneHighCircleFlowTranslationIntegral
import ContinuousFlexibility.Analysis.OneHighCircleFlowReferenceNorms

/-!
# Actual composition bounds for the translation source

The source is the genuine speed difference composed with the supplied
flow. The zeroth order uses the low composition estimate. At every
positive order, the proved flow defect bound and the derivative bound
for the reference difference give a constant controlled by Λ₄ and the
integrated low difference norm.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory Function
open scoped ContDiff

variable {P : ℝ} [hP : Fact (0 < P)]

theorem circleFlowReferenceNorm_eq (G : PolarPoint → ℝ) (hG : ContDiff ℝ ∞ G)
    (hperiod : ∀ t : ℝ, Function.Periodic (fun θ => G (t, θ)) P)
    (c : ℝ → ℝ) (s : ℕ) (t : ℝ) :
    circleFlowReferenceNorm G hG hperiod c s t =
      circleRealSobolevNorm (s : ℝ)
        (periodicCircleJet (fun θ => G (t, θ) - c t)
          (circle_periodic_sub_const (hperiod t) (c t))
          ((hG.comp (contDiff_const.prodMk contDiff_id)).sub contDiff_const) 0) :=
  congrArg (circleRealSobolevNorm (s : ℝ))
    (periodicCircleJet_sub_const (fun θ => G (t, θ)) (hperiod t)
      (hG.comp (contDiff_const.prodMk contDiff_id)) (c t) 0)

variable {G Θ : PolarPoint → ℝ} {a b : ℝ}
  (hG : ContDiff ℝ ∞ G)
  (hperiod : ∀ t : ℝ, Function.Periodic (fun θ => G (t, θ)) P)
  (hΘ : ∀ θ : ℝ, ContinuousOn (fun r => Θ (r, θ)) (Icc a b))
  (hinit : ∀ θ : ℝ, Θ (a, θ) = θ)
  (hflow : ∀ t ∈ Ioo a b, ∀ θ : ℝ,
    HasDerivAt (fun r => Θ (r, θ)) (G (t, Θ (t, θ))) t)

theorem circleFlow_reference_source_eq (c : ℝ → ℝ) {t : ℝ} (ht : t ∈ Icc a b) :
    circleSubtractConstantJet
        (circleFlowComposedSpeedJet hG hperiod hΘ hinit hflow t) (c t) 0 =
      periodicCircleJet ((fun θ => G (t, θ) - c t) ∘ (fun θ => Θ (t, θ)))
        (periodic_comp_circleLift
          (circle_periodic_sub_const (hperiod t) (c t))
          (circleFlow_lift_add hG hperiod hΘ hinit hflow ht))
        (((hG.comp (contDiff_const.prodMk contDiff_id)).sub contDiff_const).comp
          (circleFlow_contDiff_angle hG hP.out hperiod hΘ hinit hflow ht)) 0 := by
  ext x
  induction x using QuotientAddGroup.induction_on
  rename_i θ
  simp only [circleSubtractConstantJet_apply, if_pos rfl,
    circleFlowComposedSpeedJet_coe_apply hG hperiod hΘ hinit hflow ht,
    periodicCircleJet_coe_apply, iteratedDeriv_zero, Function.comp_apply]

theorem circleFlow_reference_source_zero_le (c : ℝ → ℝ) {t : ℝ} (ht : t ∈ Icc a b) :
    circleRealSobolevNorm 0
        (circleSubtractConstantJet
          (circleFlowComposedSpeedJet hG hperiod hΘ hinit hflow t) (c t) 0) ≤
      circleLiftCompositionLowConstant P 0
        (Real.exp (-(circleFlowEmbeddingConstant P * circleFlowLambda G hG hperiod 4 a b)))
        (circleFlowLowGeometryBound P (circleFlowLambda G hG hperiod 4 a b)) *
          circleFlowReferenceNorm G hG hperiod c 0 t := by
  rw [circleFlow_reference_source_eq hG hperiod hΘ hinit hflow c ht,
    circleFlowReferenceNorm_eq G hG hperiod c 0 t]
  exact circleLift_sobolev_comp_le_low (fun θ => G (t, θ) - c t)
    (circle_periodic_sub_const (hperiod t) (c t))
    ((hG.comp (contDiff_const.prodMk contDiff_id)).sub contDiff_const)
    (fun θ => Θ (t, θ)) (circleFlow_contDiff_angle hG hP.out hperiod hΘ hinit hflow ht)
    (circleFlow_lift_add hG hperiod hΘ hinit hflow ht)
    (Real.exp_pos _) (circleFlowLowGeometryBound_nonneg P
      (circleFlowLambda_nonneg G hG hperiod 4 (ht.1.trans ht.2)))
    (fun θ => (circleFlow_deriv_bounds_lowSobolev hG hperiod hΘ hinit hflow ht θ).1)
    (circleFlow_defect_h3_le hG hperiod hΘ hinit hflow ht) 0 (by norm_num)

theorem circleFlow_reference_source_succ_le {c : ℝ → ℝ}
    (hc : IntervalIntegrable c volume a b) (s : ℕ) {t : ℝ} (ht : t ∈ Icc a b) :
    circleRealSobolevNorm ((s + 1 : ℕ) : ℝ)
        (circleSubtractConstantJet
          (circleFlowComposedSpeedJet hG hperiod hΘ hinit hflow t) (c t) 0) ≤
      circleLiftCompositionConstant P
        (Real.exp (-(circleFlowEmbeddingConstant P * circleFlowLambda G hG hperiod 4 a b)))
        (circleFlowLowGeometryBound P (circleFlowLambda G hG hperiod 4 a b)) (s + 1) *
        (circleFlowReferenceNorm G hG hperiod c (s + 1) t +
          circleFlowReferenceNorm G hG hperiod c 3 t *
            (circleFlowSobolevConstant P (circleFlowLambda G hG hperiod 4 a b) s *
              circleFlowReferenceSize G hG hperiod c (s + 1) a b)) := by
  have hdefect := circleFlow_defect_sobolev_le hG hperiod hΘ hinit hflow s ht
  rw [circleFlowDefectJet_eq hG hperiod hΘ hinit hflow ht 0] at hdefect
  have hY := hdefect.trans (mul_le_mul_of_nonneg_left
    (circleFlowLambda_le_referenceSize G hG hperiod (ht.1.trans ht.2) hc s)
    (circleFlowSobolevConstant_pos P (circleFlowLambda G hG hperiod 4 a b) s).le)
  rw [circleFlow_reference_source_eq hG hperiod hΘ hinit hflow c ht,
    circleFlowReferenceNorm_eq G hG hperiod c (s + 1) t,
    circleFlowReferenceNorm_eq G hG hperiod c 3 t]
  have hcomp := circleLift_sobolev_comp_le (s + 1) (Real.exp_pos _)
    (circleFlowLowGeometryBound_nonneg P
      (circleFlowLambda_nonneg G hG hperiod 4 (ht.1.trans ht.2)))
    (fun θ => G (t, θ) - c t)
    (circle_periodic_sub_const (hperiod t) (c t))
    ((hG.comp (contDiff_const.prodMk contDiff_id)).sub contDiff_const)
    (fun θ => Θ (t, θ)) (circleFlow_contDiff_angle hG hP.out hperiod hΘ hinit hflow ht)
    (circleFlow_lift_add hG hperiod hΘ hinit hflow ht)
    (fun θ => (circleFlow_deriv_bounds_lowSobolev hG hperiod hΘ hinit hflow ht θ).1)
    (circleFlow_defect_h3_le hG hperiod hΘ hinit hflow ht)
  simp only [Nat.add_sub_cancel] at hcomp
  apply hcomp.trans
  apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans
    (circleLiftCompositionConstant_one_le _ _ _ _))
  exact add_le_add le_rfl
    (mul_le_mul_of_nonneg_left hY (circle_real_sobolevNorm_nonneg _ _))

end ContinuousFlexibility.Analysis
