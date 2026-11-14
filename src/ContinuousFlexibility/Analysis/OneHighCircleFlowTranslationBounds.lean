module

public import ContinuousFlexibility.Analysis.OneHighCircleFlowTranslationSource

/-!
# Uniform Sobolev comparison with the reference translation

For every integrable scalar reference speed, the actual displacement
from its translation is bounded by the integrated speed difference.
The explicit constant depends only on the period, the Sobolev order,
Λ₄, and the integrated H³ difference norm. The reference speed's mean
rotation never enters this constant.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open scoped ContDiff

def circleFlowTranslationHighFactor (P L : ℝ) : ℕ → ℝ
  | 0 => 0
  | s + 1 => circleFlowSobolevConstant P L s

theorem circleFlowTranslationHighFactor_nonneg (P L : ℝ) (s : ℕ) :
    0 ≤ circleFlowTranslationHighFactor P L s := by
  cases s with
  | zero => exact le_rfl
  | succ s => exact (circleFlowSobolevConstant_pos P L s).le

def circleFlowTranslationConstant (P L J : ℝ) (s : ℕ) : ℝ :=
  max 1 ((2 : ℝ) ^ (s + 1) *
    circleLiftCompositionConstant P (Real.exp (-(circleFlowEmbeddingConstant P * L)))
      (circleFlowLowGeometryBound P L) s *
        (1 + circleFlowTranslationHighFactor P L s * J))

theorem circleFlowTranslationConstant_one_le (P L J : ℝ) (s : ℕ) :
    1 ≤ circleFlowTranslationConstant P L J s := le_max_left _ _

variable {P : ℝ} [hP : Fact (0 < P)]
  {G Θ : PolarPoint → ℝ} {a b : ℝ}
  (hG : ContDiff ℝ ∞ G)
  (hperiod : ∀ t : ℝ, Function.Periodic (fun θ => G (t, θ)) P)
  (hΘ : ∀ θ : ℝ, ContinuousOn (fun r => Θ (r, θ)) (Icc a b))
  (hinit : ∀ θ : ℝ, Θ (a, θ) = θ)
  (hflow : ∀ t ∈ Ioo a b, ∀ θ : ℝ,
    HasDerivAt (fun r => Θ (r, θ)) (G (t, Θ (t, θ))) t)

private theorem circleFlow_reference_source_allOrders_le {c : ℝ → ℝ}
    (hc : IntervalIntegrable c volume a b) (s : ℕ) {t : ℝ} (ht : t ∈ Icc a b) :
    circleRealSobolevNorm (s : ℝ)
        (circleSubtractConstantJet
          (circleFlowComposedSpeedJet hG hperiod hΘ hinit hflow t) (c t) 0) ≤
      circleLiftCompositionConstant P
        (Real.exp (-(circleFlowEmbeddingConstant P * circleFlowLambda G hG hperiod 4 a b)))
        (circleFlowLowGeometryBound P (circleFlowLambda G hG hperiod 4 a b)) s *
        (circleFlowReferenceNorm G hG hperiod c s t +
          circleFlowReferenceNorm G hG hperiod c 3 t *
            (circleFlowTranslationHighFactor P (circleFlowLambda G hG hperiod 4 a b) s *
              circleFlowReferenceSize G hG hperiod c s a b)) := by
  cases s with
  | zero =>
    simpa only [circleFlowTranslationHighFactor, zero_mul, mul_zero, add_zero,
      circleLiftCompositionConstant, Nat.cast_zero] using
      circleFlow_reference_source_zero_le hG hperiod hΘ hinit hflow c ht
  | succ s =>
    exact circleFlow_reference_source_succ_le hG hperiod hΘ hinit hflow hc s ht

/-- The translation comparison at every natural Sobolev order, uniformly
on the closed time interval, for an arbitrary integrable scalar
reference speed. All source integrability and geometry are derived. -/
theorem circleFlow_translation_sobolev_le {c : ℝ → ℝ}
    (hc : IntervalIntegrable c volume a b) (s : ℕ) {t : ℝ} (ht : t ∈ Icc a b) :
    circleRealSobolevNorm (s : ℝ)
        (circleFlowTranslationJet hG hperiod hΘ hinit hflow c t 0) ≤
      circleFlowTranslationConstant P (circleFlowLambda G hG hperiod 4 a b)
        (circleFlowReferenceSize G hG hperiod c 3 a b) s *
          circleFlowReferenceSize G hG hperiod c s a b := by
  let L : ℝ := circleFlowLambda G hG hperiod 4 a b
  let C : ℝ := circleLiftCompositionConstant P
    (Real.exp (-(circleFlowEmbeddingConstant P * L))) (circleFlowLowGeometryBound P L) s
  let F : ℝ := circleFlowTranslationHighFactor P L s
  let J : ℝ := circleFlowReferenceSize G hG hperiod c s a b
  let J₃ : ℝ := circleFlowReferenceSize G hG hperiod c 3 a b
  have hC : 0 ≤ C := zero_le_one.trans (circleLiftCompositionConstant_one_le _ _ _ _)
  have hF : 0 ≤ F := circleFlowTranslationHighFactor_nonneg P L s
  have hJ : 0 ≤ J := circleFlowReferenceSize_nonneg G hG hperiod c s (ht.1.trans ht.2)
  have hc' : IntervalIntegrable c volume a t := hc.mono_set (by
    rw [uIcc_of_le ht.1, uIcc_of_le (ht.1.trans ht.2)]
    exact Icc_subset_Icc le_rfl ht.2)
  have hD (k : ℕ) :
      IntervalIntegrable (circleFlowReferenceNorm G hG hperiod c k) volume a t :=
    intervalIntegrable_circleFlowReferenceNorm G hG hperiod ht.1 hc' k
  have hsourceI : IntervalIntegrable (fun r => circleRealSobolevNorm (s : ℝ)
      (circleSubtractConstantJet
        (circleFlowComposedSpeedJet hG hperiod hΘ hinit hflow r) (c r) 0)) volume a t :=
    intervalIntegrable_circleSubtractConstantSobolevNorm
      (circleFlowComposedSpeedJet hG hperiod hΘ hinit hflow) ht.1
      (fun n => (continuousOn_circleFlowComposedSpeedJet hG hperiod hΘ hinit hflow n).mono
        (Icc_subset_Icc le_rfl ht.2))
      (fun r hr => circleFlowComposedSpeedJet_hasDerivAt hG hperiod hΘ hinit hflow
        ⟨hr.1, hr.2.trans ht.2⟩) hc' s
  have hmono := intervalIntegral.integral_mono_on (μ := volume) ht.1
    hsourceI (((hD s).add ((hD 3).mul_const (F * J))).const_mul C)
    (fun r hr => circleFlow_reference_source_allOrders_le hG hperiod hΘ hinit hflow hc s
      ⟨hr.1, hr.2.trans ht.2⟩)
  have hmono' : (∫ r in a..t, circleRealSobolevNorm (s : ℝ)
        (circleSubtractConstantJet
          (circleFlowComposedSpeedJet hG hperiod hΘ hinit hflow r) (c r) 0)) ≤
      C * (circleFlowReferenceSize G hG hperiod c s a t +
        circleFlowReferenceSize G hG hperiod c 3 a t * (F * J)) := by
    simpa only [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add (hD s) ((hD 3).mul_const (F * J)),
      intervalIntegral.integral_mul_const, circleFlowReferenceSize] using hmono
  have hpartial :
      C * (circleFlowReferenceSize G hG hperiod c s a t +
        circleFlowReferenceSize G hG hperiod c 3 a t * (F * J)) ≤
      C * (J + J₃ * (F * J)) :=
    mul_le_mul_of_nonneg_left
      (add_le_add (circleFlowReferenceSize_partial_le G hG hperiod hc ht s)
        (mul_le_mul_of_nonneg_right
          (circleFlowReferenceSize_partial_le G hG hperiod hc ht 3) (mul_nonneg hF hJ))) hC
  calc
    _ ≤ (2 : ℝ) ^ (s + 1) * ∫ r in a..t, circleRealSobolevNorm (s : ℝ)
        (circleSubtractConstantJet
          (circleFlowComposedSpeedJet hG hperiod hΘ hinit hflow r) (c r) 0) :=
      circleFlow_translation_sobolev_integral_le hG hperiod hΘ hinit hflow hc s ht
    _ ≤ (2 : ℝ) ^ (s + 1) *
        (C * (circleFlowReferenceSize G hG hperiod c s a t +
          circleFlowReferenceSize G hG hperiod c 3 a t * (F * J))) :=
      mul_le_mul_of_nonneg_left hmono' (by positivity)
    _ ≤ (2 : ℝ) ^ (s + 1) * (C * (J + J₃ * (F * J))) :=
      mul_le_mul_of_nonneg_left hpartial (by positivity)
    _ = ((2 : ℝ) ^ (s + 1) * C * (1 + F * J₃)) * J := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (le_max_right 1 ((2 : ℝ) ^ (s + 1) * C * (1 + F * J₃))) hJ

end ContinuousFlexibility.Analysis
