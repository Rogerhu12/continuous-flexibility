import ContinuousFlexibility.Analysis.RootTravelDifferential
import ContinuousFlexibility.Analysis.AiryHalfHolonomy

/-!
# The actual root chart determined by its two first integrals

The Airy travel power is invertible on the nonnegative canonical radial
axis. Thus the two characteristic values determine the entire root
chart. Reflection obtains the second value from the same signed inverse
sample; the Boolean formula retains the right-root travel offset.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements

theorem rootTravelPower_airyTravelPrimitive {ξ : ℝ} (hξ : 0 ≤ ξ) :
    rootTravelPower (airyTravelPrimitive ξ) = ξ := by
  unfold rootTravelPower airyTravelPrimitive
  rw [show (3 / 2 : ℝ) * ((2 / 3 : ℝ) * ξ ^ (3 / 2 : ℝ)) =
      ξ ^ (3 / 2 : ℝ) by ring,
    ← Real.rpow_mul hξ,
    show (3 / 2 : ℝ) * (2 / 3 : ℝ) = 1 by norm_num, Real.rpow_one]

theorem extendedRootEvenOddChart_eq_of_travel_values
    {G : ℝ × ℝ × ℝ → ℝ} {p q : PolarPoint}
    (hp : 0 < p.1) (hq : 0 ≤ q.1)
    (htravel : characteristicTravelChart (rootCharacteristicCoordinate G 1)
      (rootCharacteristicCoordinate G (-1)) p = (airyTravelPrimitive q.1, q.2)) :
    extendedRootEvenOddChart G p = q := by
  have ht := congrArg Prod.fst
    (characteristicTravelChart_rootCharacteristicCoordinate G hp)
  have hqv := congrArg Prod.fst htravel
  dsimp only at ht hqv
  have hpow : 0 < p.1 ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hp _
  have hnonneg : 0 ≤ airyTravelPrimitive q.1 :=
    mul_nonneg (by norm_num : (0 : ℝ) ≤ 2 / 3) (Real.rpow_nonneg hq _)
  have hχ : 0 ≤ rootOddCoefficient G p := by
    nlinarith only [ht, hqv, hpow, hnonneg]
  rw [extendedRootEvenOddChart_eq_rootTravelPower G hp hχ, htravel,
    rootTravelPower_airyTravelPrimitive hq]

/-- One signed sample and its reflected angle determine both chart
coordinates. The same positive root scale is used on the two ends. -/
theorem extendedRootEvenOddChart_eq_of_reflected_footpoints
    {G : ℝ × ℝ × ℝ → ℝ} {p q : PolarPoint} {V U T : ℝ}
    (rightEnd : Bool) (hp : 0 < p.1) (hq : 0 ≤ q.1)
    (hreflect : ∀ x ζ θ, G (x, -ζ, -θ) = -G (x, ζ, θ))
    (hV : G (p.1, (if rightEnd then (1 : ℝ) else -1) * p.1 ^ (3 / 2 : ℝ), p.2) =
      V - if rightEnd then T else 0)
    (hU : G (p.1, (if rightEnd then (1 : ℝ) else -1) * p.1 ^ (3 / 2 : ℝ), -p.2) =
      -U - if rightEnd then T else 0)
    (hangle : q.2 = (V + U) / 2)
    (htravel : airyTravelPrimitive q.1 =
      if rightEnd then T - (V - U) / 2 else (V - U) / 2) :
    extendedRootEvenOddChart G p = q := by
  apply extendedRootEvenOddChart_eq_of_travel_values hp hq
  cases rightEnd with
  | false =>
      simp only [Bool.false_eq_true, ite_false, neg_one_mul, sub_zero] at hV hU htravel
      have hr : G (p.1, p.1 ^ (3 / 2 : ℝ), p.2) =
          -G (p.1, -(p.1 ^ (3 / 2 : ℝ)), -p.2) := by
        simpa only [neg_neg] using hreflect p.1 (-(p.1 ^ (3 / 2 : ℝ))) (-p.2)
      apply Prod.ext
      · simp only [characteristicTravelChart, rootCharacteristicCoordinate, one_mul, neg_one_mul]
        rw [hr, hV, hU]
        linarith only [htravel]
      · simp only [characteristicTravelChart, rootCharacteristicCoordinate, one_mul, neg_one_mul]
        rw [hr, hV, hU]
        linarith only [hangle]
  | true =>
      simp only [ite_true, one_mul] at hV hU htravel
      have hr : G (p.1, -(p.1 ^ (3 / 2 : ℝ)), p.2) =
          -G (p.1, p.1 ^ (3 / 2 : ℝ), -p.2) := by
        simpa only [neg_neg] using hreflect p.1 (p.1 ^ (3 / 2 : ℝ)) (-p.2)
      apply Prod.ext
      · simp only [characteristicTravelChart, rootCharacteristicCoordinate, one_mul, neg_one_mul]
        rw [hr, hV, hU]
        linarith only [htravel]
      · simp only [characteristicTravelChart, rootCharacteristicCoordinate, one_mul, neg_one_mul]
        rw [hr, hV, hU]
        linarith only [hangle]

end ContinuousFlexibility.Analysis
