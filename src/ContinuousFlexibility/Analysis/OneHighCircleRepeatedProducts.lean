import ContinuousFlexibility.Analysis.OneHighCircleRealSobolev
import ContinuousFlexibility.Analysis.OneHighCompositionJets

/-!
# Repeated inputs in the actual circle derivative-product estimate

The constants are explicit polynomials in a prescribed Fourier `L¹` bound.
In particular they are uniform over all inputs satisfying that bound, and
cannot contain an undisclosed high Sobolev norm.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory
open scoped ENNReal BigOperators

variable {P : ℝ} [Fact (0 < P)]

theorem circle_real_repeated_derivative_product_le
    (f : ℕ → C(AddCircle P, ℝ))
    (hderiv : ∀ k : ℕ, ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => f k (y : AddCircle P))
        (f (k + 1) (x : AddCircle P)) x)
    {m s : ℕ} (hm : 0 < m) (a : Fin m → ℕ) (ha : ∑ i, a i ≤ s)
    {R : ℝ} (hR : circleRealFourierL1Norm (f 0) ≤ R) :
    (eLpNorm (∏ i, f (a i)) 2 AddCircle.haarAddCircle).toReal ≤
      (m : ℝ) * R ^ (m - 1) * circleRealSobolevNorm (s : ℝ) (f 0) := by
  classical
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  have h := circle_real_derivative_product_oneHigh k s (fun _ => f)
    (fun _ => hderiv) a ha
  have hH : 0 ≤ circleRealSobolevNorm (s : ℝ) (f 0) := ENNReal.toReal_nonneg
  have hF : 0 ≤ circleRealFourierL1Norm (f 0) := ENNReal.toReal_nonneg
  have hp (j : Fin (k + 1)) :
      (∏ _i ∈ Finset.univ.erase j, circleRealFourierL1Norm (f 0)) ≤ R ^ k := by
    calc
      _ ≤ ∏ _i ∈ Finset.univ.erase j, R :=
        Finset.prod_le_prod₀ (fun _ _ => hF) (fun _ _ => hR)
      _ = R ^ k := by simp
  calc
    _ ≤ ∑ j : Fin (k + 1), circleRealSobolevNorm (s : ℝ) (f 0) *
        ∏ _i ∈ Finset.univ.erase j, circleRealFourierL1Norm (f 0) := h
    _ ≤ ∑ _j : Fin (k + 1), circleRealSobolevNorm (s : ℝ) (f 0) * R ^ k :=
      Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hp j) hH
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, Nat.succ_eq_add_one, Nat.add_sub_cancel]; ring

/-- The finite coefficient appearing in the positive-order composition
estimate. Its arguments are only the order, the low Fourier bound, and the
specified bounds for the outer derivatives. -/
def circleScalarCompositionCoefficient (s : ℕ) (R : ℝ) (B : ℕ → ℝ) : ℝ :=
  ∑ c : OrderedFinpartition s, B c.length * (c.length : ℝ) * R ^ (c.length - 1)

theorem circleScalarCompositionCoefficient_nonneg (s : ℕ) {R : ℝ} (hR : 0 ≤ R)
    {B : ℕ → ℝ} (hB : ∀ m, 0 ≤ B m) :
    0 ≤ circleScalarCompositionCoefficient s R B := by
  classical
  exact Finset.sum_nonneg fun c _ =>
    mul_nonneg (mul_nonneg (hB c.length) (Nat.cast_nonneg _)) (pow_nonneg hR _)

end ContinuousFlexibility.Analysis
