module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Inverse
public import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# First derivatives of inverse circle lifts

A positive lower bound for the actual derivative gives a lower bound for
all increments by the scalar mean value theorem.  A right inverse is
therefore Lipschitz, which supplies its continuity before the inverse
derivative theorem is applied.  No continuity or differentiability of the
inverse is assumed, and no higher-order inverse theorem is used.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology

/-- A positive derivative lower bound controls the distance between
images of any two points.  Differentiability follows from positivity of
the actual derivative. -/
theorem mul_abs_sub_le_abs_image_sub_of_deriv_lower_bound
    {F : ℝ → ℝ} {A : ℝ} (hA : 0 < A)
    (hF : ∀ x : ℝ, A ≤ deriv F x) (x y : ℝ) :
    A * |x - y| ≤ |F x - F y| := by
  have hd : Differentiable ℝ F := fun t =>
    differentiableAt_of_deriv_ne_zero (hA.trans_le (hF t)).ne'
  rcases le_total x y with hxy | hyx
  · calc
      A * |x - y| = A * (y - x) := by
        rw [abs_sub_comm x y, abs_of_nonneg (sub_nonneg.mpr hxy)]
      _ ≤ F y - F x := mul_sub_le_image_sub_of_le_deriv hd hF hxy
      _ ≤ |F y - F x| := le_abs_self _
      _ = |F x - F y| := abs_sub_comm _ _
  · calc
      A * |x - y| = A * (x - y) := by
        rw [abs_of_nonneg (sub_nonneg.mpr hyx)]
      _ ≤ F x - F y := mul_sub_le_image_sub_of_le_deriv hd hF hyx
      _ ≤ |F x - F y| := le_abs_self _

/-- The distance bound for the inverse uses only the right inverse identity. -/
theorem abs_inverse_sub_le_of_deriv_lower_bound
    {F G : ℝ → ℝ} {A : ℝ} (hA : 0 < A)
    (hF : ∀ x : ℝ, A ≤ deriv F x) (hFG : ∀ y : ℝ, F (G y) = y)
    (x y : ℝ) :
    |G x - G y| ≤ A⁻¹ * |x - y| := by
  have h := mul_abs_sub_le_abs_image_sub_of_deriv_lower_bound hA hF (G x) (G y)
  rw [hFG x, hFG y] at h
  calc
    |G x - G y| ≤ |x - y| / A := by
      apply (le_div_iff₀ hA).2
      simpa only [mul_comm] using h
    _ = A⁻¹ * |x - y| := by rw [div_eq_mul_inv, mul_comm]

/-- A right inverse has Lipschitz constant the reciprocal of the positive
forward derivative lower bound. -/
theorem lipschitzWith_inverse_of_deriv_lower_bound
    {F G : ℝ → ℝ} {A : ℝ} (hA : 0 < A)
    (hF : ∀ x : ℝ, A ≤ deriv F x) (hFG : ∀ y : ℝ, F (G y) = y) :
    LipschitzWith (NNReal.mk A⁻¹ (inv_nonneg.mpr hA.le)) G := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [Real.dist_eq, NNReal.coe_mk] using
    abs_inverse_sub_le_of_deriv_lower_bound hA hF hFG x y

theorem continuous_inverse_of_deriv_lower_bound
    {F G : ℝ → ℝ} {A : ℝ} (hA : 0 < A)
    (hF : ∀ x : ℝ, A ≤ deriv F x) (hFG : ∀ y : ℝ, F (G y) = y) :
    Continuous G :=
  (lipschitzWith_inverse_of_deriv_lower_bound hA hF hFG).continuous

/-- The inverse derivative is obtained after proving inverse continuity
from the forward increment bound. -/
theorem hasDerivAt_inverse_of_deriv_lower_bound
    {F G : ℝ → ℝ} {A : ℝ} (hA : 0 < A)
    (hF : ∀ x : ℝ, A ≤ deriv F x) (hFG : ∀ y : ℝ, F (G y) = y)
    (y : ℝ) :
    HasDerivAt G (deriv F (G y))⁻¹ y := by
  have hpos : 0 < deriv F (G y) := hA.trans_le (hF (G y))
  exact HasDerivAt.of_local_left_inverse
    (continuous_inverse_of_deriv_lower_bound hA hF hFG).continuousAt
    (differentiableAt_of_deriv_ne_zero hpos.ne').hasDerivAt hpos.ne'
    (Filter.Eventually.of_forall hFG)

theorem deriv_inverse_eq_one_div
    {F G : ℝ → ℝ} {A : ℝ} (hA : 0 < A)
    (hF : ∀ x : ℝ, A ≤ deriv F x) (hFG : ∀ y : ℝ, F (G y) = y)
    (y : ℝ) :
    deriv G y = 1 / deriv F (G y) := by
  simpa only [one_div] using
    (hasDerivAt_inverse_of_deriv_lower_bound hA hF hFG y).deriv

/-- The inverse derivative lies between the reciprocals of the forward
bounds.  Positivity of the upper bound already follows from the hypotheses. -/
theorem inverse_deriv_bounds
    {F G : ℝ → ℝ} {A B : ℝ} (hA : 0 < A)
    (hF : ∀ x : ℝ, A ≤ deriv F x ∧ deriv F x ≤ B)
    (hFG : ∀ y : ℝ, F (G y) = y) (y : ℝ) :
    1 / B ≤ deriv G y ∧ deriv G y ≤ 1 / A := by
  rw [deriv_inverse_eq_one_div hA (fun x => (hF x).1) hFG y]
  exact ⟨one_div_le_one_div_of_le (hA.trans_le (hF (G y)).1) (hF (G y)).2,
    one_div_le_one_div_of_le hA (hF (G y)).1⟩

end ContinuousFlexibility.Analysis
