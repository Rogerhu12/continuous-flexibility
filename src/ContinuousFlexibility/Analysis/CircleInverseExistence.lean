module

public import ContinuousFlexibility.Analysis.CircleInverseDerivativeBounds
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Logic.Function.Basic
public import Mathlib.Tactic.Linarith

/-!
# Global inverse existence from a positive derivative lower bound

The scalar mean value theorem bounds the image above and below every
prescribed real value.  The intermediate value theorem then gives
surjectivity; strict monotonicity gives injectivity.  The actual chosen
inverse is Lipschitz and has the reciprocal derivative, by the preceding
inverse derivative module.  No periodicity or inverse candidate is assumed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

/-- A uniformly positive actual derivative forces the image to cross every
real value.  The bracketing points are explicit, and continuity follows
from positivity of the derivative. -/
theorem surjective_of_deriv_lower_bound
    {F : ℝ → ℝ} {A : ℝ} (hA : 0 < A)
    (hF : ∀ x : ℝ, A ≤ deriv F x) :
    Function.Surjective F := by
  have hd : Differentiable ℝ F := fun t =>
    differentiableAt_of_deriv_ne_zero (hA.trans_le (hF t)).ne'
  intro y
  let q : ℝ := (y - F 0) / A
  refine mem_range_of_exists_le_of_exists_ge hd.continuous ?_ ?_
  · refine ⟨min 0 q, ?_⟩
    have hstep := mul_sub_le_image_sub_of_le_deriv hd hF (min_le_left 0 q)
    have hmin : min 0 q ≤ (y - F 0) / A := min_le_right 0 q
    have hdiv := (le_div_iff₀ hA).mp hmin
    linarith
  · refine ⟨max 0 q, ?_⟩
    have hstep := mul_sub_le_image_sub_of_le_deriv hd hF (le_max_left 0 q)
    have hmax : (y - F 0) / A ≤ max 0 q := le_max_right 0 q
    have hdiv := (div_le_iff₀ hA).mp hmax
    linarith

/-- The positive lower bound gives a genuine global bijection, without a
periodicity hypothesis. -/
theorem bijective_of_deriv_lower_bound
    {F : ℝ → ℝ} {A : ℝ} (hA : 0 < A)
    (hF : ∀ x : ℝ, A ≤ deriv F x) :
    Function.Bijective F :=
  ⟨(strictMono_of_deriv_pos (fun x => hA.trans_le (hF x))).injective,
    surjective_of_deriv_lower_bound hA hF⟩

/-- The chosen inverse is an actual right inverse on the whole real line. -/
theorem rightInverse_invFun_of_deriv_lower_bound
    {F : ℝ → ℝ} {A : ℝ} (hA : 0 < A)
    (hF : ∀ x : ℝ, A ≤ deriv F x) :
    Function.RightInverse (Function.invFun F) F :=
  Function.rightInverse_invFun (surjective_of_deriv_lower_bound hA hF)

/-- The same chosen inverse is also a left inverse. -/
theorem leftInverse_invFun_of_deriv_lower_bound
    {F : ℝ → ℝ} {A : ℝ} (hA : 0 < A)
    (hF : ∀ x : ℝ, A ≤ deriv F x) :
    Function.LeftInverse (Function.invFun F) F :=
  Function.leftInverse_invFun (bijective_of_deriv_lower_bound hA hF).1

theorem continuous_invFun_of_deriv_lower_bound
    {F : ℝ → ℝ} {A : ℝ} (hA : 0 < A)
    (hF : ∀ x : ℝ, A ≤ deriv F x) :
    Continuous (Function.invFun F) :=
  continuous_inverse_of_deriv_lower_bound hA hF
    (rightInverse_invFun_of_deriv_lower_bound hA hF)

/-- The actual chosen inverse has the expected first derivative. -/
theorem hasDerivAt_invFun_of_deriv_lower_bound
    {F : ℝ → ℝ} {A : ℝ} (hA : 0 < A)
    (hF : ∀ x : ℝ, A ≤ deriv F x) (y : ℝ) :
    HasDerivAt (Function.invFun F) (deriv F (Function.invFun F y))⁻¹ y :=
  hasDerivAt_inverse_of_deriv_lower_bound hA hF
    (rightInverse_invFun_of_deriv_lower_bound hA hF) y

/-- Quantitative derivative bounds for the chosen global inverse. -/
theorem invFun_deriv_bounds
    {F : ℝ → ℝ} {A B : ℝ} (hA : 0 < A)
    (hF : ∀ x : ℝ, A ≤ deriv F x ∧ deriv F x ≤ B) (y : ℝ) :
    1 / B ≤ deriv (Function.invFun F) y ∧ deriv (Function.invFun F) y ≤ 1 / A :=
  inverse_deriv_bounds hA hF
    (rightInverse_invFun_of_deriv_lower_bound hA (fun x => (hF x).1)) y

end ContinuousFlexibility.Analysis
