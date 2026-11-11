import ContinuousFlexibility.Analysis.JointMixedDiagonalCalculus
import ContinuousFlexibility.Analysis.N01CoefficientMixedBounds

/-!
# Actual mixed jets of a parameter-independent radial cutoff

Along a pure parameter line the radial scalar is constant. The supplied
genuine tower therefore has no positive pure-parameter jets. Angular
derivatives also vanish, leaving exactly the ordinary radial derivative.
This gives the degree-zero cutoff factors in the transport recurrence.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {U : Set E} {V : Set PolarPoint}

theorem jointMixedDiagonal_radial_field
    {g : ℝ → ℝ}
    (J : SmoothDirections (U ×ˢ V) (fun z : E × PolarPoint => g z.2.1))
    (hU : IsOpen U) (hV : IsOpen V) (hc : Convex ℝ (U ×ˢ V))
    (n a b : ℕ) (x w : E) (hx : x ∈ U) {p : PolarPoint} (hp : p ∈ V) :
    jointMixedDiagonal J n a b x w p =
      if n = 0 ∧ b = 0 then iteratedDeriv a g p.1 else 0 := by
  have hz : x + (0 : ℝ) • w ∈ U := by simpa only [zero_smul, add_zero] using hx
  have heq : jointMixedDiagonal J n a b x w p =
      iteratedDeriv n (fun _ : ℝ =>
        mixedDerivative a b (fun q : PolarPoint => g q.1) p) 0 := by
    simpa only [zero_smul, add_zero] using
      (jointMixedDiagonal_eq_iteratedDeriv J hU hV hc n a b x w hz hp).symm
  rw [heq, iteratedDeriv_const, mixedDerivative_radial_field]
  by_cases hn : n = 0 <;> by_cases hb : b = 0 <;> simp [hn, hb]

/-- The actual derivative of the selected cutoff is the coefficient
appearing in the correction velocity. Its radial order is `a + 1`. -/
theorem jointMixedDiagonal_radial_deriv
    {χ : ℝ → ℝ}
    (J : SmoothDirections (U ×ˢ V) (fun z : E × PolarPoint => deriv χ z.2.1))
    (hU : IsOpen U) (hV : IsOpen V) (hc : Convex ℝ (U ×ˢ V))
    (n a b : ℕ) (x w : E) (hx : x ∈ U) {p : PolarPoint} (hp : p ∈ V) :
    jointMixedDiagonal J n a b x w p =
      if n = 0 ∧ b = 0 then iteratedDeriv (a + 1) χ p.1 else 0 := by
  rw [jointMixedDiagonal_radial_field J hU hV hc n a b x w hx hp,
    ← iteratedDeriv_succ']

/-- A cutoff power bound is inherited without any high parameter factor
or spatial-degree charge. -/
theorem jointMixedDiagonal_radial_deriv_abs_le
    {χ : ℝ → ℝ}
    (J : SmoothDirections (U ×ˢ V) (fun z : E × PolarPoint => deriv χ z.2.1))
    (hU : IsOpen U) (hV : IsOpen V) (hc : Convex ℝ (U ×ˢ V))
    (n a b : ℕ) (x w : E) (hx : x ∈ U) {p : PolarPoint} (hp : p ∈ V)
    {K W P : ℝ} (hK : 0 ≤ K) (hW : 0 ≤ W)
    (hbound : |iteratedDeriv (a + 1) χ p.1| ≤ K * W ^ P) :
    |jointMixedDiagonal J n a b x w p| ≤ K * W ^ P := by
  rw [jointMixedDiagonal_radial_deriv J hU hV hc n a b x w hx hp]
  split_ifs
  · exact hbound
  · simpa only [abs_zero] using mul_nonneg hK (Real.rpow_nonneg hW P)

end ContinuousFlexibility.Analysis
