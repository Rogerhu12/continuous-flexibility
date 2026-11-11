import ContinuousFlexibility.Analysis.N08OpticalSquareRoot
import ContinuousFlexibility.Statements.Nonlinear
import ContinuousFlexibility.Analysis.TameElementaryCalculus
import ContinuousFlexibility.Scalar.WeightedProductTower
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Differences of the same genuine first jet

The second member of a directional tower differentiates its first member.
After a continuous scalar observation, the ordinary mean-value estimate
therefore controls first-jet differences along a segment. This retains the
original tower and makes no separate smooth-family assumption.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped Topology BigOperators

section Difference

variable {E F : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
  {U : Set E} {f : E → F}

theorem n08_firstJet_coordinate_difference_bound
    (J : SmoothDirections U f) (L : F →L[ℝ] ℝ)
    {x y v : E} {B : ℝ}
    (hsegment : ∀ t ∈ Icc (0 : ℝ) 1, x + t • (y - x) ∈ U)
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1,
      |L (J.D 2 (x + t • (y - x))
        (Fin.cons (y - x) (Fin.cons v Fin.elim0)))| ≤ B) :
    |L (J.D 1 y (Fin.cons v Fin.elim0)) -
      L (J.D 1 x (Fin.cons v Fin.elim0))| ≤ B := by
  let g (t : ℝ) : ℝ := L (J.D 1 (x + t • (y - x)) (Fin.cons v Fin.elim0))
  let g' (t : ℝ) : ℝ := L (J.D 2 (x + t • (y - x))
    (Fin.cons (y - x) (Fin.cons v Fin.elim0)))
  have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : HasDerivAt g (g' t) t :=
    n08_hasDerivAt_affine_parameter
      ((J.derivative 1 _ (hsegment t ht) (Fin.cons v Fin.elim0) (y - x)).clm_comp L)
  have hb (t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1) : ‖g' t‖ ≤ B := by
    simpa only [g', Real.norm_eq_abs] using hbound t (Ico_subset_Icc_self ht)
  have h := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun t ht => (hd t ht).hasDerivWithinAt) hb
  have hend : x + (y - x) = y := by abel
  simpa only [g, one_smul, zero_smul, add_zero, hend, Real.norm_eq_abs] using h

end Difference

/-- A fixed second-order tame expression reduces to a product of two
stronger input seminorms on a bounded stronger-seminorm ball. -/
theorem n08_oneHigh_two_le
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (hp : Monotone p)
    {base high n : ℕ} (hb : base ≤ n) (hh : high ≤ n)
    (x d v : E) (hx : p n x ≤ 1) :
    oneHighVariationWeight p base high x (Fin.cons d (Fin.cons v Fin.elim0)) ≤
      4 * p n d * p n v := by
  have hprod : p base d * p base v ≤ p n d * p n v :=
    mul_le_mul (hp hb d) (hp hb v) (apply_nonneg _ _) (apply_nonneg _ _)
  have hfirst : (1 + p high x) * (p base d * p base v) ≤
      2 * (p n d * p n v) :=
    mul_le_mul (by linarith [hp hh x]) hprod
      (mul_nonneg (apply_nonneg _ _) (apply_nonneg _ _)) (by norm_num)
  have hsecond : p high d * p base v ≤ p n d * p n v :=
    mul_le_mul (hp hh d) (hp hb v) (apply_nonneg _ _) (apply_nonneg _ _)
  have hthird : p base d * p high v ≤ p n d * p n v :=
    mul_le_mul (hp hb d) (hp hh v) (apply_nonneg _ _) (apply_nonneg _ _)
  have hv : (Fin.cons d (Fin.cons v Fin.elim0) : Fin 2 → E) = ![d, v] := by
    funext i
    fin_cases i <;> rfl
  rw [hv, oneHighVariationWeight, oneHigh_fin_two, Fin.prod_univ_two]
  change (1 + p high x) * (p base d * p base v) +
    (p high d * p base v + p base d * p high v) ≤ 4 * p n d * p n v
  linarith only [hfirst, hsecond, hthird]

theorem n08_seminorm_segment_lt
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : Seminorm ℝ E) {x y : E} {r t : ℝ}
    (hx : p x < r) (hy : p y < r) (ht : t ∈ Icc (0 : ℝ) 1) :
    p (x + t • (y - x)) < r := by
  exact p.mem_ball_zero.mp ((p.convex_ball 0 r).add_smul_sub_mem
    (p.mem_ball_zero.mpr hx) (p.mem_ball_zero.mpr hy) ht)

/-- A verified second-jet tame estimate gives a local first-jet difference
bound for every continuous scalar observation controlled by the target
seminorm. All parameters are fixed before the observation or direction. -/
theorem n08_firstJet_tame_difference_bound
    {E F : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    {U : Set E} {f : E → F} (J : SmoothDirections U f)
    (p : ℕ → Seminorm ℝ E) (hp : Monotone p) (q : Seminorm ℝ F)
    {base high : ℕ} {ε K : ℝ} (hK : 0 ≤ K)
    (hjet : ∀ z ∈ U, p base z < ε → ∀ d v : E,
      q (J.D 2 z (Fin.cons d (Fin.cons v Fin.elim0))) ≤
        K * oneHighVariationWeight p base high z (Fin.cons d (Fin.cons v Fin.elim0)))
    (L : F →L[ℝ] ℝ) {A : ℝ} (hA : 0 ≤ A)
    (hL : ∀ u, |L u| ≤ A * q u)
    {x y v : E}
    (hx : p (max base high) x < min ε 1)
    (hy : p (max base high) y < min ε 1)
    (hsegment : ∀ t ∈ Icc (0 : ℝ) 1, x + t • (y - x) ∈ U) :
    |L (J.D 1 y (Fin.cons v Fin.elim0)) - L (J.D 1 x (Fin.cons v Fin.elim0))| ≤
      A * (4 * K) * p (max base high) (y - x) * p (max base high) v := by
  apply n08_firstJet_coordinate_difference_bound J L hsegment
  intro t ht
  let z := x + t • (y - x)
  have hsmall : p (max base high) z < min ε 1 :=
    n08_seminorm_segment_lt (p (max base high)) hx hy ht
  have hnear : p base z < ε :=
    (hp (le_max_left base high) z).trans_lt (hsmall.trans_le (min_le_left _ _))
  have hbounded : p (max base high) z ≤ 1 :=
    hsmall.le.trans (min_le_right _ _)
  have h := hjet z (hsegment t ht) hnear (y - x) v
  have htwo := n08_oneHigh_two_le p hp (le_max_left base high) (le_max_right base high)
    z (y - x) v hbounded
  calc
    _ ≤ A * q (J.D 2 z (Fin.cons (y - x) (Fin.cons v Fin.elim0))) := hL _
    _ ≤ A * (K * oneHighVariationWeight p base high z
        (Fin.cons (y - x) (Fin.cons v Fin.elim0))) := mul_le_mul_of_nonneg_left h hA
    _ ≤ A * (K * (4 * p (max base high) (y - x) * p (max base high) v)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left htwo hK) hA
    _ = _ := by ring

end ContinuousFlexibility.Analysis
