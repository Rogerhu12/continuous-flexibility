import ContinuousFlexibility.Analysis.OneHighCircleComponents
import ContinuousFlexibility.Analysis.OneHighCompositionJets

/-!
# One-high-factor products of actual vector derivative norms

A finite expansion over component choices converts the vector norm products
in the genuine Faà di Bruno formula to the already proved scalar derivative
products. The resulting constant is explicit in the number of components.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory
open scoped ENNReal BigOperators

variable {P : ℝ} [Fact (0 < P)] {m : ℕ}

theorem circle_vector_derivative_product_le
    (f : ℕ → C(AddCircle P, Fin m → ℝ))
    (hderiv : ∀ n : ℕ, ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => f n (y : AddCircle P))
        (f (n + 1) (x : AddCircle P)) x)
    {k s : ℕ} (hk : 0 < k) (a : Fin k → ℕ) (ha : ∑ j, a j ≤ s)
    {R : ℝ} (hR0 : 0 ≤ R)
    (hR : ∀ i, circleRealFourierL1Norm (circleComponent (f 0) i) ≤ R) :
    (eLpNorm (∏ j, circleNormMap (f (a j))) 2 AddCircle.haarAddCircle).toReal ≤
      (m : ℝ) ^ k * (k : ℝ) * R ^ (k - 1) *
        ∑ i, circleRealSobolevNorm (s : ℝ) (circleComponent (f 0) i) := by
  classical
  let N (sel : Fin k → Fin m) : C(AddCircle P, ℝ) :=
    circleNormMap (∏ j, circleComponent (f (a j)) (sel j))
  have hpoint (θ : AddCircle P) :
      ‖(∏ j, circleNormMap (f (a j))) θ‖ ≤ ‖(∑ sel, N sel) θ‖ := by
    have hl : 0 ≤ (∏ j, circleNormMap (f (a j))) θ := by
      simp only [ContinuousMap.prod_apply, circleNormMap_apply]
      exact Finset.prod_nonneg fun _ _ => norm_nonneg _
    have hr : 0 ≤ (∑ sel, N sel) θ := by
      simp only [ContinuousMap.sum_apply, N, circleNormMap_apply]
      exact Finset.sum_nonneg fun _ _ => norm_nonneg _
    rw [Real.norm_of_nonneg hl, Real.norm_of_nonneg hr]
    simp only [ContinuousMap.prod_apply, ContinuousMap.sum_apply, N, circleNormMap_apply,
      circleComponent_apply, norm_prod]
    calc
      _ ≤ ∏ j, ∑ i : Fin m, ‖f (a j) θ i‖ :=
        Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
          (fun j _ => norm_pi_le_sum_norm (f (a j) θ))
      _ = _ := Fintype.prod_sum (fun (j : Fin k) (i : Fin m) => ‖f (a j) θ i‖)
  have hterm (sel : Fin k → Fin m) :
      (eLpNorm (N sel) 2 AddCircle.haarAddCircle).toReal ≤
        (k : ℝ) * R ^ (k - 1) *
          ∑ i, circleRealSobolevNorm (s : ℝ) (circleComponent (f 0) i) := by
    rw [N, circle_l2_norm_map]
    exact circle_real_selected_derivative_product_le
      (fun i n => circleComponent (f n) i)
      (fun i => circleComponent_hasDerivAt f hderiv i) hk sel a ha hR0 hR
  calc
    _ ≤ (eLpNorm (∑ sel, N sel) 2 AddCircle.haarAddCircle).toReal :=
      circle_l2_le_of_norm_le (∏ j, circleNormMap (f (a j))) (∑ sel, N sel) hpoint
    _ ≤ ∑ sel, (eLpNorm (N sel) 2 AddCircle.haarAddCircle).toReal := circle_l2_sum_le N
    _ ≤ ∑ _sel : Fin k → Fin m, (k : ℝ) * R ^ (k - 1) *
        ∑ i, circleRealSobolevNorm (s : ℝ) (circleComponent (f 0) i) :=
      Finset.sum_le_sum fun sel _ => hterm sel
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
        Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow]
      ring

def circleVectorCompositionCoefficient (m s : ℕ) (R : ℝ) (B : ℕ → ℝ) : ℝ :=
  ∑ c : OrderedFinpartition s,
    B c.length * (m : ℝ) ^ c.length * (c.length : ℝ) * R ^ (c.length - 1)

end ContinuousFlexibility.Analysis
