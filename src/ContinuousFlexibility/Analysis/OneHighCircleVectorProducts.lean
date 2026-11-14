module

public import ContinuousFlexibility.Analysis.OneHighCircleComponents
public import ContinuousFlexibility.Analysis.OneHighCompositionJets

/-!
# One-high-factor products of actual vector derivative norms

A finite expansion over component choices converts the vector norm products
in the genuine Faà di Bruno formula to the already proved scalar derivative
products. The resulting constant is explicit in the number of components.
-/

@[expose] public section

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
  let Q (sel : Fin k → Fin m) : C(AddCircle P, ℝ) :=
    ∏ j, circleComponent (f (a j)) (sel j)
  let W : C(AddCircle P, ℝ) := ∏ j, circleNormMap (f (a j))
  have hW : (∏ j : Fin k, (circleNormMap (f (a j)) : AddCircle P → ℝ)) =
      (W : AddCircle P → ℝ) := by
    funext θ
    simp only [W, Finset.prod_apply, ContinuousMap.prod_apply]
  have hpoint (θ : AddCircle P) :
      ‖W θ‖ ≤ ∑ sel : Fin k → Fin m, 1 * ‖Q sel θ‖ := by
    have hl : 0 ≤ W θ := by
      simp only [W, ContinuousMap.prod_apply, circleNormMap_apply]
      exact Finset.prod_nonneg fun _ _ => norm_nonneg _
    rw [Real.norm_of_nonneg hl]
    simp only [W, Q, one_mul, ContinuousMap.prod_apply, circleNormMap_apply,
      circleComponent_apply, norm_prod]
    calc
      _ ≤ ∏ j, ∑ i : Fin m, ‖f (a j) θ i‖ :=
        Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
          (fun j _ => norm_pi_le_sum_norm (f (a j) θ))
      _ = _ := Fintype.prod_sum (fun (j : Fin k) (i : Fin m) => ‖f (a j) θ i‖)
  have hterm (sel : Fin k → Fin m) :
      (eLpNorm (Q sel) 2 AddCircle.haarAddCircle).toReal ≤
        (k : ℝ) * R ^ (k - 1) *
          ∑ i, circleRealSobolevNorm (s : ℝ) (circleComponent (f 0) i) := by
    have h := circle_real_selected_derivative_product_le
      (fun i n => circleComponent (f n) i)
      (fun i => circleComponent_hasDerivAt f hderiv i) hk sel a ha hR0 hR
    have he : (∏ j : Fin k, (circleComponent (f (a j)) (sel j) : AddCircle P → ℝ)) =
        (Q sel : AddCircle P → ℝ) := by
      funext θ
      simp only [Q, Finset.prod_apply, ContinuousMap.prod_apply]
    rw [he] at h
    exact h
  have hD := oneHigh_l2_finite_domination
    (μ := AddCircle.haarAddCircle) (g := (W : AddCircle P → ℝ))
    W.continuous.aestronglyMeasurable
    (fun sel : Fin k → Fin m => (Q sel : AddCircle P → ℝ))
    (fun sel => ContinuousMap.memLp (p := 2) (μ := AddCircle.haarAddCircle) ℝ (Q sel))
    (fun _ => (1 : ℝ)) (fun _ => zero_le_one) (Filter.Eventually.of_forall hpoint)
  have hout : (eLpNorm W 2 AddCircle.haarAddCircle).toReal ≤
      (m : ℝ) ^ k * (k : ℝ) * R ^ (k - 1) *
        ∑ i, circleRealSobolevNorm (s : ℝ) (circleComponent (f 0) i) := by
    apply hD.2.trans
    calc
      _ ≤ ∑ _sel : Fin k → Fin m, (k : ℝ) * R ^ (k - 1) *
          ∑ i, circleRealSobolevNorm (s : ℝ) (circleComponent (f 0) i) := by
        apply Finset.sum_le_sum
        intro sel _
        simpa only [one_mul] using hterm sel
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
          Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow]
        ring
  simpa only [hW] using hout

def circleVectorCompositionCoefficient (m s : ℕ) (R : ℝ) (B : ℕ → ℝ) : ℝ :=
  ∑ c : OrderedFinpartition s,
    B c.length * (m : ℝ) ^ c.length * (c.length : ℝ) * R ^ (c.length - 1)

end ContinuousFlexibility.Analysis
