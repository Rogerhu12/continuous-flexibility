import ContinuousFlexibility.Analysis.CanonicalJetProductClosure
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Algebra.BigOperators.Fin

/-!
# Products of actual ordinary jets at one point

The binomial norm inequality only needs finite smoothness near the
evaluation point. Numerical interpolation then gives a common fixed
loss for the product of two actual fields. This local form applies at
root boundaries where the constructed formulas are smooth at the point
but need not be globally smooth on the whole plane.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

/-- The ordinary binomial derivative bound is local. For each finite
order, take a common open neighborhood of that order and use the public
within-derivative inequality there. -/
theorem norm_iteratedFDeriv_mul_le_at
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {f g : X → ℝ} {x : X}
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun y => f y * g y) x‖ ≤
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (n - i) g x‖ := by
  obtain ⟨U, hU, hxU, hfU⟩ := hf.contDiffOn' (m := (n : ℕ∞ω)) (by simp) (by simp)
  obtain ⟨V, hV, hxV, hgV⟩ := hg.contDiffOn' (m := (n : ℕ∞ω)) (by simp) (by simp)
  have hf' : ContDiffOn ℝ n f U := by simpa using hfU
  have hg' : ContDiffOn ℝ n g V := by simpa using hgV
  have hUV := hU.inter hV
  have hx : x ∈ U ∩ V := ⟨hxU, hxV⟩
  have hfjet (j : ℕ) : iteratedFDerivWithin ℝ j f (U ∩ V) x = iteratedFDeriv ℝ j f x :=
    iteratedFDerivWithin_eq_iteratedFDeriv hUV.uniqueDiffOn (hf.of_le (by simp)) hx
  have hgjet (j : ℕ) : iteratedFDerivWithin ℝ j g (U ∩ V) x = iteratedFDeriv ℝ j g x :=
    iteratedFDerivWithin_eq_iteratedFDeriv hUV.uniqueDiffOn (hg.of_le (by simp)) hx
  have hprod : iteratedFDerivWithin ℝ n (fun y => f y * g y) (U ∩ V) x =
      iteratedFDeriv ℝ n (fun y => f y * g y) x :=
    iteratedFDerivWithin_eq_iteratedFDeriv hUV.uniqueDiffOn
      ((hf.mul hg).of_le (by simp)) hx
  simpa only [hfjet, hgjet, hprod] using
    norm_iteratedFDerivWithin_mul_le (hf'.mono inter_subset_left)
      (hg'.mono inter_subset_right) hUV.uniqueDiffOn hx le_rfl

theorem pointwiseProduct_fixed_loss_material_bound
    {E : Type} [AddCommGroup E] [Module ℝ E]
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p) (hI : HasInterpolation p)
    (inputLoss : ℕ) :
    ∃ base loss : ℕ, ∀ A : ℕ → ℝ, (∀ n, 0 < A n) →
      ∃ B : ℕ → ℝ, (∀ n, 0 < B n) ∧
      ∀ z : E, p base z ≤ 1 → ∀ f g : X → ℝ, ∀ x : X,
      ContDiffAt ℝ ∞ f x → ContDiffAt ℝ ∞ g x →
      (∀ n : ℕ, ‖iteratedFDeriv ℝ n f x‖ ≤ A n * (1 + p (n + inputLoss) z)) →
      (∀ n : ℕ, ‖iteratedFDeriv ℝ n g x‖ ≤ A n * (1 + p (n + inputLoss) z)) →
      ∀ n : ℕ, ‖iteratedFDeriv ℝ n (fun y => f y * g y) x‖ ≤
        B n * (1 + p (n + loss) z) := by
  obtain ⟨base, loss, hproducts⟩ := coordinate_jet_product_le_one_high_of_low hp hI inputLoss
  have hpair (n : ℕ) (i : Fin (n + 1)) :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ z : E, p base z ≤ 1 →
        (1 + p ((i : ℕ) + inputLoss) z) * (1 + p (n - i + inputLoss) z) ≤
          C * (1 + p (n + loss) z) := by
    have hi : (i : ℕ) ≤ n := Nat.le_of_lt_succ i.isLt
    have hdegree : (∑ j : Fin 2, (![i, n - i] : Fin 2 → ℕ) j) ≤ n := by
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      omega
    obtain ⟨C, hC, hb⟩ := hproducts (![i, n - i] : Fin 2 → ℕ) n hdegree
    refine ⟨C, hC, ?_⟩
    intro z hz
    simpa only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] using hb z hz
  choose C hC hpair using hpair
  refine ⟨base, loss, ?_⟩
  intro A hA
  let K (n : ℕ) (i : Fin (n + 1)) : ℝ := (n.choose i : ℝ) * A i * A (n - i) * C n i
  have hK (n : ℕ) (i : Fin (n + 1)) : 0 ≤ K n i :=
    mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hA i).le)
      (hA (n - i)).le) (hC n i)
  let B : ℕ → ℝ := fun n => 1 + ∑ i : Fin (n + 1), K n i
  have hB (n : ℕ) : 0 < B n :=
    add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg (fun i _ => hK n i))
  refine ⟨B, hB, ?_⟩
  intro z hz f g x hf hg hfj hgj n
  have hn : 0 ≤ 1 + p (n + loss) z := add_nonneg zero_le_one (apply_nonneg _ _)
  have hstart := norm_iteratedFDeriv_mul_le_at hf hg n
  rw [Finset.sum_range] at hstart
  apply hstart.trans
  calc
    _ ≤ ∑ i : Fin (n + 1), K n i * (1 + p (n + loss) z) := by
      apply Finset.sum_le_sum
      intro i _
      have hc : 0 ≤ (n.choose (i : ℕ) : ℝ) := Nat.cast_nonneg _
      have hcoeff : 0 ≤ (n.choose (i : ℕ) : ℝ) * A i * A (n - i) :=
        mul_nonneg (mul_nonneg hc (hA i).le) (hA (n - i)).le
      calc
        _ ≤ (n.choose (i : ℕ) : ℝ) *
            (A i * (1 + p ((i : ℕ) + inputLoss) z)) *
            (A (n - i) * (1 + p (n - i + inputLoss) z)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hfj i) hc) (hgj (n - i))
            (norm_nonneg _) (mul_nonneg hc
              (mul_nonneg (hA i).le (add_nonneg zero_le_one (apply_nonneg _ _))))
        _ = ((n.choose (i : ℕ) : ℝ) * A i * A (n - i)) *
            ((1 + p ((i : ℕ) + inputLoss) z) * (1 + p (n - i + inputLoss) z)) := by ring
        _ ≤ ((n.choose (i : ℕ) : ℝ) * A i * A (n - i)) *
            (C n i * (1 + p (n + loss) z)) :=
          mul_le_mul_of_nonneg_left (hpair n i z hz) hcoeff
        _ = K n i * (1 + p (n + loss) z) := by dsimp only [K]; ring
    _ = (∑ i : Fin (n + 1), K n i) * (1 + p (n + loss) z) := by rw [Finset.sum_mul]
    _ ≤ B n * (1 + p (n + loss) z) :=
      mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) hn

end ContinuousFlexibility.Analysis
