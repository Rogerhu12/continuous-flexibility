import ContinuousFlexibility.Analysis.N01cDistributedRadialProducts
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Absorbing bounded exponent factors in genuine profile products

A finite range of radial orders has one common envelope exponent.  In the
actual Leibniz majorant, one parameter factor retains its full weight and
all remaining exponent factors use their uniform scalar bound.  This
applies to every positive parameter order and keeps the exact height
exponent; the number of factors changes only a numerical coefficient.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false

/-- Finitely many original envelope estimates admit common positive
constants and a common exponent when the envelope is at least one. -/
theorem finiteOrder_envelope_bound {X : Type*}
    (W E : X → ℝ) (hW : ∀ x, 0 ≤ W x) (hE : ∀ x, 1 ≤ E x)
    (F : ℕ → X → ℝ)
    (hF : ∀ j : ℕ, ∃ C A : ℝ, 0 < C ∧ 0 < A ∧
      ∀ x, F j x ≤ C * W x * E x ^ A) (n : ℕ) :
    ∃ C A : ℝ, 0 < C ∧ 0 < A ∧
      ∀ j : ℕ, j ≤ n → ∀ x, F j x ≤ C * W x * E x ^ A := by
  classical
  choose c a hc ha hbound using hF
  let C : ℝ := 1 + ∑ i : Fin (n + 1), c i.val
  let A : ℝ := 1 + ∑ i : Fin (n + 1), a i.val
  have hsumc : 0 ≤ ∑ i : Fin (n + 1), c i.val :=
    Finset.sum_nonneg (fun i _ => (hc i.val).le)
  have hsuma : 0 ≤ ∑ i : Fin (n + 1), a i.val :=
    Finset.sum_nonneg (fun i _ => (ha i.val).le)
  have hC : 0 < C := by dsimp only [C]; linarith
  have hA : 0 < A := by dsimp only [A]; linarith
  refine ⟨C, A, hC, hA, fun j hj x => ?_⟩
  let i : Fin (n + 1) := ⟨j, Nat.lt_succ_of_le hj⟩
  have hcj : c j ≤ C := by
    have hh : c i.val ≤ ∑ l : Fin (n + 1), c l.val :=
      Finset.single_le_sum (fun l _ => (hc l.val).le) (Finset.mem_univ i)
    dsimp only [i] at hh
    dsimp only [C]
    linarith
  have haj : a j ≤ A := by
    have hh : a i.val ≤ ∑ l : Fin (n + 1), a l.val :=
      Finset.single_le_sum (fun l _ => (ha l.val).le) (Finset.mem_univ i)
    dsimp only [i] at hh
    dsimp only [A]
    linarith
  exact (hbound j x).trans
    (mul_le_mul (mul_le_mul_of_nonneg_right hcj (hW x))
      (Real.rpow_le_rpow_of_exponent_le (hE x) haj)
      (Real.rpow_nonneg (zero_le_one.trans (hE x)) _)
      (mul_nonneg hC.le (hW x)))

theorem radialLeibnizOrders_le (k n : ℕ) (d : RadialLeibnizIndex k n)
    (i : Fin (k + 1)) : radialLeibnizOrders k n d i ≤ n :=
  (Finset.single_le_sum (fun j _ => Nat.zero_le (radialLeibnizOrders k n d j))
    (Finset.mem_univ i)).trans_eq (radialLeibnizOrders_sum k n d)

/-- A scalar upper bound for the original exponent jets bounds the
ordered-partition majorant at exactly those finite radial orders. -/
theorem exponentialJetProductMajorant_le_const
    (P : ℕ → ℝ) {R q : ℝ} (hP : ∀ j, 0 ≤ P j) (hq : 0 ≤ q)
    (n : ℕ) (hbound : ∀ j, j ≤ n → P j ≤ R) :
    exponentialJetProductMajorant P q n ≤
      exponentialJetProductMajorant (fun _ => R) q n :=
  Finset.sum_le_sum (fun c _ =>
    Finset.prod_le_prod₀ (fun i _ => mul_nonneg (hP _) hq)
      (fun i _ => mul_le_mul_of_nonneg_right (hbound _ (c.partSize_le i)) hq))

/-- The unweighted reference-profile envelope factors out of the finite
radial Leibniz majorant. -/
theorem scaledExponentialJetMajorant_le_const
    (W P : ℕ → ℝ) {B R q : ℝ}
    (hW : ∀ j, 0 ≤ W j) (hP : ∀ j, 0 ≤ P j)
    (hB : 0 ≤ B) (hq : 0 ≤ q) (n : ℕ)
    (hWbound : ∀ j, j ≤ n → W j ≤ B)
    (hPbound : ∀ j, j ≤ n → P j ≤ R) :
    scaledExponentialJetMajorant W P q n ≤
      B * scaledExponentialJetMajorant (fun _ => 1) (fun _ => R) q n := by
  rw [scaledExponentialJetMajorant, scaledExponentialJetMajorant, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  have ha : a.val ≤ n := Nat.le_of_lt_succ a.isLt
  have hPa := exponentialJetProductMajorant_le_const P hP hq (n - a.val)
    (fun j hj => hPbound j (hj.trans (Nat.sub_le n a.val)))
  calc
    _ ≤ (n.choose a.val : ℝ) * B *
        exponentialJetProductMajorant (fun _ => R) q (n - a.val) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (hWbound a.val ha) (Nat.cast_nonneg _))
        hPa (exponentialJetProductMajorant_nonneg P q hP hq _)
        (mul_nonneg (Nat.cast_nonneg _) hB)
    _ = _ := by ring

/-- In a nonempty product, one original factor keeps its weighted bound.
Every other factor uses only the scalar bound. -/
theorem prod_le_one_weighted_factor {k : ℕ} (hk : 0 < k)
    (u : Fin k → ℝ) {R U : ℝ}
    (hu : ∀ i, 0 ≤ u i) (hU : 0 ≤ U)
    (hRbound : ∀ i, u i ≤ R) (hUbound : ∀ i, u i ≤ U) :
    ∏ i, u i ≤ U * R ^ (k - 1) := by
  cases k with
  | zero => omega
  | succ k =>
    simp only [Nat.succ_sub_one]
    rw [Fin.prod_univ_succ]
    have ht : ∏ i : Fin k, u i.succ ≤ R ^ k := by
      calc
        _ ≤ ∏ _i : Fin k, R :=
          Finset.prod_le_prod₀ (fun i _ => hu i.succ) (fun i _ => hRbound i.succ)
        _ = _ := by
          simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact mul_le_mul (hUbound 0) ht
      (Finset.prod_nonneg (fun i _ => hu i.succ)) hU

/-- A purely numerical coefficient from the exact finite expansion. -/
def radialProfileNumericMajorant (R q : ℝ) (n k : ℕ) : ℝ :=
  ∑ d : RadialLeibnizIndex k n, (radialLeibnizCoefficient k n d : ℝ) *
    scaledExponentialJetMajorant (fun _ => 1) (fun _ => R) q
      (radialLeibnizOrders k n d 0)

theorem radialProfileNumericMajorant_nonneg {R q : ℝ}
    (hR : 0 ≤ R) (hq : 0 ≤ q) (n k : ℕ) :
    0 ≤ radialProfileNumericMajorant R q n k :=
  Finset.sum_nonneg (fun d _ => mul_nonneg (Nat.cast_nonneg _)
    (scaledExponentialJetMajorant_nonneg _ _ q (fun _ => zero_le_one)
      (fun _ => hR) hq _))

/-- Exact single-weight absorption for the genuine profile majorant.
The assumptions concern its primitive reference and exponent jets. -/
theorem profileParameterProductMajorant_le_one_weight
    (W P : ℕ → ℝ) {B R U q : ℝ}
    (hW : ∀ j, 0 ≤ W j) (hP : ∀ j, 0 ≤ P j)
    (hB : 0 ≤ B) (hR : 0 ≤ R) (hU : 0 ≤ U) (hq : 0 ≤ q)
    (n k : ℕ) (hk : 0 < k)
    (hWbound : ∀ j, j ≤ n → W j ≤ B)
    (hPbound : ∀ j, j ≤ n → P j ≤ R)
    (hPweight : ∀ j, j ≤ n → P j ≤ U) :
    profileParameterProductMajorant W P q n k ≤
      radialProfileNumericMajorant R q n k * B * U * R ^ (k - 1) := by
  classical
  let F (d : RadialLeibnizIndex k n) :=
    scaledExponentialJetMajorant (fun _ => 1) (fun _ => R) q
      (radialLeibnizOrders k n d 0)
  have hF (d : RadialLeibnizIndex k n) : 0 ≤ F d :=
    scaledExponentialJetMajorant_nonneg _ _ q (fun _ => zero_le_one)
      (fun _ => hR) hq _
  calc
    profileParameterProductMajorant W P q n k ≤
        ∑ d : RadialLeibnizIndex k n,
          ((radialLeibnizCoefficient k n d : ℝ) * F d) *
            (B * U * R ^ (k - 1)) := by
      apply Finset.sum_le_sum
      intro d _
      have hd0 := radialLeibnizOrders_le k n d 0
      have hscaled := scaledExponentialJetMajorant_le_const W P hW hP hB hq
        (radialLeibnizOrders k n d 0)
        (fun j hj => hWbound j (hj.trans hd0))
        (fun j hj => hPbound j (hj.trans hd0))
      have hdirection := prod_le_one_weighted_factor hk
        (fun i : Fin k => P (radialLeibnizOrders k n d i.succ))
        (fun i => hP _) hU
        (fun i => hPbound _ (radialLeibnizOrders_le k n d i.succ))
        (fun i => hPweight _ (radialLeibnizOrders_le k n d i.succ))
      calc
        _ ≤ (radialLeibnizCoefficient k n d : ℝ) *
            (B * F d) * (U * R ^ (k - 1)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hscaled (Nat.cast_nonneg _))
            hdirection (Finset.prod_nonneg (fun i _ => hP _))
            (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hB (hF d)))
        _ = _ := by ring
    _ = (∑ d : RadialLeibnizIndex k n,
        (radialLeibnizCoefficient k n d : ℝ) * F d) *
          (B * U * R ^ (k - 1)) := (Finset.sum_mul _ _ _).symm
    _ = radialProfileNumericMajorant R q n k * B * U * R ^ (k - 1) := by
      rw [radialProfileNumericMajorant]
      dsimp only [F]
      ring

end ContinuousFlexibility.Analysis
