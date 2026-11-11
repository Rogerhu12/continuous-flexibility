import ContinuousFlexibility.Analysis.N01cProfileMixedDerivatives
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Algebra.BigOperators.Fin

/-!
# Finite radial Leibniz products with exact differential order

The index type records a recursive binomial expansion for a product of
one or more scalar functions.  Every summand has exactly the requested
total spatial order, including terms whose order at some factors is zero.
The exponential expansion uses the genuine ordered-partition formula.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

/-- Indices of the recursive Leibniz expansion for a product of k+1 factors. -/
def RadialLeibnizIndex : ℕ → ℕ → Type
  | 0, _ => Unit
  | k + 1, n => (j : Fin (n + 1)) × RadialLeibnizIndex k (n - j.val)

instance radialLeibnizIndexFintype (k n : ℕ) : Fintype (RadialLeibnizIndex k n) := by
  induction k generalizing n with
  | zero =>
      change Fintype Unit
      infer_instance
  | succ k ih =>
      change Fintype ((j : Fin (n + 1)) × RadialLeibnizIndex k (n - j.val))
      letI : ∀ j : Fin (n + 1), Fintype (RadialLeibnizIndex k (n - j.val)) :=
        fun j => ih (n - j.val)
      infer_instance

instance radialLeibnizIndexUniqueZero (n : ℕ) : Unique (RadialLeibnizIndex 0 n) := by
  change Unique Unit
  infer_instance

/-- The order at each factor in the chosen Leibniz summand. -/
def radialLeibnizOrders : (k n : ℕ) → RadialLeibnizIndex k n → Fin (k + 1) → ℕ
  | 0, n, _ => fun _ => n
  | k + 1, n, d => Fin.cons d.1.val (radialLeibnizOrders k (n - d.1.val) d.2)

/-- The nonnegative integer coefficient of the chosen summand. -/
def radialLeibnizCoefficient : (k n : ℕ) → RadialLeibnizIndex k n → ℕ
  | 0, _, _ => 1
  | k + 1, n, d => n.choose d.1.val * radialLeibnizCoefficient k (n - d.1.val) d.2

theorem radialLeibnizOrders_sum (k : ℕ) :
    ∀ n (d : RadialLeibnizIndex k n), ∑ i, radialLeibnizOrders k n d i = n := by
  induction k with
  | zero =>
      intro n d
      simp only [radialLeibnizOrders, Fin.sum_univ_one]
  | succ k ih =>
      intro n d
      simp only [radialLeibnizOrders, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
      rw [ih]
      have hj : d.1.val ≤ n := Nat.le_of_lt_succ d.1.isLt
      omega

/-- Exact finite Leibniz formula; only smoothness at the evaluation point
is needed, so the result applies to the original locally finite profiles. -/
theorem iteratedDeriv_finProduct_eq_radialLeibniz (k : ℕ) :
    ∀ (n : ℕ) (f : Fin (k + 1) → ℝ → ℝ) (x : ℝ),
      (∀ i, ContDiffAt ℝ ∞ (f i) x) →
      iteratedDeriv n (fun t => ∏ i, f i t) x =
        ∑ d : RadialLeibnizIndex k n, (radialLeibnizCoefficient k n d : ℝ) *
          ∏ i, iteratedDeriv (radialLeibnizOrders k n d i) (f i) x := by
  induction k with
  | zero =>
      intro n f x hf
      have hprod : (fun t => ∏ i : Fin 1, f i t) = f 0 :=
        funext (fun t => Fin.prod_univ_one (fun i => f i t))
      rw [hprod]
      simp only [radialLeibnizCoefficient, radialLeibnizOrders,
        Fintype.sum_unique, Fin.prod_univ_one, Nat.cast_one, one_mul]
  | succ k ih =>
      intro n f x hf
      let g : Fin (k + 1) → ℝ → ℝ := fun i => f i.succ
      have hg : ContDiffAt ℝ ∞ (fun t => ∏ i, g i t) x :=
        contDiffAt_prod (fun i _ => hf i.succ)
      have hprod : (fun t => ∏ i : Fin (k + 2), f i t) =
          (fun t => f 0 t * ∏ i : Fin (k + 1), g i t) :=
        funext (fun t => Fin.prod_univ_succ (fun i => f i t))
      let term (j : ℕ) : ℝ := (n.choose j : ℝ) *
        iteratedDeriv j (f 0) x * iteratedDeriv (n - j) (fun t => ∏ i, g i t) x
      have hmul : iteratedDeriv n (fun t => ∏ i : Fin (k + 2), f i t) x =
          ∑ j : Fin (n + 1), term j.val := by
        rw [hprod, Fin.sum_univ_eq_sum_range term]
        exact iteratedDeriv_fun_mul ((hf 0).of_le (by simp)) (hg.of_le (by simp))
      calc
        iteratedDeriv n (fun t => ∏ i : Fin (k + 2), f i t) x =
            ∑ j : Fin (n + 1), term j.val := hmul
        _ = ∑ j : Fin (n + 1), ∑ e : RadialLeibnizIndex k (n - j.val),
            (radialLeibnizCoefficient (k + 1) n ⟨j, e⟩ : ℝ) *
              ∏ i, iteratedDeriv (radialLeibnizOrders (k + 1) n ⟨j, e⟩ i) (f i) x := by
          apply Finset.sum_congr rfl
          intro j _
          dsimp only [term]
          rw [ih (n - j.val) g x (fun i => hf i.succ), Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro e _
          simp only [radialLeibnizCoefficient, radialLeibnizOrders,
            Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Nat.cast_mul, g]
          ring
        _ = ∑ d : RadialLeibnizIndex (k + 1) n,
            (radialLeibnizCoefficient (k + 1) n d : ℝ) *
              ∏ i, iteratedDeriv (radialLeibnizOrders (k + 1) n d i) (f i) x := by
          rw [Fintype.sum_sigma]

/-- Replacing each actual factor jet by its own original majorant preserves
the distribution of spatial orders in every term. -/
theorem abs_iteratedDeriv_finProduct_le_radialLeibniz
    (k n : ℕ) (f : Fin (k + 1) → ℝ → ℝ) (x : ℝ)
    (hf : ∀ i, ContDiffAt ℝ ∞ (f i) x) (M : Fin (k + 1) → ℕ → ℝ)
    (hM : ∀ i j, |iteratedDeriv j (f i) x| ≤ M i j) :
    |iteratedDeriv n (fun t => ∏ i, f i t) x| ≤
      ∑ d : RadialLeibnizIndex k n, (radialLeibnizCoefficient k n d : ℝ) *
        ∏ i, M i (radialLeibnizOrders k n d i) := by
  rw [iteratedDeriv_finProduct_eq_radialLeibniz k n f x hf]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro d _
  rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _), Finset.abs_prod]
  exact mul_le_mul_of_nonneg_left
    (Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun i _ => hM i _))
    (Nat.cast_nonneg _)

/-- An ordered partition spends precisely its input derivative order. -/
theorem orderedFinpartition_sum_partSize {n : ℕ} (c : OrderedFinpartition n) :
    ∑ i, c.partSize i = n := by
  simpa only [Fintype.card_sigma, Fintype.card_fin] using Fintype.card_congr c.equivSigma

/-- The finite original products in an exponential jet majorant. -/
def exponentialJetProductMajorant (P : ℕ → ℝ) (q : ℝ) (n : ℕ) : ℝ :=
  ∑ c : OrderedFinpartition n, ∏ i, P (c.partSize i) * q

theorem exponentialJetProductMajorant_nonneg (P : ℕ → ℝ) (q : ℝ)
    (hP : ∀ n, 0 ≤ P n) (hq : 0 ≤ q) (n : ℕ) :
    0 ≤ exponentialJetProductMajorant P q n :=
  Finset.sum_nonneg (fun c _ =>
    Finset.prod_nonneg (fun i _ => mul_nonneg (hP (c.partSize i)) hq))

theorem iteratedDeriv_exp_eq_orderedProducts {e : ℝ → ℝ} {r : ℝ}
    (he : ContDiffAt ℝ ∞ e r) (n : ℕ) :
    iteratedDeriv n (fun t => Real.exp (e t)) r =
      ∑ c : OrderedFinpartition n,
        Real.exp (e r) * ∏ i, iteratedDeriv (c.partSize i) e r := by
  have h := iteratedDeriv_comp_eq_sum_orderedFinpartition
    (Real.contDiff_exp.contDiffAt : ContDiffAt ℝ ∞ Real.exp (e r)) he
    (by simp : (n : ℕ∞ω) ≤ ∞)
  simpa only [Function.comp_apply, iteratedDeriv_eq_iterate, Real.iter_deriv_exp] using h

theorem abs_iteratedDeriv_exp_le_orderedProducts {e : ℝ → ℝ} {r : ℝ}
    (he : ContDiffAt ℝ ∞ e r) (P : ℕ → ℝ) (q : ℝ)
    (hjet : ∀ j, |iteratedDeriv j e r| ≤ P j * q) (n : ℕ) :
    |iteratedDeriv n (fun t => Real.exp (e t)) r| ≤
      Real.exp (e r) * exponentialJetProductMajorant P q n := by
  rw [iteratedDeriv_exp_eq_orderedProducts he n, exponentialJetProductMajorant,
    Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro c _
  rw [abs_mul, abs_of_pos (Real.exp_pos _), Finset.abs_prod]
  exact mul_le_mul_of_nonneg_left
    (Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun i _ => hjet (c.partSize i)))
    (Real.exp_pos _).le

/-- The reference-profile jets and the original exponent-jet products
before any weight comparison or interpolation. -/
def scaledExponentialJetMajorant (W P : ℕ → ℝ) (q : ℝ) (n : ℕ) : ℝ :=
  ∑ a : Fin (n + 1), (n.choose a.val : ℝ) * W a.val *
    exponentialJetProductMajorant P q (n - a.val)

theorem scaledExponentialJetMajorant_nonneg (W P : ℕ → ℝ) (q : ℝ)
    (hW : ∀ j, 0 ≤ W j) (hP : ∀ j, 0 ≤ P j) (hq : 0 ≤ q) (n : ℕ) :
    0 ≤ scaledExponentialJetMajorant W P q n :=
  Finset.sum_nonneg (fun a _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hW a.val))
      (exponentialJetProductMajorant_nonneg P q hP hq (n - a.val)))

theorem abs_iteratedDeriv_mul_exp_le {w e : ℝ → ℝ} {r : ℝ}
    (hw : ContDiffAt ℝ ∞ w r) (he : ContDiffAt ℝ ∞ e r)
    (P : ℕ → ℝ) (q : ℝ) (hjet : ∀ j, |iteratedDeriv j e r| ≤ P j * q)
    (n : ℕ) :
    |iteratedDeriv n (fun t => w t * Real.exp (e t)) r| ≤
      Real.exp (e r) *
        scaledExponentialJetMajorant (fun a => |iteratedDeriv a w r|) P q n := by
  let term (a : ℕ) : ℝ := (n.choose a : ℝ) * iteratedDeriv a w r *
    iteratedDeriv (n - a) (fun t => Real.exp (e t)) r
  have hmul : iteratedDeriv n (fun t => w t * Real.exp (e t)) r =
      ∑ a : Fin (n + 1), term a.val := by
    rw [Fin.sum_univ_eq_sum_range term]
    exact iteratedDeriv_fun_mul (hw.of_le (by simp)) (he.exp.of_le (by simp))
  rw [hmul, scaledExponentialJetMajorant, Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro a _
  dsimp only [term]
  rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _)]
  calc
    _ ≤ (n.choose a.val : ℝ) * |iteratedDeriv a.val w r| *
        (Real.exp (e r) * exponentialJetProductMajorant P q (n - a.val)) :=
      mul_le_mul_of_nonneg_left
        (abs_iteratedDeriv_exp_le_orderedProducts he P q hjet (n - a.val))
        (mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _))
    _ = Real.exp (e r) * ((n.choose a.val : ℝ) * |iteratedDeriv a.val w r| *
        exponentialJetProductMajorant P q (n - a.val)) := by ring

/-- Combining the Leibniz split and the exponential partition spends
exactly n spatial derivatives, so it fits distributed-order estimates. -/
theorem radialLeibniz_exponential_total_order (k n : ℕ) (d : RadialLeibnizIndex k n)
    (a : Fin (radialLeibnizOrders k n d 0 + 1))
    (c : OrderedFinpartition (radialLeibnizOrders k n d 0 - a.val)) :
    a.val + (∑ j, c.partSize j) +
      (∑ i : Fin k, radialLeibnizOrders k n d i.succ) = n := by
  have hsum := radialLeibnizOrders_sum k n d
  rw [Fin.sum_univ_succ] at hsum
  rw [orderedFinpartition_sum_partSize]
  have ha : a.val ≤ radialLeibnizOrders k n d 0 := Nat.le_of_lt_succ a.isLt
  omega

theorem exponentialJetProductMajorant_mono (P : ℕ → ℝ) {q Q : ℝ}
    (hP : ∀ j, 0 ≤ P j) (hq : 0 ≤ q) (hqq : q ≤ Q) (n : ℕ) :
    exponentialJetProductMajorant P q n ≤ exponentialJetProductMajorant P Q n :=
  Finset.sum_le_sum (fun c _ =>
    Finset.prod_le_prod₀ (fun i _ => mul_nonneg (hP (c.partSize i)) hq)
      (fun i _ => mul_le_mul_of_nonneg_left hqq (hP (c.partSize i))))

theorem scaledExponentialJetMajorant_mono (W P : ℕ → ℝ) {q Q : ℝ}
    (hW : ∀ j, 0 ≤ W j) (hP : ∀ j, 0 ≤ P j) (hq : 0 ≤ q) (hqq : q ≤ Q) (n : ℕ) :
    scaledExponentialJetMajorant W P q n ≤ scaledExponentialJetMajorant W P Q n :=
  Finset.sum_le_sum (fun a _ =>
    mul_le_mul_of_nonneg_left (exponentialJetProductMajorant_mono P hP hq hqq (n - a.val))
      (mul_nonneg (Nat.cast_nonneg _) (hW a.val)))

/-- The complete finite coefficient in the mixed profile derivative bound.
The direction seminorms have been factored out, while the P-order assigned
to each direction is retained in every summand. -/
def profileParameterProductMajorant (W P : ℕ → ℝ) (q : ℝ) (n k : ℕ) : ℝ :=
  ∑ d : RadialLeibnizIndex k n, (radialLeibnizCoefficient k n d : ℝ) *
    scaledExponentialJetMajorant W P q (radialLeibnizOrders k n d 0) *
      ∏ i : Fin k, P (radialLeibnizOrders k n d i.succ)

theorem profileParameterProductMajorant_nonneg (W P : ℕ → ℝ) (q : ℝ)
    (hW : ∀ j, 0 ≤ W j) (hP : ∀ j, 0 ≤ P j) (hq : 0 ≤ q) (n k : ℕ) :
    0 ≤ profileParameterProductMajorant W P q n k :=
  Finset.sum_nonneg (fun d _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
      (scaledExponentialJetMajorant_nonneg W P q hW hP hq _))
      (Finset.prod_nonneg (fun i _ => hP _)))

theorem profileParameterProductMajorant_mono (W P : ℕ → ℝ) {q Q : ℝ}
    (hW : ∀ j, 0 ≤ W j) (hP : ∀ j, 0 ≤ P j) (hq : 0 ≤ q) (hqq : q ≤ Q) (n k : ℕ) :
    profileParameterProductMajorant W P q n k ≤ profileParameterProductMajorant W P Q n k :=
  Finset.sum_le_sum (fun d _ =>
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (scaledExponentialJetMajorant_mono W P hW hP hq hqq _)
        (Nat.cast_nonneg _))
      (Finset.prod_nonneg (fun i _ => hP _)))

theorem radialLeibniz_product_factorization
    (W P : ℕ → ℝ) (q a : ℝ) (n k : ℕ) (V : Fin k → ℝ) :
    (∑ d : RadialLeibnizIndex k n, (radialLeibnizCoefficient k n d : ℝ) *
      ∏ i : Fin (k + 1),
        ((Fin.cons (fun j => a * scaledExponentialJetMajorant W P q j)
          (fun i j => P j * V i) : Fin (k + 1) → ℕ → ℝ) i)
            (radialLeibnizOrders k n d i)) =
      a * profileParameterProductMajorant W P q n k * ∏ i, V i := by
  rw [profileParameterProductMajorant, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d _
  rw [Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  rw [Finset.prod_mul_distrib]
  ring

theorem seminorm_le_reference_add_of_displacement_bound
    {E : Type*} [AddCommGroup E] [Module ℝ E] (p : Seminorm ℝ E)
    (x reference : E) {ε : ℝ} (h : p (x - reference) ≤ ε) :
    p x ≤ p reference + ε := by
  have ht : p x ≤ p (x - reference) + p reference := by
    simpa only [sub_add_cancel] using map_add_le_add p (x - reference) reference
  linarith


end ContinuousFlexibility.Analysis
