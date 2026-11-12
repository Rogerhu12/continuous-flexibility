import ContinuousFlexibility.Analysis.N01cOneHighProducts
import ContinuousFlexibility.Analysis.N01cStateSeminorms

/-!
# Fixed-base normalization for the higher flow variations

The circle forcing estimate has one factor at the requested spatial
order and finitely many factors at orders depending only on the
parameter order.  Interpolation spends the sum of these offsets in the
high index.  The low base is chosen once, before the parameter order,
polynomial degree, offset, or spatial order.

The last theorem applies to the genuine multilinear variation. Its raw
unit-ball hypothesis is the polynomial estimate obtained from the
linear variational equation and the finite forcing products. The same
constants work at every larger low base, so independently chosen common
neighbourhoods can be restricted before this normalization is applied.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements
open scoped BigOperators

section AggregateProducts

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Arbitrary products of affine sums of actual seminorms, with one
common interpolation base and the exact total assigned order. -/
theorem exists_oneHighAggregateProductBounds
    (p : ℕ → Seminorm ℝ E) (hp : Monotone p) (hinterp : HasInterpolation p) :
    ∃ base loss : ℕ, ∀ k factors s : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ a : Fin factors → ℕ, (∑ j, a j ≤ s) → ∀ x : Fin k → E,
        (∀ i, p base (x i) ≤ 1) →
        (∏ j, (1 + ∑ i, p (a j) (x i))) ≤
          C * (1 + ∑ i, p (s + loss) (x i)) := by
  classical
  obtain ⟨base, loss, hsingle⟩ := exists_interpolatedJetBounds p hp hinterp 0
  refine ⟨base, loss, fun k factors s => ?_⟩
  choose c hc hcb using
    (fun a : Fin (s + 1) => hsingle s a.val (Nat.le_of_lt_succ a.isLt))
  let M : ℝ := ∑ a : Fin (s + 1), c a
  have hM : 0 ≤ M := Finset.sum_nonneg (fun a _ => zero_le_one.trans (hc a))
  have hcM (a : Fin (s + 1)) : c a ≤ M :=
    Finset.single_le_sum (fun j _ => zero_le_one.trans (hc j)) (Finset.mem_univ a)
  let K : ℝ := 1 + (k : ℝ) * M
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨K ^ factors, pow_pos hK _, fun a ha x hx => ?_⟩
  let R : ℝ := 1 + ∑ i, p (s + loss) (x i)
  have hR : 1 ≤ R := by
    dsimp only [R]
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => apply_nonneg _ _))
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hai (j : Fin factors) : a j ≤ s :=
    (Finset.single_le_sum (fun i _ => Nat.zero_le (a i)) (Finset.mem_univ j)).trans ha
  have hfactor (j : Fin factors) :
      1 + ∑ i, p (a j) (x i) ≤ K * R ^ ((a j : ℝ) / ((s : ℝ) + 1)) := by
    let θ : ℝ := (a j : ℝ) / ((s : ℝ) + 1)
    have hθ : 0 ≤ θ := by dsimp only [θ]; positivity
    have hpoint (i : Fin k) : p (a j) (x i) ≤ M * R ^ θ := by
      have hb : p (a j) (x i) ≤ c ⟨a j, Nat.lt_succ_of_le (hai j)⟩ *
          (1 + p (s + loss) (x i)) ^ θ := by
        simpa only [Nat.add_zero] using
          hcb ⟨a j, Nat.lt_succ_of_le (hai j)⟩ (x i) (hx i)
      have harg : 1 + p (s + loss) (x i) ≤ R :=
        add_le_add (le_rfl : (1 : ℝ) ≤ 1)
          (Finset.single_le_sum (fun l _ => apply_nonneg _ _) (Finset.mem_univ i))
      have hpow := Real.rpow_le_rpow (by positivity : 0 ≤ 1 + p (s + loss) (x i)) harg hθ
      exact hb.trans (mul_le_mul (hcM _) hpow
        (Real.rpow_nonneg (by positivity) _) hM)
    have hsum : ∑ i, p (a j) (x i) ≤ (k : ℝ) * M * R ^ θ := by
      calc
        _ ≤ ∑ _i : Fin k, M * R ^ θ := Finset.sum_le_sum (fun i _ => hpoint i)
        _ = _ := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
    calc
      1 + ∑ i, p (a j) (x i) ≤ R ^ θ + (k : ℝ) * M * R ^ θ :=
        add_le_add (Real.one_le_rpow hR hθ) hsum
      _ = K * R ^ θ := by dsimp only [K]; ring
  calc
    (∏ j, (1 + ∑ i, p (a j) (x i))) ≤
        ∏ j, K * R ^ ((a j : ℝ) / ((s : ℝ) + 1)) :=
      Finset.prod_le_prod₀
        (fun j _ => by positivity) (fun j _ => hfactor j)
    _ = K ^ factors * R ^ (∑ j, (a j : ℝ) / ((s : ℝ) + 1)) := by
      rw [Finset.prod_mul_distrib, ← Real.rpow_sum_of_pos hRpos]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ ≤ K ^ factors * R :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_self_of_one_le hR (sum_order_fractions_le_one a ha))
        (pow_nonneg hK.le _)

end AggregateProducts

section MultilinearNormalization

variable {E F : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A polynomial in fixed low spatial orders, multiplied by one
requested-order factor, costs only a parameter-dependent additive loss.
The base is independent of all four natural-number arguments. The
normalization is valid on the unit ball of any larger base, with the
same constant and the same high index. -/
theorem exists_flowVariationPolynomialNormalization
    (p : ℕ → Seminorm ℝ E) (hp : Monotone p) (hinterp : HasInterpolation p) :
    ∃ base loss : ℕ, ∀ k degree offset s : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ base' : ℕ, base ≤ base' →
      ∀ x : E, p base' x ≤ 1 → ∀ A : E [×k]→L[ℝ] F, ∀ M : ℝ, 0 ≤ M →
      (∀ v : Fin k → E, (∀ i, p base' (v i) < 1) →
        ‖A v‖ ≤ M *
          ((1 + p (s + offset) x) + ∑ i, p (s + offset) (v i)) *
          (((1 + p offset x) + ∑ i, p offset (v i)) ^ degree)) →
      ∀ v : Fin k → E, ‖A v‖ ≤ M * C *
        oneHighVariationWeight p base'
          (s + (degree + 1) * offset + loss) x v := by
  classical
  obtain ⟨base, loss, hprod⟩ := exists_oneHighAggregateProductBounds p hp hinterp
  refine ⟨base, loss, fun k degree offset s => ?_⟩
  let S : ℕ := s + (degree + 1) * offset
  obtain ⟨C, hC, hb⟩ := hprod (k + 1) (degree + 1) S
  refine ⟨C, hC, fun base' hbase x hx A M hM hraw v => ?_⟩
  have hn : ∀ w : Fin k → E,
      (normSeminorm ℝ F) (A w) ≤ M * C *
        multilinearTameSize (p base') (p (S + loss)) k
          (1 + p (S + loss) x) w := by
    apply multilinear_bound_of_unitBall A (normSeminorm ℝ F)
      (p base') (p (S + loss)) (mul_nonneg hM hC.le)
    intro w hw
    let orders : Fin (degree + 1) → ℕ := Fin.cons (s + offset) (fun _ => offset)
    have horders : ∑ j, orders j ≤ S := by
      simp only [orders, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        S, Nat.add_mul, Nat.one_mul, Nat.cast_id]
      omega
    let xw : Fin (k + 1) → E := Fin.cons x w
    have hxw : ∀ i : Fin (k + 1), p base (xw i) ≤ 1 := by
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa only [xw, Fin.cons_zero] using (hp hbase x).trans hx
      · simpa only [xw, Fin.cons_succ] using (hp hbase (w j)).trans (hw j).le
    have hpoly := hb orders horders xw hxw
    have hpoly' :
        (((1 + p (s + offset) x) + ∑ i, p (s + offset) (w i)) *
          (((1 + p offset x) + ∑ i, p offset (w i)) ^ degree)) ≤
        C * ((1 + p (S + loss) x) + ∑ i, p (S + loss) (w i)) := by
      simpa only [orders, xw, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
        Fin.sum_univ_succ, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        ← add_assoc] using hpoly
    calc
      (normSeminorm ℝ F) (A w) = ‖A w‖ := rfl
      _ ≤ M *
          ((1 + p (s + offset) x) + ∑ i, p (s + offset) (w i)) *
          (((1 + p offset x) + ∑ i, p offset (w i)) ^ degree) := hraw w hw
      _ = M * ((((1 + p (s + offset) x) + ∑ i, p (s + offset) (w i)) *
          (((1 + p offset x) + ∑ i, p offset (w i)) ^ degree))) := by ring
      _ ≤ M * (C * ((1 + p (S + loss) x) + ∑ i, p (S + loss) (w i))) :=
        mul_le_mul_of_nonneg_left hpoly' hM
      _ = _ := by ring
  simpa only [coe_normSeminorm, multilinearTameSize, oneHighVariationWeight, S] using hn v

end MultilinearNormalization

end ContinuousFlexibility.Analysis
