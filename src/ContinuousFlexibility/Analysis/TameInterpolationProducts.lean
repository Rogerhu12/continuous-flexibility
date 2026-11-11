import ContinuousFlexibility.Statements.Analysis
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Interpolation of products on one fixed low-order neighborhood

The loss in the frozen interpolation hypothesis is charged to each
factor whose order exceeds the chosen low order. A product is bounded
by one high seminorm whenever the sum of these charges fits below the
high order. The low order and the final loss are chosen before the
requested output order.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open scoped BigOperators

/-- The high-order interpolation exponent, before division by the
distance between the common high and low orders. -/
def interpolationOrderCost (base loss order : ℕ) : ℕ :=
  if base < order then order - base + loss else 0

section OneFactor

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- A single interpolation estimate with a freely chosen common upper
scale. Low-order factors have zero cost. -/
theorem interpolation_le_rpow_scale
    (p : ℕ → Seminorm ℝ E) (hp : Monotone p)
    (base loss order high : ℕ) (hhigh : base < high)
    (horder : base < order → order + loss < high)
    (hinterp : ∀ b c : ℕ, base < b → b + loss < c →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ x,
        p b x ≤ C * (p base x) ^ (((c : ℝ) - b - loss) / (c - base)) *
          (p c x) ^ (((b : ℝ) - base + loss) / (c - base)))
    (K : ℝ) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : E) (Q : ℝ),
      p base x ≤ K → p high x ≤ Q → 1 ≤ Q →
      p order x ≤ C * Q ^
        ((interpolationOrderCost base loss order : ℝ) / ((high : ℝ) - base)) := by
  by_cases hbo : base < order
  · obtain ⟨C, hC, hbound⟩ := hinterp order high hbo (horder hbo)
    have hden : 0 < (high : ℝ) - base := sub_pos.mpr (by exact_mod_cast hhigh)
    have hnum : 0 ≤ (high : ℝ) - order - loss := by
      have h : (order : ℝ) + loss < high := by exact_mod_cast horder hbo
      linarith
    have hnum' : 0 ≤ (order : ℝ) - base + loss := by
      have h : (base : ℝ) < order := by exact_mod_cast hbo
      linarith [Nat.cast_nonneg (α := ℝ) loss]
    have hα : 0 ≤ ((high : ℝ) - order - loss) / (high - base) :=
      div_nonneg hnum hden.le
    have hβ : 0 ≤ ((order : ℝ) - base + loss) / (high - base) :=
      div_nonneg hnum' hden.le
    have hcost : (interpolationOrderCost base loss order : ℝ) =
        (order : ℝ) - base + loss := by
      simp only [interpolationOrderCost, if_pos hbo, Nat.cast_add, Nat.cast_sub hbo.le]
    refine ⟨C * K ^ (((high : ℝ) - order - loss) / (high - base)),
      mul_nonneg hC (Real.rpow_nonneg hK _), ?_⟩
    intro x Q hx hQ hQone
    rw [hcost]
    exact (hbound x).trans (mul_le_mul
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (apply_nonneg _ _) hx hα) hC)
      (Real.rpow_le_rpow (apply_nonneg _ _) hQ hβ)
      (Real.rpow_nonneg (apply_nonneg _ _) _)
      (mul_nonneg hC (Real.rpow_nonneg hK _)))
  · refine ⟨K, hK, ?_⟩
    intro x Q hx hQ hQone
    simpa only [interpolationOrderCost, if_neg hbo, Nat.cast_zero,
      zero_div, Real.rpow_zero, mul_one] using
      (hp (Nat.le_of_not_gt hbo) x).trans hx

end OneFactor

/-- The scalar product step, valid for any finite number of factors.
Only the sum of the interpolation exponents is relevant. -/
theorem prod_le_common_scale_of_rpow_bounds
    {ι : Type*} [Fintype ι] (a C exponent : ι → ℝ) (Q : ℝ)
    (ha : ∀ i, 0 ≤ a i) (hC : ∀ i, 0 ≤ C i) (hQ : 1 ≤ Q)
    (hexponent : ∑ i, exponent i ≤ 1)
    (hbound : ∀ i, a i ≤ C i * Q ^ exponent i) :
    ∏ i, a i ≤ (∏ i, C i) * Q := by
  have hQpos : 0 < Q := zero_lt_one.trans_le hQ
  calc
    ∏ i, a i ≤ ∏ i, C i * Q ^ exponent i :=
      Finset.prod_le_prod₀ (fun i _ => ha i) (fun i _ => hbound i)
    _ = (∏ i, C i) * Q ^ (∑ i, exponent i) := by
      rw [Finset.prod_mul_distrib, Real.rpow_sum_of_pos hQpos]
    _ ≤ (∏ i, C i) * Q ^ (1 : ℝ) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hQ hexponent)
        (Finset.prod_nonneg (fun i _ => hC i))
    _ = (∏ i, C i) * Q := by rw [Real.rpow_one]

section FiniteProducts

variable {ι : Type*} [Fintype ι] {E : ι → Type*}
  [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)]

/-- Different spaces and different interpolation losses may share one
high scale. This form preserves the exact derivative-order budget for
Faà di Bruno and Leibniz terms. -/
theorem finite_product_interpolation_bound
    (p : ∀ i, ℕ → Seminorm ℝ (E i)) (hp : ∀ i, Monotone (p i))
    (base high : ℕ) (loss order : ι → ℕ) (hhigh : base < high)
    (horder : ∀ i, base < order i → order i + loss i < high)
    (hcost : ∑ i, interpolationOrderCost base (loss i) (order i) ≤ high - base)
    (hinterp : ∀ i, ∀ b c : ℕ, base < b → b + loss i < c →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ x,
        p i b x ≤ C * (p i base x) ^ (((c : ℝ) - b - loss i) / (c - base)) *
          (p i c x) ^ (((b : ℝ) - base + loss i) / (c - base)))
    (K : ι → ℝ) (hK : ∀ i, 0 ≤ K i) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ∀ i, E i,
      (∀ i, p i base (x i) ≤ K i) →
      ∏ i, p i (order i) (x i) ≤ C * (1 + ∑ i, p i high (x i)) := by
  classical
  choose C hC hbound using fun i =>
    interpolation_le_rpow_scale (p i) (hp i) base (loss i) (order i) high
      hhigh (horder i) (hinterp i) (K i) (hK i)
  refine ⟨∏ i, C i, Finset.prod_nonneg (fun i _ => hC i), ?_⟩
  intro x hx
  let Q : ℝ := 1 + ∑ i, p i high (x i)
  have hQ : 1 ≤ Q :=
    le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => apply_nonneg _ _))
  have hden : 0 < (high : ℝ) - base := sub_pos.mpr (by exact_mod_cast hhigh)
  have hsum : (∑ i, (interpolationOrderCost base (loss i) (order i) : ℝ) /
      ((high : ℝ) - base)) ≤ 1 := by
    calc
      _ = ((∑ i, interpolationOrderCost base (loss i) (order i) : ℕ) : ℝ) /
          ((high : ℝ) - base) := by
        simp only [div_eq_mul_inv, ← Finset.sum_mul, Nat.cast_sum]
      _ ≤ ((high - base : ℕ) : ℝ) / ((high : ℝ) - base) :=
        div_le_div_of_nonneg_right (by exact_mod_cast hcost) hden.le
      _ = 1 := by rw [Nat.cast_sub hhigh.le, div_self hden.ne']
  apply prod_le_common_scale_of_rpow_bounds
    (fun i => p i (order i) (x i)) C
    (fun i => (interpolationOrderCost base (loss i) (order i) : ℝ) /
      ((high : ℝ) - base)) Q (fun i => apply_nonneg _ _) hC hQ hsum
  intro i
  have hi : p i high (x i) ≤ ∑ j, p j high (x j) :=
    Finset.single_le_sum (f := fun j => p j high (x j))
      (fun j _ => apply_nonneg (p j high) (x j)) (Finset.mem_univ i)
  exact hbound i (x i) Q (hx i) (hi.trans (by dsimp [Q]; linarith)) hQ

end FiniteProducts

section TwoFactors

variable {E F : Type*} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F]

/-- The two-factor cost criterion, without identifying the two spaces. -/
theorem two_factor_interpolation_bound
    (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ F)
    (hp : Monotone p) (hq : Monotone q)
    (base high lossP lossQ a b : ℕ) (hhigh : base < high)
    (ha : base < a → a + lossP < high)
    (hb : base < b → b + lossQ < high)
    (hcost : interpolationOrderCost base lossP a +
      interpolationOrderCost base lossQ b ≤ high - base)
    (hIp : ∀ i j : ℕ, base < i → i + lossP < j →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ x,
        p i x ≤ C * (p base x) ^ (((j : ℝ) - i - lossP) / (j - base)) *
          (p j x) ^ (((i : ℝ) - base + lossP) / (j - base)))
    (hIq : ∀ i j : ℕ, base < i → i + lossQ < j →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ y,
        q i y ≤ C * (q base y) ^ (((j : ℝ) - i - lossQ) / (j - base)) *
          (q j y) ^ (((i : ℝ) - base + lossQ) / (j - base)))
    (Kp Kq : ℝ) (hKp : 0 ≤ Kp) (hKq : 0 ≤ Kq) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x y, p base x ≤ Kp → q base y ≤ Kq →
      p a x * q b y ≤ C * (1 + p high x + q high y) := by
  obtain ⟨Cp, hCp, hpb⟩ :=
    interpolation_le_rpow_scale p hp base lossP a high hhigh ha hIp Kp hKp
  obtain ⟨Cq, hCq, hqb⟩ :=
    interpolation_le_rpow_scale q hq base lossQ b high hhigh hb hIq Kq hKq
  refine ⟨Cp * Cq, mul_nonneg hCp hCq, ?_⟩
  intro x y hx hy
  let Q : ℝ := 1 + p high x + q high y
  have hQ : 1 ≤ Q := by
    dsimp [Q]
    linarith [apply_nonneg (p high) x, apply_nonneg (q high) y]
  have hpQ : p high x ≤ Q := by dsimp [Q]; linarith [apply_nonneg (q high) y]
  have hqQ : q high y ≤ Q := by dsimp [Q]; linarith [apply_nonneg (p high) x]
  have hden : 0 < (high : ℝ) - base := sub_pos.mpr (by exact_mod_cast hhigh)
  have hsum :
      (interpolationOrderCost base lossP a : ℝ) / ((high : ℝ) - base) +
      (interpolationOrderCost base lossQ b : ℝ) / ((high : ℝ) - base) ≤ 1 := by
    rw [← add_div, div_le_one hden]
    have hc : ((interpolationOrderCost base lossP a : ℝ) +
        (interpolationOrderCost base lossQ b : ℝ)) ≤ ((high - base : ℕ) : ℝ) := by
      exact_mod_cast hcost
    simpa only [Nat.cast_sub hhigh.le] using hc
  calc
    p a x * q b y ≤
        (Cp * Q ^ ((interpolationOrderCost base lossP a : ℝ) / ((high : ℝ) - base))) *
        (Cq * Q ^ ((interpolationOrderCost base lossQ b : ℝ) / ((high : ℝ) - base))) :=
      mul_le_mul (hpb x Q hx hpQ hQ) (hqb y Q hy hqQ hQ)
        (apply_nonneg _ _) (mul_nonneg hCp (Real.rpow_nonneg (zero_le_one.trans hQ) _))
    _ = (Cp * Cq) * Q ^
        ((interpolationOrderCost base lossP a : ℝ) / ((high : ℝ) - base) +
          (interpolationOrderCost base lossQ b : ℝ) / ((high : ℝ) - base)) := by
      rw [Real.rpow_add (zero_lt_one.trans_le hQ)]
      ring
    _ ≤ (Cp * Cq) * Q ^ (1 : ℝ) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hQ hsum) (mul_nonneg hCp hCq)
    _ = (Cp * Cq) * (1 + p high x + q high y) := by rw [Real.rpow_one]

/-- The frozen interpolation hypotheses give a loss independent of the
output order and one constant uniform over all splits of that order.
The requested low order can be imposed before choosing the neighborhood. -/
theorem hasInterpolation_mul_local_growth
    (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ F)
    (hp : Monotone p) (hq : Monotone q)
    (hIp : HasInterpolation p) (hIq : HasInterpolation q)
    (offset requestedBase : ℕ) (Kp Kq : ℝ) (hKp : 0 ≤ Kp) (hKq : 0 ≤ Kq) :
    ∃ base loss : ℕ, requestedBase ≤ base ∧
      ∀ s : ℕ, base ≤ s → ∃ C : ℝ, 0 ≤ C ∧
        ∀ a b : ℕ, a + b ≤ s + offset → ∀ x y,
          p base x ≤ Kp → q base y ≤ Kq →
          p a x * q b y ≤ C * (1 + p (s + loss) x + q (s + loss) y) := by
  classical
  obtain ⟨bp, lp, hIp⟩ := hIp
  obtain ⟨bq, lq, hIq⟩ := hIq
  let base : ℕ := max requestedBase (max bp bq)
  let loss : ℕ := offset + lp + lq + 1
  have hbp : bp ≤ base := (le_max_left bp bq).trans (le_max_right _ _)
  have hbq : bq ≤ base := (le_max_right bp bq).trans (le_max_right _ _)
  refine ⟨base, loss, le_max_left _ _, ?_⟩
  intro s hs
  have hhigh : base < s + loss := by dsimp [loss]; omega
  have hsingle (a b : ℕ) (hab : a + b ≤ s + offset) :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ x y, p base x ≤ Kp → q base y ≤ Kq →
        p a x * q b y ≤ C * (1 + p (s + loss) x + q (s + loss) y) := by
    refine two_factor_interpolation_bound p q hp hq base (s + loss) lp lq a b hhigh
      ?_ ?_ ?_ ?_ ?_ Kp Kq hKp hKq
    · intro hba
      dsimp [loss]
      omega
    · intro hbb
      dsimp [loss]
      omega
    · unfold interpolationOrderCost
      dsimp [loss]
      split_ifs <;> omega
    · exact fun i j hi hij => hIp base i j hbp hi hij
    · exact fun i j hi hij => hIq base i j hbq hi hij
  let I := {ab : Fin (s + offset + 1) × Fin (s + offset + 1) //
    ab.1.val + ab.2.val ≤ s + offset}
  have hfinite : ∀ i : I, ∃ C : ℝ, 0 ≤ C ∧ ∀ x y,
      p base x ≤ Kp → q base y ≤ Kq →
      p i.val.1.val x * q i.val.2.val y ≤
        C * (1 + p (s + loss) x + q (s + loss) y) :=
    fun i => hsingle i.val.1.val i.val.2.val i.property
  choose C hC hbound using hfinite
  refine ⟨∑ i : I, C i, Finset.sum_nonneg (fun i _ => hC i), ?_⟩
  intro a b hab x y hx hy
  let i : I := ⟨(⟨a, by omega⟩, ⟨b, by omega⟩), hab⟩
  have hi : C i ≤ ∑ j : I, C j :=
    Finset.single_le_sum (fun j _ => hC j) (Finset.mem_univ i)
  exact (hbound i x y hx hy).trans
    (mul_le_mul_of_nonneg_right hi (by positivity))

end TwoFactors

end ContinuousFlexibility.Statements
