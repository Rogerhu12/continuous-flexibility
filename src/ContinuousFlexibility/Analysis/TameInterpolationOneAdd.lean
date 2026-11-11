import ContinuousFlexibility.Analysis.TameInterpolationProducts

/-!
# Affine factors in finite interpolation products

The first derivative of a circle chart is one plus a decoded derivative.
Adding one to an interpolated seminorm does not change its order cost,
because the common high scale is at least one.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open scoped BigOperators

variable {ι : Type*} [Fintype ι] {E : ι → Type*}
  [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)]

theorem finite_product_one_add_interpolation_bound
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
      ∏ i, (1 + p i (order i) (x i)) ≤ C * (1 + ∑ i, p i high (x i)) := by
  classical
  choose C hC hbound using fun i =>
    interpolation_le_rpow_scale (p i) (hp i) base (loss i) (order i) high
      hhigh (horder i) (hinterp i) (K i) (hK i)
  have hCp (i : ι) : 0 ≤ 1 + C i := by linarith [hC i]
  refine ⟨∏ i, (1 + C i), Finset.prod_nonneg (fun i _ => hCp i), ?_⟩
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
    (fun i => 1 + p i (order i) (x i)) (fun i => 1 + C i)
    (fun i => (interpolationOrderCost base (loss i) (order i) : ℝ) /
      ((high : ℝ) - base)) Q (fun i => by positivity) hCp hQ hsum
  intro i
  have hi : p i high (x i) ≤ ∑ j, p j high (x j) :=
    Finset.single_le_sum (f := fun j => p j high (x j))
      (fun j _ => apply_nonneg (p j high) (x j)) (Finset.mem_univ i)
  have hpow : 1 ≤ Q ^
      ((interpolationOrderCost base (loss i) (order i) : ℝ) / ((high : ℝ) - base)) := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hQ
      (div_nonneg (Nat.cast_nonneg (interpolationOrderCost base (loss i) (order i))) hden.le)
  calc
    1 + p i (order i) (x i) ≤ Q ^
        ((interpolationOrderCost base (loss i) (order i) : ℝ) / ((high : ℝ) - base)) +
        C i * Q ^
          ((interpolationOrderCost base (loss i) (order i) : ℝ) / ((high : ℝ) - base)) :=
      add_le_add hpow (hbound i (x i) Q (hx i)
        (hi.trans (by dsimp [Q]; linarith)) hQ)
    _ = _ := by ring

end ContinuousFlexibility.Statements
