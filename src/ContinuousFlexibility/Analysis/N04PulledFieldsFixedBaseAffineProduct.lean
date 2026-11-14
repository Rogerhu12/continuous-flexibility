import ContinuousFlexibility.Analysis.JointJetInterpolationBudget

/-!
# Complementary spatial products with one fixed low base

The interpolation base is chosen before either derivative loss. Losses
that depend on the parameter order enter only the common high index.
This is the elementary estimate needed to multiply fixed-base mixed
growth certificates without moving their parameter neighborhood.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open ContinuousFlexibility.Analysis
open scoped BigOperators

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

private theorem n04PulledFields_interpolationCost_le
    (B ell order : ℕ) : interpolationOrderCost B ell order ≤ order + ell := by
  unfold interpolationOrderCost
  split_ifs <;> omega

private theorem n04PulledFields_affine_product_at_orders
    (p : ℕ → Seminorm ℝ E) (hp : Monotone p) (B ell lossA lossB : ℕ)
    (hinterp : ∀ b c : ℕ, B < b → b + ell < c →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ x,
        p b x ≤ C * (p B x) ^ (((c : ℝ) - b - ell) / (c - B)) *
          (p c x) ^ (((b : ℝ) - B + ell) / (c - B)))
    (R : ℝ) (hR : 0 ≤ R) (a b : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x w : E, p B x ≤ R → p B w ≤ 1 →
      (1 + p (a + lossA) x + p (a + lossA) w) *
        (1 + p (b + lossB) x + p (b + lossB) w) ≤
          C * (1 + p (a + b + (B + lossA + lossB + 2 * ell + 1)) x +
            p (a + b + (B + lossA + lossB + 2 * ell + 1)) w) := by
  let high : ℕ := a + b + (B + lossA + lossB + 2 * ell + 1)
  let order : Fin 2 → ℕ := ![a + lossA, b + lossB]
  have hhigh : B < high := by dsimp only [high]; omega
  have horder (i : Fin 2) : B < order i → order i + ell < high := by
    fin_cases i <;> simp only [order, Matrix.cons_val_zero', Matrix.cons_val_succ'] <;>
      (dsimp only [high]; omega)
  have hcost : (∑ i : Fin 2, interpolationOrderCost B ell (order i)) ≤ high - B := by
    have h₀ := n04PulledFields_interpolationCost_le B ell (a + lossA)
    have h₁ := n04PulledFields_interpolationCost_le B ell (b + lossB)
    simp only [Fin.sum_univ_two, order, Matrix.cons_val_zero, Matrix.cons_val_one]
    dsimp only [high]
    omega
  obtain ⟨C, hC, hb⟩ := finite_affine_family_interpolation_bound
    p hp B ell high 1 order (fun _ => 1) (fun _ _ => 0)
    hhigh horder hcost hinterp R hR
  refine ⟨C, hC, fun x w hx hw => ?_⟩
  have h := hb x (fun _ : Fin 1 => w) hx (fun _ => hw)
  simp only [Fin.prod_univ_two, Fin.sum_univ_one, order,
    Matrix.cons_val_zero, Matrix.cons_val_one] at h
  exact h

/-- The same low base works for every pair of losses. Only the high
loss depends on them, and it is chosen before the spatial order. -/
theorem n04PulledFields_affine_mixed_product_fixedBase
    (p : ℕ → Seminorm ℝ E) (hp : Monotone p) (hI : HasInterpolation p)
    (requestedBase : ℕ) :
    ∃ B : ℕ, requestedBase ≤ B ∧ ∀ lossA lossB : ℕ, ∃ L : ℕ,
      ∀ R : ℝ, 0 ≤ R → ∀ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ a b : ℕ, a + b ≤ s → ∀ x w : E, p B x ≤ R → p B w ≤ 1 →
        (1 + p (a + lossA) x + p (a + lossA) w) *
          (1 + p (b + lossB) x + p (b + lossB) w) ≤
            C * (1 + p (s + L) x + p (s + L) w) := by
  classical
  obtain ⟨ib, ell, hinterp⟩ := hI
  let B : ℕ := max requestedBase ib
  have hib : ib ≤ B := le_max_right _ _
  refine ⟨B, le_max_left _ _, fun lossA lossB => ?_⟩
  let L : ℕ := B + lossA + lossB + 2 * ell + 1
  refine ⟨L, fun R hR s => ?_⟩
  have hfinite (a b : Fin (s + 1)) :=
    n04PulledFields_affine_product_at_orders p hp B ell lossA lossB
      (fun u v hu huv => hinterp B u v hib hu huv) R hR a.val b.val
  choose C hC hb using hfinite
  let C₀ : ℝ := ∑ a : Fin (s + 1), ∑ b : Fin (s + 1), C a b
  have hC₀ : 0 ≤ C₀ := Finset.sum_nonneg (fun a _ =>
    Finset.sum_nonneg (fun b _ => hC a b))
  refine ⟨C₀, hC₀, fun a b hab x w hx hw => ?_⟩
  let a' : Fin (s + 1) := ⟨a, by omega⟩
  let b' : Fin (s + 1) := ⟨b, by omega⟩
  have hCb : C a' b' ≤ ∑ j : Fin (s + 1), C a' j :=
    Finset.single_le_sum (f := fun j => C a' j)
      (fun j _ => hC a' j) (Finset.mem_univ b')
  have hCa : (∑ j : Fin (s + 1), C a' j) ≤ C₀ :=
    Finset.single_le_sum (f := fun i => ∑ j : Fin (s + 1), C i j)
      (fun i _ => Finset.sum_nonneg (fun j _ => hC i j)) (Finset.mem_univ a')
  have hindex : a + b + L ≤ s + L := Nat.add_le_add_right hab L
  have hhigh : 1 + p (a + b + L) x + p (a + b + L) w ≤
      1 + p (s + L) x + p (s + L) w :=
    add_le_add (add_le_add le_rfl (hp hindex x)) (hp hindex w)
  exact (hb a' b' x w hx hw).trans
    (mul_le_mul (hCb.trans hCa) hhigh (by positivity) hC₀)

end ContinuousFlexibility.Statements
