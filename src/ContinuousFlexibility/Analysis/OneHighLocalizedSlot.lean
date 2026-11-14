module

public import ContinuousFlexibility.Statements.Nonlinear
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Keeping one localized slot separate in the N01 one-high expression

On the unit low-seminorm box for the other directions, the localized
slot occurs either at the low order or at the high order. This preserves
the two different derivative budgets needed by weighted localization.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open scoped BigOperators

theorem oneHighVariationWeight_snoc_le_of_low_le_one
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (base high : ℕ) (x : E)
    {n : ℕ} (v : Fin n → E) (w : E)
    (hv : ∀ i, p base (v i) ≤ 1) :
    oneHighVariationWeight p base high x (Fin.snoc v w) ≤
      (1 + p high x + ∑ i : Fin n, p high (v i)) * p base w + p high w := by
  classical
  let u : Fin (n + 1) → E := Fin.snoc v w
  have hcast (i : Fin n) : u i.castSucc = v i := Fin.snoc_castSucc _ _ i
  have hlast : u (Fin.last n) = w := Fin.snoc_last _ _
  have hlow (i : Fin (n + 1)) (hi : i ≠ Fin.last n) : p base (u i) ≤ 1 := by
    cases i using Fin.lastCases with
    | last => exact (hi rfl).elim
    | cast j => rw [hcast]; exact hv j
  have hp : (∏ i : Fin (n + 1), p base (u i)) ≤ p base w := by
    rw [Fin.prod_univ_castSucc]
    simp only [hcast, hlast]
    exact mul_le_of_le_one_left (apply_nonneg _ _)
      (Finset.prod_le_one₀ (fun _ _ => apply_nonneg _ _) (fun i _ => hv i))
  have he (i : Fin n) :
      (∏ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i.castSucc, p base (u j)) ≤
        p base w := by
    let A : Finset (Fin (n + 1)) := Finset.univ.erase i.castSucc
    have hn : Fin.last n ≠ i.castSucc := by
      intro h
      have hh := congrArg Fin.val h
      simp only [Fin.val_last, Fin.val_castSucc] at hh
      omega
    have hm : Fin.last n ∈ A := Finset.mem_erase.mpr ⟨hn, Finset.mem_univ _⟩
    have hrest : (∏ j ∈ A.erase (Fin.last n), p base (u j)) ≤ 1 :=
      Finset.prod_le_one₀ (fun _ _ => apply_nonneg _ _)
        (fun j hj => hlow j (Finset.mem_erase.mp hj).1)
    calc
      _ = p base (u (Fin.last n)) * ∏ j ∈ A.erase (Fin.last n), p base (u j) :=
        (Finset.mul_prod_erase A (fun j => p base (u j)) hm).symm
      _ ≤ p base (u (Fin.last n)) * 1 :=
        mul_le_mul_of_nonneg_left hrest (apply_nonneg _ _)
      _ = p base w := by rw [hlast, mul_one]
  have helast :
      (∏ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase (Fin.last n), p base (u j)) ≤ 1 :=
    Finset.prod_le_one₀ (fun _ _ => apply_nonneg _ _)
      (fun j hj => hlow j (Finset.mem_erase.mp hj).1)
  have hfirst : (1 + p high x) * (∏ i : Fin (n + 1), p base (u i)) ≤
      (1 + p high x) * p base w :=
    mul_le_mul_of_nonneg_left hp (add_nonneg zero_le_one (apply_nonneg _ _))
  have hsum : (∑ i : Fin n, p high (u i.castSucc) *
      ∏ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i.castSucc, p base (u j)) ≤
      ∑ i : Fin n, p high (v i) * p base w := by
    apply Finset.sum_le_sum
    intro i _
    rw [hcast]
    exact mul_le_mul_of_nonneg_left (he i) (apply_nonneg _ _)
  have hlastterm : p high (u (Fin.last n)) *
      (∏ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase (Fin.last n), p base (u j)) ≤
      p high w := by
    rw [hlast]
    exact mul_le_of_le_one_right (apply_nonneg _ _) helast
  change oneHighVariationWeight p base high x u ≤ _
  rw [oneHighVariationWeight, Fin.sum_univ_castSucc]
  exact (add_le_add hfirst (add_le_add hsum hlastterm)).trans_eq (by
    rw [← Finset.sum_mul]
    ring)

end ContinuousFlexibility.Statements
