import ContinuousFlexibility.Scalar.WeightedTowerCalculus
import Mathlib.Algebra.BigOperators.Fin

/-!
# Finite one-high costs on a fixed neighbourhood

These identities separate one coefficient factor from the directional
factors. The coefficient's low norm is bounded uniformly on the domain;
its high norm contributes exactly one high base-point term.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open ContinuousFlexibility.Analysis
open scoped BigOperators

private theorem fin_prod_erase_eq_ite {n : ℕ} (f : Fin n → ℝ) (i : Fin n) :
    (∏ j ∈ Finset.univ.erase i, f j) = ∏ j, if j = i then 1 else f j := by
  classical
  symm
  rw [← Finset.mul_prod_erase Finset.univ (fun j => if j = i then (1 : ℝ) else f j)
    (Finset.mem_univ i)]
  simp only [ite_true, one_mul]
  apply Finset.prod_congr rfl
  intro j hj
  rw [if_neg (Finset.mem_erase.mp hj).1]

private theorem fin_prod_erase_cons_zero {E : Type*} {n : ℕ}
    (L : E → ℝ) (x : E) (v : Fin n → E) :
    (∏ j ∈ Finset.univ.erase (0 : Fin (n + 1)), L (Fin.cons x v j)) =
      ∏ j, L (v j) := by
  rw [fin_prod_erase_eq_ite, Fin.prod_univ_succ]
  simp

private theorem fin_prod_erase_cons_succ {E : Type*} {n : ℕ}
    (L : E → ℝ) (x : E) (v : Fin n → E) (i : Fin n) :
    (∏ j ∈ Finset.univ.erase i.succ, L (Fin.cons x v j)) =
      L x * ∏ j ∈ Finset.univ.erase i, L (v j) := by
  rw [fin_prod_erase_eq_ite, Fin.prod_univ_succ, fin_prod_erase_eq_ite]
  simp

theorem scalarOneHighCost_cons {E : Type*} {n : ℕ}
    (L H : E → ℝ) (x : E) (v : Fin n → E) :
    (∑ i : Fin (n + 1), H (Fin.cons x v i) *
      ∏ j ∈ Finset.univ.erase i, L (Fin.cons x v j)) =
      H x * (∏ i, L (v i)) +
        L x * ∑ i, H (v i) * ∏ j ∈ Finset.univ.erase i, L (v j) := by
  rw [Fin.sum_univ_succ, fin_prod_erase_cons_zero]
  simp only [Fin.cons_zero, Fin.cons_succ, fin_prod_erase_cons_succ]
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem scalarOneHighCost_mono {E : Type*} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p)
    {b b' h h' n : ℕ} (hb : b ≤ b') (hh : h ≤ h') (v : Fin n → E) :
    (∑ i, p h (v i) * ∏ j ∈ Finset.univ.erase i, p b (v j)) ≤
      ∑ i, p h' (v i) * ∏ j ∈ Finset.univ.erase i, p b' (v j) := by
  classical
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul (hp hh (v i))
    (Finset.prod_le_prod₀ (fun j _ => apply_nonneg _ _) (fun j _ => hp hb (v j)))
    (Finset.prod_nonneg (fun j _ => apply_nonneg _ _)) (apply_nonneg _ _)

theorem scalarOneHighCost_le_tameJetSize
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p)
    {b h base loss s k : ℕ} (hb : b ≤ base) (hh : h ≤ s + loss)
    (x : E) (v : Fin k → E) :
    (∑ i, p h (v i) * ∏ j ∈ Finset.univ.erase i, p b (v j)) ≤
      tameJetSize p k s loss base x v := by
  apply (scalarOneHighCost_mono hp hb hh v).trans
  exact le_add_of_nonneg_left (mul_nonneg
    (by linarith only [apply_nonneg (p (s + loss)) x])
    (Finset.prod_nonneg (fun i _ => apply_nonneg _ _)))

/-- Separate the single coefficient factor, increasing the common directional
base and high order once. The coefficient bounds need not be homogeneous. -/
theorem scalarOneHighCost_cons_le_tameJetSize
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p)
    {b h base loss s k : ℕ} (hb : b ≤ base) (hh : h ≤ s + loss)
    {Cₕ Cₗ : ℝ} (hCₕ : 0 ≤ Cₕ) (hCₗ : 0 ≤ Cₗ)
    (x g : E) (v : Fin k → E)
    (hgHigh : p h g ≤ Cₕ * (1 + p (s + loss) x))
    (hgLow : p b g ≤ Cₗ) :
    (∑ i : Fin (k + 1), p h (Fin.cons g v i) *
        ∏ j ∈ Finset.univ.erase i, p b (Fin.cons g v j)) ≤
      (Cₕ + Cₗ) * tameJetSize p k s loss base x v := by
  classical
  rw [scalarOneHighCost_cons]
  let X : ℝ := (1 + p (s + loss) x) * ∏ i, p base (v i)
  let Y : ℝ := ∑ i, p (s + loss) (v i) *
    ∏ j ∈ Finset.univ.erase i, p base (v j)
  have hX : 0 ≤ X := mul_nonneg
    (by linarith only [apply_nonneg (p (s + loss)) x])
    (Finset.prod_nonneg (fun i _ => apply_nonneg _ _))
  have hY : 0 ≤ Y := Finset.sum_nonneg (fun i _ =>
    mul_nonneg (apply_nonneg _ _) (Finset.prod_nonneg (fun j _ => apply_nonneg _ _)))
  have hhead : p h g * (∏ i, p b (v i)) ≤ Cₕ * X := by
    calc
      _ ≤ (Cₕ * (1 + p (s + loss) x)) * (∏ i, p base (v i)) :=
        mul_le_mul hgHigh
          (Finset.prod_le_prod₀ (fun i _ => apply_nonneg _ _) (fun i _ => hp hb (v i)))
          (Finset.prod_nonneg (fun i _ => apply_nonneg _ _))
          (mul_nonneg hCₕ (by linarith only [apply_nonneg (p (s + loss)) x]))
      _ = _ := by dsimp [X]; ring
  have htail : p b g * (∑ i, p h (v i) *
      ∏ j ∈ Finset.univ.erase i, p b (v j)) ≤ Cₗ * Y :=
    mul_le_mul hgLow (scalarOneHighCost_mono hp hb hh v)
      (Finset.sum_nonneg (fun i _ =>
        mul_nonneg (apply_nonneg _ _) (Finset.prod_nonneg (fun j _ => apply_nonneg _ _)))) hCₗ
  calc
    _ ≤ Cₕ * X + Cₗ * Y := add_le_add hhead htail
    _ ≤ (Cₕ + Cₗ) * (X + Y) := by
      nlinarith only [mul_nonneg hCₕ hY, mul_nonneg hCₗ hX]
    _ = _ := rfl

end ContinuousFlexibility.Statements
