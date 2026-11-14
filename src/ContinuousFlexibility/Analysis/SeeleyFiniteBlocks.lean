module

public import ContinuousFlexibility.Analysis.SeeleyData
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Finite corrections of reflection moments

Lagrange interpolation gives a finite block whose moments below a prescribed
order vanish. Dilation preserves this cancellation and makes every lower
absolute moment arbitrarily small, while the prescribed moment stays fixed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Finset Polynomial

private def seeleyUnitNode (n : ℕ) (i : Fin (n + 1)) : ℝ := (i : ℕ) + 1

private theorem seeleyUnitNode_one_le (n : ℕ) (i : Fin (n + 1)) :
    1 ≤ seeleyUnitNode n i := by
  dsimp [seeleyUnitNode]
  have hi : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg _
  linarith

private theorem seeleyNegativeNode_injective (n : ℕ) :
    Function.Injective (fun i : Fin (n + 1) => -seeleyUnitNode n i) := by
  intro i j hij
  apply Fin.ext
  have hcast : (i : ℝ) = (j : ℝ) := add_right_cancel (neg_injective hij)
  exact_mod_cast hcast

private def seeleyUnitWeight (n : ℕ) (i : Fin (n + 1)) : ℝ :=
  (∏ j ∈ (univ : Finset (Fin (n + 1))).erase i,
    ((-seeleyUnitNode n i) - (-seeleyUnitNode n j)))⁻¹

private theorem seeleyUnitWeight_moment (n m : ℕ) (hmn : m ≤ n) :
    (∑ i : Fin (n + 1), seeleyUnitWeight n i * (-seeleyUnitNode n i) ^ m) =
      if m = n then 1 else 0 := by
  have hdeg : ((X : ℝ[X]) ^ m).degree <
      ((univ : Finset (Fin (n + 1))).card : WithBot ℕ) := by
    rw [degree_X_pow, card_univ, Fintype.card_fin]
    exact_mod_cast Nat.lt_succ_of_le hmn
  have h := Lagrange.coeff_eq_sum
    (s := (univ : Finset (Fin (n + 1))))
    (v := fun i => -seeleyUnitNode n i)
    (seeleyNegativeNode_injective n).injOn hdeg
  simpa only [card_univ, Fintype.card_fin, Nat.add_sub_cancel_right, coeff_X_pow,
    eval_pow, eval_X, div_eq_mul_inv, seeleyUnitWeight, mul_comm, eq_comm] using h.symm

/-- A finite group of reflection coefficients. -/
structure SeeleyBlock (n : ℕ) where
  a : Fin (n + 1) → ℝ
  b : Fin (n + 1) → ℝ
  one_le_b : ∀ i, 1 ≤ b i

namespace SeeleyBlock

variable {n : ℕ}

def moment (B : SeeleyBlock n) (m : ℕ) : ℝ :=
  ∑ i : Fin (n + 1), B.a i * (-B.b i) ^ m

def absMoment (B : SeeleyBlock n) (m : ℕ) : ℝ :=
  ∑ i : Fin (n + 1), |B.a i| * B.b i ^ m

theorem absMoment_nonneg (B : SeeleyBlock n) (m : ℕ) : 0 ≤ B.absMoment m :=
  Finset.sum_nonneg (fun i _ =>
    mul_nonneg (abs_nonneg _) (pow_nonneg (zero_le_one.trans (B.one_le_b i)) _))

end SeeleyBlock

/-- Correct one moment, preserve all lower moments, and make the absolute
contribution at every lower order as small as prescribed. -/
theorem exists_seeleyBlock (n : ℕ) (r ε : ℝ) (hε : 0 < ε) :
    ∃ B : SeeleyBlock n,
      (∀ m < n, B.moment m = 0) ∧ B.moment n = r ∧
      ∀ m < n, B.absMoment m ≤ ε := by
  let C : ℝ := ∑ i : Fin (n + 1),
    |seeleyUnitWeight n i| * seeleyUnitNode n i ^ n
  let R : ℝ := max 1 (|r| * C / ε)
  have hR : 1 ≤ R := le_max_left _ _
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hscale : |r| * C ≤ ε * R := by
    have h := (div_le_iff₀ hε).mp (le_max_right 1 (|r| * C / ε))
    simpa only [mul_comm] using h
  let B : SeeleyBlock n :=
    { a := fun i => r * seeleyUnitWeight n i / R ^ n
      b := fun i => seeleyUnitNode n i * R
      one_le_b := fun i =>
        one_le_mul_of_one_le_of_one_le (seeleyUnitNode_one_le n i) hR }
  have hmoment (m : ℕ) : B.moment m =
      (r * R ^ m / R ^ n) *
        (∑ i : Fin (n + 1), seeleyUnitWeight n i * (-seeleyUnitNode n i) ^ m) := by
    dsimp only [SeeleyBlock.moment, B]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [show -(seeleyUnitNode n i * R) = (-seeleyUnitNode n i) * R by ring, mul_pow]
    ring
  have habs (m : ℕ) : B.absMoment m =
      (|r| * (∑ i : Fin (n + 1),
        |seeleyUnitWeight n i| * seeleyUnitNode n i ^ m) * R ^ m) / R ^ n := by
    dsimp only [SeeleyBlock.absMoment, B]
    calc
      (∑ i : Fin (n + 1), |r * seeleyUnitWeight n i / R ^ n| *
          (seeleyUnitNode n i * R) ^ m) =
          ∑ i : Fin (n + 1), (|r| * R ^ m / R ^ n) *
            (|seeleyUnitWeight n i| * seeleyUnitNode n i ^ m) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [abs_div, abs_mul, abs_pow, abs_of_pos hRpos, mul_pow]
        ring
      _ = (|r| * R ^ m / R ^ n) *
          (∑ i : Fin (n + 1), |seeleyUnitWeight n i| * seeleyUnitNode n i ^ m) :=
        (Finset.mul_sum _ _ _).symm
      _ = _ := by ring
  refine ⟨B, ?_, ?_, ?_⟩
  · intro m hmn
    rw [hmoment, seeleyUnitWeight_moment n m hmn.le, if_neg hmn.ne, mul_zero]
  · rw [hmoment, seeleyUnitWeight_moment n n le_rfl, if_pos rfl, mul_one]
    exact mul_div_cancel_right₀ r (pow_ne_zero n hRpos.ne')
  · intro m hmn
    rw [habs]
    apply (div_le_iff₀ (pow_pos hRpos n)).mpr
    have hC : (∑ i : Fin (n + 1),
        |seeleyUnitWeight n i| * seeleyUnitNode n i ^ m) ≤ C := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ (seeleyUnitNode_one_le n i) hmn.le) (abs_nonneg _)
    calc
      |r| * (∑ i : Fin (n + 1),
          |seeleyUnitWeight n i| * seeleyUnitNode n i ^ m) * R ^ m ≤
          (ε * R) * R ^ m :=
        mul_le_mul_of_nonneg_right
          ((mul_le_mul_of_nonneg_left hC (abs_nonneg r)).trans hscale)
          (pow_nonneg hRpos.le m)
      _ = ε * R ^ (m + 1) := by rw [pow_succ]; ring
      _ ≤ ε * R ^ n := mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hR (Nat.succ_le_of_lt hmn)) hε.le

end ContinuousFlexibility.Analysis
