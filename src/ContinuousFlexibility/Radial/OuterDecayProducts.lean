module

public import ContinuousFlexibility.Radial.DeepTailPhysicalDecay
public import ContinuousFlexibility.Radial.OuterEnvelope
public import Mathlib.Algebra.BigOperators.Intervals

/-!
# Relative products with the full cubic attenuation exponent

The physical mass-resistance bound gives an estimate for every interval
product, with an explicit constant independent of the starting index.
It retains the coefficient one in the difference of the cubic exponents.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real
open scoped BigOperators
open ContinuousFlexibility.Statements

def outerPhysicalDecayCost (C : ℝ) : ℝ := max 0 (log 8) + C + 3

theorem outerPhysicalDecayCost_nonneg {C : ℝ} (hC : 0 ≤ C) :
    0 ≤ outerPhysicalDecayCost C := by
  dsimp only [outerPhysicalDecayCost]
  positivity

/-- The error in one mass-resistance step is a telescoping coefficient loss. -/
theorem outer_physical_decay_factor_le {C q : ℝ} (hC : 0 ≤ C) (n : ℕ)
    (hq : exp (2 * (n : ℝ) ^ 2 -
      C * ((n : ℝ) ^ (3 / 2 : ℝ) + n)) ≤ q) :
    8 / q ≤ exp (-(radialS (n + 1) - radialS n) +
      outerPhysicalDecayCost C *
        (((n + 1 : ℕ) : ℝ) ^ (5 / 2 : ℝ) - (n : ℝ) ^ (5 / 2 : ℝ))) := by
  calc
    8 / q ≤ 8 / exp (2 * (n : ℝ) ^ 2 -
        C * ((n : ℝ) ^ (3 / 2 : ℝ) + n)) :=
      div_le_div_of_nonneg_left (by norm_num) (exp_pos _) hq
    _ = exp (log 8 - (2 * (n : ℝ) ^ 2 -
        C * ((n : ℝ) ^ (3 / 2 : ℝ) + n))) := by
      symm
      rw [exp_sub, exp_log (by norm_num : (0 : ℝ) < 8)]
    _ ≤ _ := by
      apply exp_le_exp.mpr
      have h := physicalDecay_exponent_step (by norm_num : (0 : ℝ) < 8) hC n
      dsimp only [outerPhysicalDecayCost]
      convert h using 1 <;> ring

/-- Finite products preserve the full difference of the cubic exponents. -/
theorem outer_physical_decay_product {q : ℕ → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (start : ℕ)
    (hq : ∀ k, exp (2 * ((start + k : ℕ) : ℝ) ^ 2 -
      C * (((start + k : ℕ) : ℝ) ^ (3 / 2 : ℝ) + (start + k : ℕ))) ≤ q k)
    {m n : ℕ} (hmn : m ≤ n) :
    (∏ k ∈ Finset.Ico m n, 8 / q k) ≤
      exp (-(radialS (start + n) - radialS (start + m)) +
        outerPhysicalDecayCost C *
          (((start + n : ℕ) : ℝ) ^ (5 / 2 : ℝ) -
            ((start + m : ℕ) : ℝ) ^ (5 / 2 : ℝ))) := by
  induction n, hmn using Nat.le_induction with
  | base => simp
  | succ n hmn ih =>
      rw [Finset.prod_Ico_succ_top hmn]
      have hqpos : 0 < q n := (exp_pos _).trans_le (hq n)
      calc
        _ ≤ exp (-(radialS (start + n) - radialS (start + m)) +
              outerPhysicalDecayCost C *
                (((start + n : ℕ) : ℝ) ^ (5 / 2 : ℝ) -
                  ((start + m : ℕ) : ℝ) ^ (5 / 2 : ℝ))) *
            exp (-(radialS (start + n + 1) - radialS (start + n)) +
              outerPhysicalDecayCost C *
                (((start + n + 1 : ℕ) : ℝ) ^ (5 / 2 : ℝ) -
                  ((start + n : ℕ) : ℝ) ^ (5 / 2 : ℝ))) :=
          mul_le_mul ih (outer_physical_decay_factor_le hC (start + n) (hq n))
            (div_nonneg (by norm_num) hqpos.le) (exp_pos _).le
        _ = _ := by
          rw [← exp_add]
          congr 1
          simp only [Nat.add_assoc]
          ring

/-- The relative product is controlled by the actual coefficient envelope. -/
theorem outer_physical_decay_product_envelope {q : ℕ → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (start : ℕ)
    (hq : ∀ k, exp (2 * ((start + k : ℕ) : ℝ) ^ 2 -
      C * (((start + k : ℕ) : ℝ) ^ (3 / 2 : ℝ) + (start + k : ℕ))) ≤ q k)
    {m n : ℕ} (hmn : m ≤ n) :
    (∏ k ∈ Finset.Ico m n, 8 / q k) ≤
      radialE (start + n) ^ outerPhysicalDecayCost C *
        exp (-|radialS (start + n) - radialS (start + m)|) := by
  apply (outer_physical_decay_product hC start hq hmn).trans
  rw [abs_of_nonneg (sub_nonneg.mpr
    (radialS_monotone (Nat.add_le_add_left hmn start))), outer_radialE_rpow, ← exp_add]
  apply exp_le_exp.mpr
  have hQ : ((start + n : ℕ) : ℝ) ^ (5 / 2 : ℝ) ≤ radialQ (start + n) := by
    unfold radialQ
    exact le_mul_of_one_le_right (rpow_nonneg (Nat.cast_nonneg _) _)
      (ssv_one_le_log (Nat.cast_nonneg _))
  have hc := outerPhysicalDecayCost_nonneg hC
  have hmul := mul_le_mul_of_nonneg_left hQ hc
  have hbase := mul_nonneg hc
    (rpow_nonneg (Nat.cast_nonneg (start + m)) (5 / 2 : ℝ))
  linarith

end ContinuousFlexibility.Radial
