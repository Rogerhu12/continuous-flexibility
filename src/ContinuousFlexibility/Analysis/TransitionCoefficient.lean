module

public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith

/-!
# Absorbing an intermediate coefficient by the extra travel distance

Two decaying columns travel through the same intermediate level. Outside
the interval between their endpoints, the sum of the two distances has
an extra term. Slow variation of the coefficient scale pays its cost
from exactly that extra distance, preserving the full endpoint decay.
-/

@[expose] public section

namespace ContinuousFlexibility.Analysis

theorem transition_coefficient_absorb {q s : ℕ → ℝ}
    (hq0 : ∀ n, 0 ≤ q n) (hq : Monotone q) (hs : Monotone s)
    {d C : ℝ} (hd : 0 ≤ d) (hC : 0 ≤ C)
    (hslow : ∀ k m, d * (q m - q k) ≤ 2 * |s k - s m| + C)
    (n k m : ℕ) :
    d * q n - |s k - s n| - |s m - s n| ≤
      C + d * (q k + q m) - |s k - s m| := by
  have hordered (n k m : ℕ) (hkm : k ≤ m) :
      d * q n - |s k - s n| - |s m - s n| ≤
        C + d * (q k + q m) - |s k - s m| := by
    have hdqk : 0 ≤ d * q k := mul_nonneg hd (hq0 k)
    by_cases hnm : n ≤ m
    · have hcost := mul_le_mul_of_nonneg_left (hq hnm) hd
      have htriangle := abs_sub_le (s k) (s n) (s m)
      rw [abs_sub_comm (s n) (s m)] at htriangle
      nlinarith only [hcost, hdqk, htriangle, hC]
    · have hmn : m ≤ n := (Nat.lt_of_not_ge hnm).le
      have hskm := hs hkm
      have hsmn := hs hmn
      have hskn := hs (hkm.trans hmn)
      have hcost := hslow m n
      rw [abs_of_nonpos (sub_nonpos.mpr hsmn)] at hcost
      rw [abs_of_nonpos (sub_nonpos.mpr hskn),
        abs_of_nonpos (sub_nonpos.mpr hsmn),
        abs_of_nonpos (sub_nonpos.mpr hskm)]
      nlinarith only [hcost, hdqk]
  by_cases hkm : k ≤ m
  · exact hordered n k m hkm
  · have h := hordered n m k (Nat.lt_of_not_ge hkm).le
    rw [abs_sub_comm (s m) (s k)] at h
    nlinarith only [h]

end ContinuousFlexibility.Analysis
