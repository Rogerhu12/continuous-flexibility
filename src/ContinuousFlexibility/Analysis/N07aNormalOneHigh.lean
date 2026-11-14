module

public import ContinuousFlexibility.Analysis.N07aNormalExpansionBound

/-!
# One high factor in a terminal-jet product

The terminal solution or source jet has its own low and high norms. The
coefficient factors have a bounded low norm and one shared high state
size. Interpolation with total exponent at most one leaves precisely a
high terminal term or a high coefficient term times the low terminal.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open scoped BigOperators

theorem n07a_oneHigh_terminal_product {n : ℕ} {low high state : ℝ}
    (hlow : 0 ≤ low) (hhigh : low ≤ high) (hstate : 1 ≤ state)
    (θ : Fin (n + 1) → ℝ) (hθ : ∀ i, 0 ≤ θ i ∧ θ i < 1)
    (hsum : ∑ i, θ i ≤ 1) :
    (low ^ (1 - θ 0) * high ^ θ 0) * (∏ i : Fin n, state ^ θ i.succ) ≤
      high + (n : ℝ) * state * low := by
  classical
  let lo : Fin (n + 1) → ℝ := fun i => if i = 0 then low else 1
  let hi : Fin (n + 1) → ℝ := fun i => if i = 0 then high else state
  have hlo (i : Fin (n + 1)) : 0 ≤ lo i := by
    dsimp only [lo]
    split <;> first | exact hlow | exact zero_le_one
  have hhi (i : Fin (n + 1)) : lo i ≤ hi i := by
    dsimp only [lo, hi]
    split <;> first | exact hhigh | exact hstate
  have h := spaces_prod_interpolation_one_high Finset.univ Finset.univ_nonempty
    lo hi θ (fun i _ => hlo i) (fun i _ => hhi i) (fun i _ => hθ i) hsum
  have hleft : (∏ i, lo i ^ (1 - θ i) * hi i ^ θ i) =
      (low ^ (1 - θ 0) * high ^ θ 0) * (∏ i : Fin n, state ^ θ i.succ) := by
    simp [Fin.prod_univ_succ, lo, hi]
  have hright : (∑ i, hi i * ∏ j ∈ Finset.univ.erase i, lo j) =
      high + (n : ℝ) * state * low := by
    have hzero (i : Fin n) : (0 : Fin (n + 1)) ≠ i.succ := by
      intro h
      have hv := congrArg Fin.val h
      simp at hv
    simp [Fin.sum_univ_succ, lo, hi, Finset.prod_ite_eq', hzero, mul_assoc]
  rwa [hleft, hright] at h

end ContinuousFlexibility.Analysis
