import ContinuousFlexibility.Radial.TailNaturalNodeLine

/-!
# Continuous natural node data

The uniform continued-fraction limit gives continuous exact node ratios.
Finite products of these ratios then select the node solution with value
one at the first node, continuously in the product topology on parameters.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set

/-- The exact ratio of consecutive positive natural node values. -/
def tailNaturalNodeRatio (b c : ℕ → ℝ)
    (hε : ∀ n, c n ^ 2 / (b n * b (n + 1)) ∈ Icc 0 (1 / 8)) (n : ℕ) : ℝ :=
  c n / b (n + 1) *
    tailFractionLimit (fun j => c j ^ 2 / (b j * b (j + 1))) hε n

theorem tailNaturalNodeRatio_pos {b c : ℕ → ℝ}
    (hb : ∀ n, 0 < b n) (hc : ∀ n, 0 < c n)
    (hε : ∀ n, c n ^ 2 / (b n * b (n + 1)) ∈ Icc 0 (1 / 8)) (n : ℕ) :
    0 < tailNaturalNodeRatio b c hε n := by
  exact mul_pos (div_pos (hc n) (hb (n + 1)))
    (zero_lt_one.trans_le (tailFractionLimit_mem _ hε n).1)

theorem continuous_tailNaturalNodeRatio {P : Type*} [TopologicalSpace P]
    (b c : P → ℕ → ℝ) (hb : ∀ p n, b p n ≠ 0)
    (hε : ∀ p n, c p n ^ 2 / (b p n * b p (n + 1)) ∈ Icc 0 (1 / 8))
    (hbcont : ∀ n, Continuous (fun p => b p n))
    (hccont : ∀ n, Continuous (fun p => c p n)) (n : ℕ) :
    Continuous (fun p => tailNaturalNodeRatio (b p) (c p) (hε p) n) := by
  have hcoeff (j : ℕ) :
      Continuous (fun p => c p j ^ 2 / (b p j * b p (j + 1))) :=
    ((hccont j).pow 2).div ((hbcont j).mul (hbcont (j + 1)))
      (fun p => mul_ne_zero (hb p j) (hb p (j + 1)))
  exact ((hccont n).div (hbcont (n + 1)) (fun p => hb p (n + 1))).mul
    (continuous_tailFractionLimit _ hε hcoeff n)

/-- A node sequence is fixed by its first value and its consecutive ratios. -/
def tailNodesFromRatio (r : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => r n * tailNodesFromRatio r n

@[simp] theorem tailNodesFromRatio_zero (r : ℕ → ℝ) : tailNodesFromRatio r 0 = 1 := rfl

theorem tailNodesFromRatio_succ (r : ℕ → ℝ) (n : ℕ) :
    tailNodesFromRatio r (n + 1) = r n * tailNodesFromRatio r n := rfl

theorem tailNodesFromRatio_pos {r : ℕ → ℝ} (hr : ∀ n, 0 < r n) (n : ℕ) :
    0 < tailNodesFromRatio r n := by
  induction n with
  | zero => exact zero_lt_one
  | succ n ih => exact mul_pos (hr n) ih

theorem continuous_tailNodesFromRatio {P : Type*} [TopologicalSpace P]
    (r : P → ℕ → ℝ) (hr : ∀ n, Continuous (fun p => r p n)) (n : ℕ) :
    Continuous (fun p => tailNodesFromRatio (r p) n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih => exact (hr n).mul ih

theorem tailNodesFromRatio_unique {r y : ℕ → ℝ} (hy₀ : y 0 = 1)
    (hy : ∀ n, y (n + 1) = r n * y n) : y = tailNodesFromRatio r := by
  funext n
  induction n with
  | zero => exact hy₀
  | succ n ih => rw [hy n, ih, tailNodesFromRatio_succ]

/-- In the parameter-dependent Jacobi equation, every fixed node of the
entrance-normalized natural sequence is a continuous scalar function. -/
theorem continuous_tailNaturalNodes {P : Type*} [TopologicalSpace P]
    (b c : P → ℕ → ℝ) (hb : ∀ p n, b p n ≠ 0)
    (hε : ∀ p n, c p n ^ 2 / (b p n * b p (n + 1)) ∈ Icc 0 (1 / 8))
    (hbcont : ∀ n, Continuous (fun p => b p n))
    (hccont : ∀ n, Continuous (fun p => c p n)) (n : ℕ) :
    Continuous (fun p => tailNodesFromRatio
      (tailNaturalNodeRatio (b p) (c p) (hε p)) n) :=
  continuous_tailNodesFromRatio _
    (continuous_tailNaturalNodeRatio b c hb hε hbcont hccont) n

end ContinuousFlexibility.Radial
