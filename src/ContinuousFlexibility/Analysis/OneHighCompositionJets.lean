module

public import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
public import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# The actual higher derivatives in smooth composition

The finite sums below come from the chain rule for the actual derivatives.
Every block has positive size and the block sizes add up to the total order.
Consequently the derivative products are precisely of the form needed by the
one-high-factor product estimate, including for a multivariate outer function.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open scoped BigOperators ContDiff

variable {E F K : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup K] [NormedSpace ℝ K]

/-- The full partition estimate retains the order of each input derivative;
no high derivative has been hidden in a uniform low-order constant. -/
theorem norm_iteratedFDeriv_comp_le_partition_sum {Φ : F → K} {v : E → F} {x : E}
    (hΦ : ContDiffAt ℝ ∞ Φ (v x)) (hv : ContDiffAt ℝ ∞ v x) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (Φ ∘ v) x‖ ≤
      ∑ c : OrderedFinpartition n,
        ‖iteratedFDeriv ℝ c.length Φ (v x)‖ *
          ∏ j, ‖iteratedFDeriv ℝ (c.partSize j) v x‖ := by
  classical
  calc
    _ = ‖∑ c : OrderedFinpartition n,
        c.compAlongOrderedFinpartition (iteratedFDeriv ℝ c.length Φ (v x))
          (fun j => iteratedFDeriv ℝ (c.partSize j) v x)‖ :=
      congrArg norm (iteratedFDeriv_comp hΦ hv (by simp : (n : ℕ∞ω) ≤ ∞))
    _ ≤ ∑ c : OrderedFinpartition n,
        ‖c.compAlongOrderedFinpartition (iteratedFDeriv ℝ c.length Φ (v x))
          (fun j => iteratedFDeriv ℝ (c.partSize j) v x)‖ := norm_sum_le _ _
    _ ≤ _ := Finset.sum_le_sum fun c _ => c.norm_compAlongOrderedFinpartition_le _ _

/-- A bound on the outer derivatives is used only at the input value.
Control along the segment to zero is needed separately for the zeroth term. -/
theorem norm_iteratedFDeriv_comp_le_bounded_partition_sum
    {Φ : F → K} {v : E → F} {x : E}
    (hΦ : ContDiffAt ℝ ∞ Φ (v x)) (hv : ContDiffAt ℝ ∞ v x)
    {n : ℕ} (hn : 0 < n) {B : ℕ → ℝ}
    (hB : ∀ m, 1 ≤ m → m ≤ n → ‖iteratedFDeriv ℝ m Φ (v x)‖ ≤ B m) :
    ‖iteratedFDeriv ℝ n (Φ ∘ v) x‖ ≤
      ∑ c : OrderedFinpartition n, B c.length *
        ∏ j, ‖iteratedFDeriv ℝ (c.partSize j) v x‖ := by
  apply (norm_iteratedFDeriv_comp_le_partition_sum hΦ hv n).trans
  apply Finset.sum_le_sum
  intro c _
  exact mul_le_mul_of_nonneg_right (hB c.length (c.length_pos hn) c.length_le)
    (Finset.prod_nonneg fun _ _ => norm_nonneg _)

/-- Scalar specialization of the partition formula, retaining the exact
ordinary derivative orders needed on a circle. -/
theorem norm_iteratedDeriv_comp_le_partition_sum {Φ v : ℝ → ℝ} {x : ℝ}
    (hΦ : ContDiffAt ℝ ∞ Φ (v x)) (hv : ContDiffAt ℝ ∞ v x) (n : ℕ) :
    ‖iteratedDeriv n (Φ ∘ v) x‖ ≤
      ∑ c : OrderedFinpartition n,
        ‖iteratedDeriv c.length Φ (v x)‖ * ∏ j, ‖iteratedDeriv (c.partSize j) v x‖ := by
  classical
  rw [iteratedDeriv_comp_eq_sum_orderedFinpartition hΦ hv (by simp : (n : ℕ∞ω) ≤ ∞)]
  apply (norm_sum_le _ _).trans
  exact le_of_eq (Finset.sum_congr rfl fun _ _ => by rw [norm_mul, norm_prod])

/-- The sizes of the blocks in every actual chain-rule summand add up to
the derivative order. -/
theorem oneHighPartition_sum_orders {n : ℕ} (c : OrderedFinpartition n) :
    ∑ j, c.partSize j = n := by
  have h := c.sum_sigma_eq_sum (fun _ : Fin n => (1 : ℕ))
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    mul_one] using h

end ContinuousFlexibility.Analysis
