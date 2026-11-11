import ContinuousFlexibility.Analysis.OneHighCompositionJets
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# A linear highest-jet bound in the actual chain rule

In the Faà di Bruno formula, a partition with one block contributes the
highest inner derivative linearly. Every other block size is strictly
smaller than the total order. This is the triangular structure used to
bound the low flow jets from an integral of speed derivatives.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open scoped BigOperators ContDiff

private theorem circleFlow_partSize_lt {n : ℕ} (c : OrderedFinpartition n)
    (hc : 1 < c.length) (i : Fin c.length) : c.partSize i < n := by
  classical
  obtain ⟨j, hji⟩ : ∃ j : Fin c.length, j ≠ i := by
    by_cases hi : i.val = 0
    · refine ⟨⟨1, hc⟩, ?_⟩
      intro he
      have hh := congrArg Fin.val he
      simp only [Fin.val_mk] at hh
      omega
    · refine ⟨⟨0, by omega⟩, ?_⟩
      intro he
      have hh := congrArg Fin.val he
      simp only [Fin.val_mk] at hh
      omega
  have hsum := Finset.sum_erase_add (s := Finset.univ) (f := c.partSize) (Finset.mem_univ i)
  have hj : c.partSize j ≤ ∑ k ∈ Finset.univ.erase i, c.partSize k :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩)
  have htotal := oneHighPartition_sum_orders c
  have hpos := c.partSize_pos j
  omega

private theorem circleFlow_prod_partition_one {n : ℕ} (c : OrderedFinpartition n)
    (hc : c.length = 1) (v : ℕ → ℝ) : (∏ j, v (c.partSize j)) = v n := by
  classical
  letI : Unique (Fin c.length) :=
    { default := ⟨0, by omega⟩
      uniq := fun j => Fin.ext (by have hj := j.isLt; omega) }
  have hsize : c.partSize default = n := by
    simpa only [Fintype.sum_unique] using oneHighPartition_sum_orders c
  simp only [Fintype.prod_unique, hsize]

/-- The highest inner derivative occurs linearly; the other factors are
bounded using derivatives of strictly smaller order. -/
theorem circleFlow_norm_iteratedDeriv_comp_le_linear_top
    {g h : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hh : ContDiff ℝ ∞ h)
    {n : ℕ} (hn : 0 < n) {B K : ℝ} (hB : 0 ≤ B) (hK : 1 ≤ K)
    (houter : ∀ j : ℕ, 1 ≤ j → j ≤ n → ∀ x : ℝ, ‖iteratedDeriv j g x‖ ≤ B)
    (hinner : ∀ j : ℕ, 1 ≤ j → j < n → ∀ x : ℝ, ‖iteratedDeriv j h x‖ ≤ K)
    (x : ℝ) :
    ‖iteratedDeriv n (g ∘ h) x‖ ≤
      (Fintype.card (OrderedFinpartition n) : ℝ) * B *
        (‖iteratedDeriv n h x‖ + K ^ n) := by
  classical
  apply (norm_iteratedDeriv_comp_le_partition_sum hg.contDiffAt hh.contDiffAt n).trans
  have hKnonneg : 0 ≤ K := zero_le_one.trans hK
  have hproduct (c : OrderedFinpartition n) :
      (∏ j, ‖iteratedDeriv (c.partSize j) h x‖) ≤ ‖iteratedDeriv n h x‖ + K ^ n := by
    by_cases hc : c.length = 1
    · rw [circleFlow_prod_partition_one c hc (fun d => ‖iteratedDeriv d h x‖)]
      exact le_add_of_nonneg_right (pow_nonneg hKnonneg n)
    · have hlength : 1 < c.length := by have hp := c.length_pos hn; omega
      have hb : (∏ j, ‖iteratedDeriv (c.partSize j) h x‖) ≤ K ^ c.length := by
        calc
          _ ≤ ∏ _j : Fin c.length, K := Finset.prod_le_prod₀
            (fun _ _ => norm_nonneg _) (fun j _ =>
              hinner (c.partSize j) (c.partSize_pos j) (circleFlow_partSize_lt c hlength j) x)
          _ = _ := by simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      exact (hb.trans (pow_le_pow_right₀ hK c.length_le)).trans
        (le_add_of_nonneg_left (norm_nonneg _))
  calc
    (∑ c : OrderedFinpartition n,
        ‖iteratedDeriv c.length g (h x)‖ * ∏ j, ‖iteratedDeriv (c.partSize j) h x‖) ≤
        ∑ _c : OrderedFinpartition n, B * (‖iteratedDeriv n h x‖ + K ^ n) := by
      apply Finset.sum_le_sum
      intro c _
      exact mul_le_mul (houter c.length (c.length_pos hn) c.length_le (h x))
        (hproduct c) (Finset.prod_nonneg fun _ _ => norm_nonneg _) hB
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

/-- A cumulative bound for the first `n` flow jets. Its input is the
integral of a common envelope for the first `n` speed derivatives. -/
def circleFlowJetBound : ℕ → ℝ → ℝ
  | 0, _ => 1
  | n + 1, L => circleFlowJetBound n L +
      (1 + (Fintype.card (OrderedFinpartition (n + 1)) : ℝ) *
        circleFlowJetBound n L ^ (n + 1) * L) *
        Real.exp ((Fintype.card (OrderedFinpartition (n + 1)) : ℝ) * L)

theorem circleFlowJetBound_one_le (n : ℕ) {L : ℝ} (hL : 0 ≤ L) :
    1 ≤ circleFlowJetBound n L := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    rw [circleFlowJetBound]
    have hk : 0 ≤ circleFlowJetBound n L := zero_le_one.trans ih
    have hnonneg : 0 ≤ (1 + (Fintype.card (OrderedFinpartition (n + 1)) : ℝ) *
        circleFlowJetBound n L ^ (n + 1) * L) *
        Real.exp ((Fintype.card (OrderedFinpartition (n + 1)) : ℝ) * L) := by positivity
    linarith

theorem circleFlowJetBound_le_succ (n : ℕ) {L : ℝ} (hL : 0 ≤ L) :
    circleFlowJetBound n L ≤ circleFlowJetBound (n + 1) L := by
  rw [circleFlowJetBound]
  have hk : 0 ≤ circleFlowJetBound n L := zero_le_one.trans (circleFlowJetBound_one_le n hL)
  exact le_add_of_nonneg_right (by positivity)

end ContinuousFlexibility.Analysis
