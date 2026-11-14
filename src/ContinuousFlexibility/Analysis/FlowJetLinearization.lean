module

public import ContinuousFlexibility.Analysis.OneHighCompositionJets
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Lean.Elab.Tactic.Omega

/-!
# Removing the linear part in the actual higher chain rule

At a fixed base point the remainder after subtracting the actual
Fréchet derivative has zero first derivative. Its higher derivatives
equal the original field derivatives. Thus its actual composition
formula involves only partitions with at least two blocks.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open scoped BigOperators ContDiff

variable {E F K : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup K] [NormedSpace ℝ K]

theorem flowJet_iteratedFDeriv_clm_eq_zero (L : E →L[ℝ] F)
    {n : ℕ} (hn : 2 ≤ n) (x : E) :
    iteratedFDeriv ℝ n (L : E → F) x = 0 := by
  apply norm_eq_zero.mp
  cases n with
  | zero => omega
  | succ n =>
    cases n with
    | zero => omega
    | succ n =>
      rw [← norm_iteratedFDeriv_fderiv]
      have he : fderiv ℝ (L : E → F) = fun _ => L :=
        funext (fun _ => L.fderiv)
      rw [he, iteratedFDeriv_succ_const]
      simp only [Pi.zero_apply, norm_zero]

theorem flowJet_norm_iteratedFDeriv_clm_le (L : E →L[ℝ] F)
    {n : ℕ} (hn : 1 ≤ n) (x : E) :
    ‖iteratedFDeriv ℝ n (L : E → F) x‖ ≤ ‖L‖ := by
  by_cases h1 : n = 1
  · subst n
    rw [norm_iteratedFDeriv_one, L.fderiv]
  · rw [flowJet_iteratedFDeriv_clm_eq_zero L (by omega), norm_zero]
    exact norm_nonneg L

/-- Subtracting the true linearization removes exactly the one-block
partitions. No candidate derivative tower is used. -/
theorem flowJet_linearization_remainder_bound_at
    {g : F → K} {h : E → F} {x : E}
    (hg : ContDiffAt ℝ ∞ g (h x)) (hh : ContDiffAt ℝ ∞ h x)
    {n : ℕ} (hn : 0 < n) :
    ‖iteratedFDeriv ℝ n
        ((g - (fderiv ℝ g (h x) : F → K)) ∘ h) x‖ ≤
      ∑ c : OrderedFinpartition n,
        if 2 ≤ c.length then
          ‖iteratedFDeriv ℝ c.length g (h x)‖ *
            ∏ j, ‖iteratedFDeriv ℝ (c.partSize j) h x‖
        else 0 := by
  classical
  let L : F →L[ℝ] K := fderiv ℝ g (h x)
  let R : F → K := g - (L : F → K)
  have hR : ContDiffAt ℝ ∞ R (h x) := hg.sub L.contDiff.contDiffAt
  have hdR : HasFDerivAt R (L - L) (h x) :=
    (hg.differentiableAt (by simp)).hasFDerivAt.sub L.hasFDerivAt
  have hRone : ‖iteratedFDeriv ℝ 1 R (h x)‖ = 0 := by
    rw [norm_iteratedFDeriv_one, hdR.fderiv, sub_self, norm_zero]
  have hRhigher (k : ℕ) (hk : 2 ≤ k) :
      iteratedFDeriv ℝ k R (h x) = iteratedFDeriv ℝ k g (h x) := by
    change iteratedFDeriv ℝ k (g - (L : F → K)) (h x) = _
    rw [iteratedFDeriv_sub_apply
      (hg.of_le (by simp : (k : ℕ∞ω) ≤ ∞))
      L.contDiff.contDiffAt, flowJet_iteratedFDeriv_clm_eq_zero L hk, sub_zero]
  apply (norm_iteratedFDeriv_comp_le_partition_sum hR hh n).trans
  apply Finset.sum_le_sum
  intro c _
  by_cases hc : 2 ≤ c.length
  · rw [if_pos hc, hRhigher c.length hc]
  · have he : c.length = 1 := by
      have hp := c.length_pos hn
      omega
    have hzero : ‖iteratedFDeriv ℝ c.length R (h x)‖ = 0 := by
      rw [he]
      exact hRone
    rw [if_neg hc, hzero, zero_mul]

/-- Global smoothness supplies the pointwise linearization estimate. -/
theorem flowJet_linearization_remainder_bound
    {g : F → K} {h : E → F}
    (hg : ContDiff ℝ ∞ g) (hh : ContDiff ℝ ∞ h)
    {n : ℕ} (hn : 0 < n) (x : E) :
    ‖iteratedFDeriv ℝ n
        ((g - (fderiv ℝ g (h x) : F → K)) ∘ h) x‖ ≤
      ∑ c : OrderedFinpartition n,
        if 2 ≤ c.length then
          ‖iteratedFDeriv ℝ c.length g (h x)‖ *
            ∏ j, ‖iteratedFDeriv ℝ (c.partSize j) h x‖
        else 0 :=
  flowJet_linearization_remainder_bound_at hg.contDiffAt hh.contDiffAt hn

/-- Every block of a nonlinear chain-rule term has lower order. -/
theorem flowJet_partition_partSize_lt {n : ℕ} (c : OrderedFinpartition n)
    (hc : 2 ≤ c.length) (i : Fin c.length) : c.partSize i < n := by
  classical
  obtain ⟨j, hji⟩ : ∃ j : Fin c.length, j ≠ i := by
    by_cases hi : i.val = 0
    · refine ⟨⟨1, by omega⟩, ?_⟩
      intro he
      have hh := congrArg Fin.val he
      simp only [Fin.val_mk] at hh
      omega
    · refine ⟨⟨0, by omega⟩, ?_⟩
      intro he
      have hh := congrArg Fin.val he
      simp only [Fin.val_mk] at hh
      omega
  have hsum := Finset.sum_erase_add (s := Finset.univ) (f := c.partSize)
    (Finset.mem_univ i)
  have hj : c.partSize j ≤ ∑ k ∈ Finset.univ.erase i, c.partSize k :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _)
      (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩)
  have htotal := oneHighPartition_sum_orders c
  have hpos := c.partSize_pos j
  omega

/-- Original field derivative of order j has weight j−1. The nonlinear
chain rule preserves the total weight n−1 exactly. -/
theorem flowJet_partition_weight {n : ℕ} (c : OrderedFinpartition n)
    (hn : 0 < n) :
    (c.length - 1) + ∑ j, (c.partSize j - 1) = n - 1 := by
  have he : (∑ j, (c.partSize j - 1)) + c.length = n := by
    calc
      _ = ∑ j, ((c.partSize j - 1) + 1) := by
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
          mul_one]
      _ = ∑ j, c.partSize j := Finset.sum_congr rfl
        (fun j _ => Nat.sub_add_cancel (c.partSize_pos j))
      _ = n := oneHighPartition_sum_orders c
  have hp := c.length_pos hn
  omega

end ContinuousFlexibility.Analysis
