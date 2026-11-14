import ContinuousFlexibility.Analysis.NonlinearInverseJetTriangle
import ContinuousFlexibility.Analysis.FlowJetPartitionPolynomial

/-!
# Weighted polynomial bounds for actual nonlinear inverse jets

The first inverse derivative is an atom of weight zero. Each forward
derivative of order k+1 has weight k. The genuine local inverse identity
and the triangular chain rule produce every higher inverse jet from
strictly lower inverse jets. No higher inverse derivative bound is an input.
-/

noncomputable section

universe u v

namespace ContinuousFlexibility.Analysis

open Filter
open scoped Topology BigOperators ContDiff

set_option backward.isDefEq.respectTransparency false

/-- A universal polynomial majorant for the actual inverse jet of order
n+1. The original first forward derivative need not be bounded. -/
def NonlinearInversePolynomialMajorant (n : ℕ) (P : FlowJetPolynomial) : Prop :=
  ∀ M : ℕ → ℝ, (∀ k, 0 ≤ M k) →
    ∀ (E : Type u) (F : Type v)
      [NormedAddCommGroup E] [NormedSpace ℝ E]
      [NormedAddCommGroup F] [NormedSpace ℝ F],
    ∀ (f : E → F) (g : F → E) (x : F),
      ContDiffAt ℝ ∞ f (g x) → ContDiffAt ℝ ∞ g x →
      f ∘ g =ᶠ[𝓝 x] (id : F → F) →
    ∀ L : F →L[ℝ] E,
      L.comp (fderiv ℝ f (g x)) = ContinuousLinearMap.id ℝ E →
      ‖L‖ ≤ M 0 →
      (∀ k : ℕ, 1 ≤ k → ‖iteratedFDeriv ℝ (k + 1) f (g x)‖ ≤ M k) →
      ‖iteratedFDeriv ℝ (n + 1) g x‖ ≤ flowJetPolynomialEval P M

/-- The order n+1 inverse jet has a polynomial majorant of weighted degree
at most n, chosen before the maps, spaces, and raw derivative bounds. -/
theorem exists_nonlinearInverse_spatialJet_polynomial (n : ℕ) :
    ∃ P : FlowJetPolynomial, FlowJetPolynomialDegreeLE P n ∧
      NonlinearInversePolynomialMajorant.{u, v} n P := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      refine ⟨[(1, [0])], FlowJetPolynomialDegreeLE.atom 0, ?_⟩
      intro M hM E F _ _ _ _ f g x hf hg hfg L hL hLbound hraw
      simpa only [flowJetPolynomialEval_atom] using
        (nonlinearInverse_firstJet_norm hf hg hfg L hL).trans_le hLbound
    · let Q : ℕ → FlowJetPolynomial := fun k =>
        if hk : k < n then (ih k hk).choose else []
      have hQdegree (k : ℕ) (hk : k < n) :
          FlowJetPolynomialDegreeLE (Q k) k := by
        simpa only [Q, dif_pos hk] using (ih k hk).choose_spec.1
      have hQbound (k : ℕ) (hk : k < n) :
          NonlinearInversePolynomialMajorant.{u, v} k (Q k) := by
        simpa only [Q, dif_pos hk] using (ih k hk).choose_spec.2
      obtain ⟨R, hR, heR⟩ := flowJetPolynomial_exists_partition_forcing n Q hQdegree
      let P : FlowJetPolynomial := flowJetPolynomialMul [(1, [0])] R
      refine ⟨P, ?_, ?_⟩
      · simpa only [Nat.zero_add] using (FlowJetPolynomialDegreeLE.atom 0).mul hR
      · intro M hM E F _ _ _ _ f g x hf hg hfg L hL hLbound hraw
        have hterms (c : OrderedFinpartition (n + 1)) :
            (if 2 ≤ c.length then
              ‖iteratedFDeriv ℝ c.length f (g x)‖ *
                ∏ j, ‖iteratedFDeriv ℝ (c.partSize j) g x‖
            else 0) ≤
            (if 2 ≤ c.length then
              M (c.length - 1) *
                ∏ j, (1 + flowJetPolynomialEval (Q (c.partSize j - 1)) M)
            else 0) := by
          by_cases hc : 2 ≤ c.length
          · rw [if_pos hc, if_pos hc]
            have hrawc := hraw (c.length - 1) (by omega)
            rw [Nat.sub_add_cancel (by omega : 1 ≤ c.length)] at hrawc
            have hinner (j : Fin c.length) :
                ‖iteratedFDeriv ℝ (c.partSize j) g x‖ ≤
                  flowJetPolynomialEval (Q (c.partSize j - 1)) M := by
              have hj : c.partSize j - 1 < n := by
                have hlt := flowJet_partition_partSize_lt c hc j
                have hpos := c.partSize_pos j
                omega
              have hprev := hQbound (c.partSize j - 1) hj
                M hM E F f g x hf hg hfg L hL hLbound hraw
              have horder : c.partSize j - 1 + 1 = c.partSize j :=
                Nat.sub_add_cancel (c.partSize_pos j)
              rw [horder] at hprev
              exact hprev
            exact mul_le_mul hrawc
              (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
                (fun j _ => (hinner j).trans (le_add_of_nonneg_left zero_le_one)))
              (Finset.prod_nonneg fun _ _ => norm_nonneg _) (hM _)
          · rw [if_neg hc, if_neg hc]
        have hsum :
            (∑ c : OrderedFinpartition (n + 1),
              if 2 ≤ c.length then
                ‖iteratedFDeriv ℝ c.length f (g x)‖ *
                  ∏ j, ‖iteratedFDeriv ℝ (c.partSize j) g x‖
              else 0) ≤ flowJetPolynomialEval R M := by
          rw [heR M]
          exact Finset.sum_le_sum fun c _ => hterms c
        calc
          ‖iteratedFDeriv ℝ (n + 1) g x‖ ≤ ‖L‖ *
              ∑ c : OrderedFinpartition (n + 1),
                if 2 ≤ c.length then
                  ‖iteratedFDeriv ℝ c.length f (g x)‖ *
                    ∏ j, ‖iteratedFDeriv ℝ (c.partSize j) g x‖
                else 0 :=
            nonlinearInverse_highJet_norm_le hf hg hfg L hL (by omega)
          _ ≤ ‖L‖ * flowJetPolynomialEval R M :=
            mul_le_mul_of_nonneg_left hsum (norm_nonneg L)
          _ ≤ M 0 * flowJetPolynomialEval R M :=
            mul_le_mul_of_nonneg_right hLbound (flowJetPolynomialEval_nonneg hR hM)
          _ = flowJetPolynomialEval P M := by
            rw [flowJetPolynomialEval_mul, flowJetPolynomialEval_atom]

end ContinuousFlexibility.Analysis
