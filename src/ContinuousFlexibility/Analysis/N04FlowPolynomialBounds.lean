import ContinuousFlexibility.Analysis.N04FlowJetGronwall
import ContinuousFlexibility.Analysis.ScalarFlowTriangularJets
import ContinuousFlexibility.Analysis.FlowJetPartitionPolynomial

/-!
# Polynomial bounds for every actual mixed spatial flow jet

The induction uses the actual differentiated integral equations and the
triangular chain rule. The polynomial is selected before the raw field
bounds, field, and chosen solution. Only the angular integral bound
enters its exponential coefficients; all original parameter derivatives
remain polynomial variables with their exact derivative weights.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory ContinuousFlexibility.Statements
open scoped BigOperators ContDiff

set_option backward.isDefEq.respectTransparency false

/-- Bounds on the actual positive-order spatial derivatives of the
original field. Index k denotes derivative order k+1. -/
def N04FlowPositiveRawBounds (M : ℕ → ℝ) (F : ℝ × N04FlowPoint → ℝ) : Prop :=
  ∀ k : ℕ, ∀ t ∈ Icc (0 : ℝ) 1, ∀ q : N04FlowPoint,
    q.1 ∈ n04FlowParameterBox →
      ‖iteratedFDeriv ℝ (k + 1) (fun y : N04FlowPoint => F (t, y)) q‖ ≤ M k

/-- A polynomial bounds the actual order n+1 flow jet for every raw field
and chosen genuine solution with the prescribed angular control. -/
def N04FlowPolynomialMajorant (Λ : ℝ) (n : ℕ) (P : FlowJetPolynomial) : Prop :=
  ∀ M : ℕ → ℝ, (∀ k, 0 ≤ M k) →
    ∀ F : ℝ × N04FlowPoint → ℝ, ContDiff ℝ ∞ F →
      (∀ t v, Function.Periodic (fun θ : ℝ => F (t, (v, θ))) Real.pi) →
      N04FlowPositiveRawBounds M F → N04FlowAngularControl F Λ →
    ∀ Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ, N04FlowEquations F Θ →
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ q : N04FlowPoint, q.1 ∈ n04FlowParameterBox →
        ‖iteratedFDeriv ℝ (n + 1) (fun y : N04FlowPoint => Θ y.1 t y.2) q‖ ≤
          flowJetPolynomialEval P M

/-- The original field jets enter with total weighted degree at most n
in the actual order n+1 flow derivative. -/
theorem exists_n04Flow_spatialJet_polynomial (Λ : ℝ) (n : ℕ) :
    ∃ P : FlowJetPolynomial,
      FlowJetPolynomialDegreeLE P n ∧ N04FlowPolynomialMajorant Λ n P := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      let P : FlowJetPolynomial :=
        flowJetPolynomialMul [(Real.exp Λ, [])] ([(1, [])] ++ [(1, [0])])
      refine ⟨P, ?_, ?_⟩
      · exact (FlowJetPolynomialDegreeLE.const (Real.exp_pos Λ).le 0).mul
          ((FlowJetPolynomialDegreeLE.const zero_le_one 0).append
            (FlowJetPolynomialDegreeLE.atom 0))
      · intro M hM F hF hperiod hraw hangular Θ hΘ t ht q hq
        have hcontrol := hangular
        obtain ⟨α, hα, hα0, hαbound, hΛ⟩ := hcontrol
        have hchain (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) :
            ‖parametricSpatialJet (n04FlowComposedField F Θ) 1 (q, r)‖ ≤
              α r * ‖iteratedFDeriv ℝ 1
                (fun y : N04FlowPoint => Θ y.1 r y.2) q‖ + M 0 := by
          have hg : ContDiff ℝ ∞ (fun y : N04FlowPoint => F (r, y)) :=
            hF.comp (contDiff_const.prodMk contDiff_id)
          have hb := flowJet_augmented_comp_first_norm_le hg
            (n04Flow_contDiff_slice hF hperiod hΘ hr) q
          have hb' :
              ‖parametricSpatialJet (n04FlowComposedField F Θ) 1 (q, r)‖ ≤
                ‖iteratedFDeriv ℝ 1 (fun y : N04FlowPoint => F (r, y))
                  (q.1, Θ q.1 r q.2)‖ +
                |deriv (fun θ => F (r, (q.1, θ))) (Θ q.1 r q.2)| *
                  ‖iteratedFDeriv ℝ 1 (fun y : N04FlowPoint => Θ y.1 r y.2) q‖ := by
            simpa only [parametricSpatialJet, n04FlowComposedField, Function.comp_def] using hb
          calc
            _ ≤ _ := hb'
            _ ≤ M 0 + α r * ‖iteratedFDeriv ℝ 1
                  (fun y : N04FlowPoint => Θ y.1 r y.2) q‖ :=
              add_le_add (hraw 0 r hr (q.1, Θ q.1 r q.2) hq)
                (mul_le_mul_of_nonneg_right (hαbound r hr q.1 hq (Θ q.1 r q.2))
                  (norm_nonneg _))
            _ = _ := add_comm _ _
        have hb := n04Flow_spatialJet_norm_le_of_composed_bound
          hF hperiod hΘ 1 q hα hα0 (hM 0) hΛ hchain t ht
        have hc : ‖iteratedFDeriv ℝ 1 (fun y : N04FlowPoint => y.2) q‖ ≤ 1 := by
          simpa only [ContinuousLinearMap.coe_snd'] using
            (flowJet_norm_iteratedFDeriv_clm_le
              (ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ) le_rfl q).trans
              (ContinuousLinearMap.norm_snd_le ℝ (ℝ × ℝ) ℝ)
        calc
          _ ≤ (‖iteratedFDeriv ℝ 1 (fun y : N04FlowPoint => y.2) q‖ + M 0) *
              Real.exp Λ := hb
          _ ≤ (1 + M 0) * Real.exp Λ :=
            mul_le_mul_of_nonneg_right (add_le_add_right hc _) (Real.exp_pos _).le
          _ = flowJetPolynomialEval P M := by
            simp only [P, flowJetPolynomialEval_mul, flowJetPolynomialEval_const,
              flowJetPolynomialEval_append, flowJetPolynomialEval_atom]
            ring
    · let Q : ℕ → FlowJetPolynomial := fun k =>
        if hk : k < n then (ih k hk).choose else []
      have hQdegree (k : ℕ) (hk : k < n) :
          FlowJetPolynomialDegreeLE (Q k) k := by
        simpa only [Q, dif_pos hk] using (ih k hk).choose_spec.1
      have hQbound (k : ℕ) (hk : k < n) :
          N04FlowPolynomialMajorant Λ k (Q k) := by
        simpa only [Q, dif_pos hk] using (ih k hk).choose_spec.2
      obtain ⟨R, hR, heR⟩ := flowJetPolynomial_exists_partition_forcing n Q hQdegree
      let P : FlowJetPolynomial := flowJetPolynomialMul [(Real.exp Λ, [])] R
      refine ⟨P, ?_, ?_⟩
      · simpa only [Nat.zero_add] using
          (FlowJetPolynomialDegreeLE.const (Real.exp_pos Λ).le 0).mul hR
      · intro M hM F hF hperiod hraw hangular Θ hΘ t ht q hq
        have hcontrol := hangular
        obtain ⟨α, hα, hα0, hαbound, hΛ⟩ := hcontrol
        have hchain (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) :
            ‖parametricSpatialJet (n04FlowComposedField F Θ) (n + 1) (q, r)‖ ≤
              α r * ‖iteratedFDeriv ℝ (n + 1)
                (fun y : N04FlowPoint => Θ y.1 r y.2) q‖ +
                flowJetPolynomialEval R M := by
          have hg : ContDiff ℝ ∞ (fun y : N04FlowPoint => F (r, y)) :=
            hF.comp (contDiff_const.prodMk contDiff_id)
          have hb := flowJet_augmented_comp_high_norm_le hg
            (n04Flow_contDiff_slice hF hperiod hΘ hr) (by omega : 2 ≤ n + 1) q
          have hterms (c : OrderedFinpartition (n + 1)) :
              (if 2 ≤ c.length then
                ‖iteratedFDeriv ℝ c.length (fun y : N04FlowPoint => F (r, y))
                  (q.1, Θ q.1 r q.2)‖ *
                  ∏ j, (1 + ‖iteratedFDeriv ℝ (c.partSize j)
                    (fun y : N04FlowPoint => Θ y.1 r y.2) q‖)
              else 0) ≤
              (if 2 ≤ c.length then
                M (c.length - 1) *
                  ∏ j, (1 + flowJetPolynomialEval (Q (c.partSize j - 1)) M)
              else 0) := by
            by_cases hc : 2 ≤ c.length
            · rw [if_pos hc, if_pos hc]
              have hrawc := hraw (c.length - 1) r hr (q.1, Θ q.1 r q.2) hq
              rw [Nat.sub_add_cancel (by omega : 1 ≤ c.length)] at hrawc
              have hinner (j : Fin c.length) :
                  ‖iteratedFDeriv ℝ (c.partSize j)
                    (fun y : N04FlowPoint => Θ y.1 r y.2) q‖ ≤
                    flowJetPolynomialEval (Q (c.partSize j - 1)) M := by
                have hj : c.partSize j - 1 < n := by
                  have hlt := flowJet_partition_partSize_lt c hc j
                  have hpos := c.partSize_pos j
                  omega
                have hprev := hQbound (c.partSize j - 1) hj
                  M hM F hF hperiod hraw hangular Θ hΘ r hr q hq
                simpa only [Nat.sub_add_cancel (c.partSize_pos j)] using hprev
              exact mul_le_mul hrawc
                (Finset.prod_le_prod₀
                  (fun _ _ => add_nonneg zero_le_one (norm_nonneg _))
                  (fun j _ => add_le_add_left (hinner j) 1))
                (Finset.prod_nonneg fun _ _ =>
                  add_nonneg zero_le_one (norm_nonneg _)) (hM _)
            · rw [if_neg hc, if_neg hc]
          have hb' :
              ‖parametricSpatialJet (n04FlowComposedField F Θ) (n + 1) (q, r)‖ ≤
                |deriv (fun θ => F (r, (q.1, θ))) (Θ q.1 r q.2)| *
                  ‖iteratedFDeriv ℝ (n + 1)
                    (fun y : N04FlowPoint => Θ y.1 r y.2) q‖ +
                ∑ c : OrderedFinpartition (n + 1),
                  if 2 ≤ c.length then
                    ‖iteratedFDeriv ℝ c.length (fun y : N04FlowPoint => F (r, y))
                      (q.1, Θ q.1 r q.2)‖ *
                      ∏ j, (1 + ‖iteratedFDeriv ℝ (c.partSize j)
                        (fun y : N04FlowPoint => Θ y.1 r y.2) q‖)
                  else 0 := by
            simpa only [parametricSpatialJet, n04FlowComposedField, Function.comp_def] using hb
          apply hb'.trans
          rw [heR M]
          exact add_le_add
            (mul_le_mul_of_nonneg_right (hαbound r hr q.1 hq (Θ q.1 r q.2))
              (norm_nonneg _))
            (Finset.sum_le_sum (fun c _ => hterms c))
        have hb := n04Flow_spatialJet_norm_le_of_composed_bound
          hF hperiod hΘ (n + 1) q hα hα0 (flowJetPolynomialEval_nonneg hR hM)
          hΛ hchain t ht
        have hc : iteratedFDeriv ℝ (n + 1) (fun y : N04FlowPoint => y.2) q = 0 := by
          simpa only [ContinuousLinearMap.coe_snd'] using
            flowJet_iteratedFDeriv_clm_eq_zero
              (ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ) (by omega : 2 ≤ n + 1) q
        rw [hc, norm_zero, zero_add] at hb
        calc
          _ ≤ flowJetPolynomialEval R M * Real.exp Λ := hb
          _ = flowJetPolynomialEval P M := by
            rw [flowJetPolynomialEval_mul, flowJetPolynomialEval_const, mul_comm]

end ContinuousFlexibility.Analysis
