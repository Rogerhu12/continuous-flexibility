module

public import ContinuousFlexibility.Analysis.N04FlowPolynomialBounds
public import ContinuousFlexibility.Analysis.RootFlowSymmetry

/-!
# Root-axis flow jets without a parameter-box radius

Draft: not independently reviewed or compiled.

The true flow-jet integral equations are evaluated on one stationary
trajectory. The angular linearization is zero there, so the triangular
induction uses no Gronwall exponential and no bound away from that
trajectory. Its raw-jet variables retain the existing derivative weights.
The final adapter obtains both identities from the actual unscaled
root-regularized ODE.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory ContinuousFlexibility.Statements
open scoped BigOperators ContDiff

set_option backward.isDefEq.respectTransparency false

/-- A pointwise majorant for the actual jets at a stationary trajectory.
No derivative bound on a parameter neighborhood occurs in this property. -/
def StationaryFlowPolynomialMajorant (n : ℕ) (P : FlowJetPolynomial) : Prop :=
  ∀ M : ℕ → ℝ, (∀ k, 0 ≤ M k) →
    ∀ F : ℝ × N04FlowPoint → ℝ, ContDiff ℝ ∞ F →
      (∀ t v, Function.Periodic (fun θ : ℝ => F (t, (v, θ))) Real.pi) →
    ∀ Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ, N04FlowEquations F Θ →
    ∀ q : N04FlowPoint,
      (∀ t ∈ Icc (0 : ℝ) 1, Θ q.1 t q.2 = q.2) →
      (∀ t ∈ Icc (0 : ℝ) 1,
        deriv (fun θ : ℝ => F (t, (q.1, θ))) q.2 = 0) →
      (∀ k : ℕ, ∀ t ∈ Icc (0 : ℝ) 1,
        ‖iteratedFDeriv ℝ (k + 1) (fun y : N04FlowPoint => F (t, y)) q‖ ≤ M k) →
      ∀ t ∈ Icc (0 : ℝ) 1,
        ‖iteratedFDeriv ℝ (n + 1) (fun y : N04FlowPoint => Θ y.1 t y.2) q‖ ≤
          flowJetPolynomialEval P M

/-- The order n+1 flow jet on a stationary axis has a genuine polynomial
majorant of weighted degree at most n. The polynomial is fixed before
the field, chosen flow, raw bounds, point and time. -/
theorem exists_stationaryFlow_spatialJet_polynomial (n : ℕ) :
    ∃ P : FlowJetPolynomial,
      FlowJetPolynomialDegreeLE P n ∧ StationaryFlowPolynomialMajorant n P := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      let P : FlowJetPolynomial := [(1, [])] ++ [(1, [0])]
      refine ⟨P, ?_, ?_⟩
      · exact (FlowJetPolynomialDegreeLE.const zero_le_one 0).append
          (FlowJetPolynomialDegreeLE.atom 0)
      · intro M hM F hF hperiod Θ hΘ q hstationary hangular hraw t ht
        have hchain (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) :
            ‖parametricSpatialJet (n04FlowComposedField F Θ) 1 (q, r)‖ ≤
              (0 : ℝ) * ‖iteratedFDeriv ℝ 1
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
          rw [hstationary r hr, hangular r hr, abs_zero, zero_mul, add_zero] at hb'
          simpa only [zero_mul, zero_add] using hb'.trans (hraw 0 r hr)
        have hb := n04Flow_spatialJet_norm_le_of_composed_bound
          hF hperiod hΘ 1 q
          (show ContinuousOn (fun _ : ℝ => (0 : ℝ)) (Icc (0 : ℝ) 1) from
            continuousOn_const)
          (fun _ _ => le_rfl) (hM 0)
          (show (∫ _t in (0 : ℝ)..1, (0 : ℝ)) ≤ 0 by
            simp only [intervalIntegral.integral_zero, le_refl])
          hchain t ht
        have hc : ‖iteratedFDeriv ℝ 1 (fun y : N04FlowPoint => y.2) q‖ ≤ 1 := by
          simpa only [ContinuousLinearMap.coe_snd'] using
            (flowJet_norm_iteratedFDeriv_clm_le
              (ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ) le_rfl q).trans
              (ContinuousLinearMap.norm_snd_le ℝ (ℝ × ℝ) ℝ)
        calc
          _ ≤ ‖iteratedFDeriv ℝ 1 (fun y : N04FlowPoint => y.2) q‖ + M 0 := by
            simpa only [Real.exp_zero, mul_one] using hb
          _ ≤ 1 + M 0 := add_le_add hc le_rfl
          _ = flowJetPolynomialEval P M := by
            simp only [P, flowJetPolynomialEval_append,
              flowJetPolynomialEval_const, flowJetPolynomialEval_atom]
    · let Q : ℕ → FlowJetPolynomial := fun k =>
        if hk : k < n then (ih k hk).choose else []
      have hQdegree (k : ℕ) (hk : k < n) :
          FlowJetPolynomialDegreeLE (Q k) k := by
        simpa only [Q, dif_pos hk] using (ih k hk).choose_spec.1
      have hQbound (k : ℕ) (hk : k < n) :
          StationaryFlowPolynomialMajorant k (Q k) := by
        simpa only [Q, dif_pos hk] using (ih k hk).choose_spec.2
      obtain ⟨R, hR, heR⟩ := flowJetPolynomial_exists_partition_forcing n Q hQdegree
      refine ⟨R, hR, ?_⟩
      intro M hM F hF hperiod Θ hΘ q hstationary hangular hraw t ht
      have hchain (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) :
          ‖parametricSpatialJet (n04FlowComposedField F Θ) (n + 1) (q, r)‖ ≤
            (0 : ℝ) * ‖iteratedFDeriv ℝ (n + 1)
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
            have hrawc :
                ‖iteratedFDeriv ℝ c.length (fun y : N04FlowPoint => F (r, y))
                  (q.1, Θ q.1 r q.2)‖ ≤ M (c.length - 1) := by
              have hb := hraw (c.length - 1) r hr
              rw [Nat.sub_add_cancel (by omega : 1 ≤ c.length)] at hb
              simpa only [hstationary r hr] using hb
            have hinner (j : Fin c.length) :
                ‖iteratedFDeriv ℝ (c.partSize j)
                  (fun y : N04FlowPoint => Θ y.1 r y.2) q‖ ≤
                  flowJetPolynomialEval (Q (c.partSize j - 1)) M := by
              have hj : c.partSize j - 1 < n := by
                have hlt := flowJet_partition_partSize_lt c hc j
                have hpos := c.partSize_pos j
                omega
              have hprev := hQbound (c.partSize j - 1) hj
                M hM F hF hperiod Θ hΘ q hstationary hangular hraw r hr
              rw [Nat.sub_add_cancel (c.partSize_pos j)] at hprev
              exact hprev
            exact mul_le_mul hrawc
              (Finset.prod_le_prod₀
                (fun _ _ => add_nonneg zero_le_one (norm_nonneg _))
                (fun j _ => add_le_add le_rfl (hinner j)))
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
        refine add_le_add ?_ (Finset.sum_le_sum (fun c _ => hterms c))
        rw [hstationary r hr, hangular r hr, abs_zero]
      have hb := n04Flow_spatialJet_norm_le_of_composed_bound
        hF hperiod hΘ (n + 1) q
        (show ContinuousOn (fun _ : ℝ => (0 : ℝ)) (Icc (0 : ℝ) 1) from
          continuousOn_const)
        (fun _ _ => le_rfl) (flowJetPolynomialEval_nonneg hR hM)
        (show (∫ _t in (0 : ℝ)..1, (0 : ℝ)) ≤ 0 by
          simp only [intervalIntegral.integral_zero, le_refl])
        hchain t ht
      have hc : iteratedFDeriv ℝ (n + 1) (fun y : N04FlowPoint => y.2) q = 0 := by
        simpa only [ContinuousLinearMap.coe_snd'] using
          flowJet_iteratedFDeriv_clm_eq_zero
            (ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ) (by omega : 2 ≤ n + 1) q
      simpa only [hc, norm_zero, zero_add, Real.exp_zero, mul_one] using hb

/-- The original root equation supplies the stationary trajectory and its
zero angular linearization. The raw jet assumption is only on the root
axis, with no radial neighborhood or normalization scale. -/
theorem exists_rootRegularizedFlow_zero_spatialJet_polynomial (n : ℕ) :
    ∃ P : FlowJetPolynomial, FlowJetPolynomialDegreeLE P n ∧
      ∀ M : ℕ → ℝ, (∀ k, 0 ≤ M k) →
      ∀ d c : PolarPoint → ℝ, ContDiff ℝ ∞ d → ContDiff ℝ ∞ c →
        (∀ r, Function.Periodic (fun θ => d (r, θ)) Real.pi) →
        (∀ r, Function.Periodic (fun θ => c (r, θ)) Real.pi) →
      ∀ Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ,
        N04FlowEquations (rootRegularizedField d c) Θ →
      ∀ θ : ℝ,
        (∀ k : ℕ, ∀ t ∈ Icc (0 : ℝ) 1,
          ‖iteratedFDeriv ℝ (k + 1)
            (fun y : N04FlowPoint => rootRegularizedField d c (t, y))
              ((0, 0), θ)‖ ≤ M k) →
        ∀ t ∈ Icc (0 : ℝ) 1,
          ‖iteratedFDeriv ℝ (n + 1)
            (fun y : N04FlowPoint => Θ y.1 t y.2) ((0, 0), θ)‖ ≤
              flowJetPolynomialEval P M := by
  obtain ⟨P, hP, hb⟩ := exists_stationaryFlow_spatialJet_polynomial n
  refine ⟨P, hP, ?_⟩
  intro M hM d c hd hc hdperiod hcperiod Θ hΘ θ hraw
  have hstationary (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      Θ (0, 0) t θ = θ :=
    rootRegularizedFlow_zero_parameters hΘ.1 hΘ.2 θ ht
  have hangular (t : ℝ) (_ht : t ∈ Icc (0 : ℝ) 1) :
      deriv (fun η : ℝ => rootRegularizedField d c (t, ((0, 0), η))) θ = 0 := by
    have he : (fun η : ℝ => rootRegularizedField d c (t, ((0, 0), η))) =
        (fun _ : ℝ => (0 : ℝ)) := by
      funext η
      simp only [rootRegularizedField, mul_zero, zero_mul, zero_add]
    rw [he, deriv_const]
  exact hb M hM (rootRegularizedField d c)
    (contDiff_rootRegularizedField hd hc)
    (rootRegularizedField_periodic hdperiod hcperiod) Θ hΘ ((0, 0), θ)
    hstationary hangular hraw

end ContinuousFlexibility.Analysis
