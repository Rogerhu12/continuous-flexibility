import ContinuousFlexibility.Analysis.N01FlowParameterVariation

/-!
# Mixed height and external-parameter bounds for the actual N01 flow

The ordered second directional jet is the ordinary derivative, in a
state direction, of the actual external-parameter derivative. Evaluating
the N01 second-order tower on one state direction and the pure external
parameter gives a bound linear in the state direction's grading.
No interchange of partial derivatives is used.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

local instance (S : PhysicalSpacesData) : SMul ℝ (AnnularState S) := Prod.instSMul
local instance : NormedSpace ℝ ℝ := NormedField.toNormedSpace

open Set Filter
open ContinuousFlexibility.Analysis
open scoped Topology BigOperators

theorem stateMixedExternalParameterLine (S : PhysicalSpacesData)
    (x η : AnnularState S) (t q : ℝ) :
    ((x, (0 : ℝ)) + t • (η, (0 : ℝ))) +
      q • ((0 : AnnularState S), (1 : ℝ)) = (x + t • η, q) := by
  change ((x + t • η) + q • (0 : AnnularState S),
    ((0 : ℝ) + t • (0 : ℝ)) + q • (1 : ℝ)) = (x + t • η, q)
  simp only [smul_zero, add_zero, smul_eq_mul, mul_one, zero_add]

theorem oneHighVariationWeight_state_external_zero
    (S : PhysicalSpacesData) (base high : ℕ) (η : AnnularState S) :
    oneHighVariationWeight (pairGrading (stateGrading S) realGrading)
      base high 0
      (Fin.cons (η, (0 : ℝ))
        (fun _ : Fin 1 => ((0 : AnnularState S), (1 : ℝ)))) =
      2 * stateGrading S base η + stateGrading S high η := by
  classical
  have he0 : (Finset.univ : Finset (Fin 2)).erase 0 = {1} := by decide
  have he1 : (Finset.univ : Finset (Fin 2)).erase 1 = {0} := by decide
  have hstate (n : ℕ) :
      pairGrading (stateGrading S) realGrading n (η, (0 : ℝ)) =
        stateGrading S n η := by
    change stateGrading S n η + realGrading n (0 : ℝ) = _
    rw [(realGrading n).map_zero', add_zero]
  have hparameter (n : ℕ) :
      pairGrading (stateGrading S) realGrading n ((0 : AnnularState S), (1 : ℝ)) = 1 := by
    change stateGrading S n (0 : AnnularState S) + realGrading n (1 : ℝ) = 1
    rw [(stateGrading S n).map_zero']
    change (0 : ℝ) + |1| = 1
    norm_num
  have hfin {E : Type*} [AddCommGroup E] [Module ℝ E]
      (p : ℕ → Seminorm ℝ E) (v w : E) :
      oneHighVariationWeight p base high 0
        (Fin.cons v (fun _ : Fin 1 => w)) =
        p base v * p base w + (p high v * p base w + p high w * p base v) := by
    simp only [oneHighVariationWeight, Fin.prod_univ_two, Fin.sum_univ_two,
      he0, he1, Finset.prod_singleton, Fin.cons_zero, Fin.cons_one,
      (p high).map_zero', add_zero, one_mul]
  apply (hfin (pairGrading (stateGrading S) realGrading)
    (η, (0 : ℝ)) ((0 : AnnularState S), (1 : ℝ))).trans
  rw [hstate, hstate, hparameter, hparameter]
  simp only [mul_one, one_mul]
  ring

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

/-- The state derivative is the first slot of the ordered second jet. -/
theorem ordinaryFlow_state_q_mixed_hasDerivAt_of_tower
    {m : ℕ} {r θ : ℝ}
    (J : SmoothDirections (stateNeighborhood S C base ε)
      (ordinaryFlowFamily S C m 0 0 (r, θ)))
    (x η : AnnularState S) (hx : (x, (0 : ℝ)) ∈ stateNeighborhood S C base ε) :
    HasDerivAt
      (fun t : ℝ => deriv (fun q : ℝ => C.minusFlow (x + t • η, q) m r θ) 0)
      (J.D 2 (x, 0)
        (Fin.cons (η, (0 : ℝ))
          (fun _ : Fin 1 => ((0 : AnnularState S), (1 : ℝ))))) 0 := by
  have h := J.hasDerivAt_mixed_scalar_line (x, (0 : ℝ))
    (η, (0 : ℝ)) ((0 : AnnularState S), (1 : ℝ)) hx
  simpa only [stateMixedExternalParameterLine, ordinaryFlowFamily, mixedDerivative,
    iteratedDeriv_zero, deriv_sub_const] using h

/-- The bound is for the ordinary mixed derivative of the actual flow
function and is linear in the state-direction grading. -/
theorem N01Properties.minusFlow_state_q_mixed_derivative_bound
    (hN : N01Properties D T S C base loss ε) :
    ∃ B : ℝ, 0 < B ∧ ∀ η : AnnularState S, ∀ m r θ,
      r ∈ Ioo (C.left m) (C.right m) →
      |deriv (fun t : ℝ => deriv (fun q : ℝ =>
        C.minusFlow (C.referenceState + t • η, q) m r θ) 0) 0| ≤
        B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
          T.E0 (T.sample (C.cell m)) ^ B *
          (2 * stateGrading S base η + stateGrading S loss η) := by
  have hdata := hN
  rcases hdata with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hflow⟩
  obtain ⟨B, hB, hb⟩ := hflow 2 0
  refine ⟨B, hB, fun η m r θ hr => ?_⟩
  obtain ⟨J, hJ⟩ := hb m 0 0 (r, θ) (by norm_num) hr
  have hz : (C.referenceState, (0 : ℝ)) ∈ stateNeighborhood S C base ε := by
    constructor
    · simpa only [sub_self, map_zero] using hN.2.1
    · simpa only [abs_zero] using hN.2.1
  have hd := (ordinaryFlow_state_q_mixed_hasDerivAt_of_tower
    J C.referenceState η hz).deriv
  have hbound := hJ (C.referenceState, 0) hz
    (Fin.cons (η, (0 : ℝ))
      (fun _ : Fin 1 => ((0 : AnnularState S), (1 : ℝ))))
  rw [← hd] at hbound
  simpa only [pow_zero, one_mul, sub_self, zero_add,
    oneHighVariationWeight_state_external_zero] using hbound

end ContinuousFlexibility.Statements
