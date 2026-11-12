import ContinuousFlexibility.Analysis.N01FlowParameterVariation
import ContinuousFlexibility.Analysis.N01OrdinaryFlowLoss

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

local instance n01FlowMixedParameterBoundStateSMul (S : PhysicalSpacesData) : SMul ℝ (AnnularState S) := Prod.instSMul
local instance n01FlowMixedParameterBoundRealNormedSpace : NormedSpace ℝ ℝ := NormedField.toNormedSpace

open Set Filter
open ContinuousFlexibility.Analysis
open scoped Topology BigOperators

theorem stateMixedExternalParameterLine (S : PhysicalSpacesData)
    (x η : AnnularState S) (t q : ℝ) :
    ((x, (0 : ℝ)) + t • (η, (0 : ℝ))) +
      q • ((0 : AnnularState S), (1 : ℝ)) = (x + t • η, q) := by
  change ((x + t • η) + q • (0 : AnnularState S),
    ((0 : ℝ) + t • (0 : ℝ)) + q • (1 : ℝ)) = (x + t • η, q)
  simp only [smul_zero, add_zero, smul_eq_mul, mul_one, mul_zero, zero_add]

theorem oneHighVariationWeight_finTwo_zero
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (base high : ℕ) (v w : E) :
    oneHighVariationWeight p base high 0 (Fin.cons v (fun _ : Fin 1 => w)) =
      p base v * p base w + (p high v * p base w + p high w * p base v) := by
  classical
  have he0 : (Finset.univ : Finset (Fin 2)).erase 0 = {1} := by decide
  have he1 : (Finset.univ : Finset (Fin 2)).erase 1 = {0} := by decide
  let z : Fin 2 → E := Fin.cons v (fun _ : Fin 1 => w)
  unfold oneHighVariationWeight
  change (1 + p high (0 : E)) *
      (∏ i : Fin 2, p base (z i)) +
      (∑ i : Fin 2, p high (z i) *
        ∏ j ∈ (Finset.univ : Finset (Fin 2)).erase i, p base (z j)) = _
  have hz : p high (0 : E) = 0 := map_zero (p high)
  rw [hz, add_zero, one_mul]
  rw [Fin.prod_univ_two, Fin.sum_univ_two]
  simp only [he0, he1, Finset.prod_singleton, z, Fin.cons_zero, Fin.cons_one]

theorem oneHighVariationWeight_state_external_zero
    (S : PhysicalSpacesData) (base high : ℕ) (η : AnnularState S) :
    oneHighVariationWeight (pairGrading (stateGrading S) realGrading)
      base high 0
      (Fin.cons (η, (0 : ℝ))
        (fun _ : Fin 1 => ((0 : AnnularState S), (1 : ℝ)))) =
      2 * stateGrading S base η + stateGrading S high η := by
  have hstate (n : ℕ) :
      pairGrading (stateGrading S) realGrading n (η, (0 : ℝ)) =
        stateGrading S n η := by
    change stateGrading S n η + realGrading n (0 : ℝ) = _
    exact (congrArg (fun t : ℝ => stateGrading S n η + t) (realGrading n).map_zero').trans
      (add_zero _)
  have hparameter (n : ℕ) :
      pairGrading (stateGrading S) realGrading n ((0 : AnnularState S), (1 : ℝ)) = 1 := by
    change stateGrading S n (0 : AnnularState S) + realGrading n (1 : ℝ) = 1
    have hr : realGrading n (1 : ℝ) = 1 := by change |(1 : ℝ)| = 1; norm_num
    exact (congrArg₂ (fun a b : ℝ => a + b) (stateGrading S n).map_zero' hr).trans
      (zero_add 1)
  have he := oneHighVariationWeight_finTwo_zero (pairGrading (stateGrading S) realGrading)
    base high (η, (0 : ℝ)) ((0 : AnnularState S), (1 : ℝ))
  apply he.trans
  calc
    _ = stateGrading S base η * 1 +
        (stateGrading S high η * 1 + 1 * stateGrading S base η) :=
      congrArg₂ (fun a b : ℝ => a + b)
        (congrArg₂ (fun a b : ℝ => a * b) (hstate base) (hparameter base))
        (congrArg₂ (fun a b : ℝ => a + b)
          (congrArg₂ (fun a b : ℝ => a * b) (hstate high) (hparameter base))
          (congrArg₂ (fun a b : ℝ => a * b) (hparameter high) (hstate base)))
    _ = _ := by ring

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
          (2 * stateGrading S base η + stateGrading S (hN.ordinaryFlowLoss 2) η) := by
  let hdata := hN.ordinaryFlowFamily_bound 2 0
  let B : ℝ := hdata.choose
  have hB : 0 < B := hdata.choose_spec.1
  have hpoint : ∀ (η : AnnularState S) (m : ℕ) (r θ : ℝ),
      r ∈ Ioo (C.left m) (C.right m) →
      |deriv (fun t : ℝ => deriv (fun q : ℝ =>
        C.minusFlow (C.referenceState + t • η, q) m r θ) 0) 0| ≤
        B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
          T.E0 (T.sample (C.cell m)) ^ B *
          (2 * stateGrading S base η + stateGrading S (hN.ordinaryFlowLoss 2) η) := by
    intro η m r θ hr
    let htower := hdata.choose_spec.2 m 0 0 (r, θ) (by norm_num) hr
    have hz : (C.referenceState, (0 : ℝ)) ∈ stateNeighborhood S C base ε := by
      constructor
      · have hz0 : stateGrading S base (C.referenceState - C.referenceState) = 0 :=
          (congrArg (fun v : AnnularState S => stateGrading S base v)
            (sub_self C.referenceState)).trans (stateGrading S base).map_zero'
        exact hz0.trans_lt hN.2.1
      · simpa only [abs_zero] using hN.2.1
    have hd := (ordinaryFlow_state_q_mixed_hasDerivAt_of_tower
      htower.choose C.referenceState η hz).deriv
    have hbound := htower.choose_spec (C.referenceState, 0) hz
      (Fin.cons (η, (0 : ℝ))
        (fun _ : Fin 1 => ((0 : AnnularState S), (1 : ℝ))))
    have hb' := le_of_zero_power_mul_le hbound
    have hw : oneHighVariationWeight (pairGrading (stateGrading S) realGrading)
        base (0 + hN.ordinaryFlowLoss 2) ((C.referenceState, (0 : ℝ)) - (C.referenceState, 0))
          (Fin.cons (η, (0 : ℝ)) (fun _ : Fin 1 => ((0 : AnnularState S), (1 : ℝ)))) =
        2 * stateGrading S base η + stateGrading S (hN.ordinaryFlowLoss 2) η := by
      exact (congrArg₂ (fun (n : ℕ) (x : AnnularState S × ℝ) =>
        oneHighVariationWeight (pairGrading (stateGrading S) realGrading) base n x
          (Fin.cons (η, (0 : ℝ))
            (fun _ : Fin 1 => ((0 : AnnularState S), (1 : ℝ)))))
        (Nat.zero_add (hN.ordinaryFlowLoss 2)) (sub_self (C.referenceState, (0 : ℝ)))).trans
          (oneHighVariationWeight_state_external_zero S base (hN.ordinaryFlowLoss 2) η)
    exact (congrArg abs hd).trans_le (hb'.trans_eq (congrArg
      (fun t : ℝ => B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
        T.E0 (T.sample (C.cell m)) ^ B * t) hw))
  exact Exists.intro B (And.intro hB hpoint)

end ContinuousFlexibility.Statements
