import ContinuousFlexibility.Statements.Nonlinear

/-!
# The ordinary-flow loss at one parameter order

The N01 certificate chooses this loss before every spatial order,
component, point, state and direction.  These accessors retain that
choice and the actual ordinary-flow family.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set

local instance n01OrdinaryFlowLossStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul
local instance n01OrdinaryFlowLossParameterSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S × ℝ) := Prod.instSMul

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

/-- The additional loss supplied by N01 at the fixed parameter order. -/
def N01Properties.ordinaryFlowParameterLoss
    (hN : N01Properties D T S C base loss ε) (k : ℕ) : ℕ :=
  (hN.2.2.2.2.2.2.2.2.2.2.2.2 k).choose

/-- The original loss together with the selected parameter-order loss. -/
def N01Properties.ordinaryFlowLoss
    (hN : N01Properties D T S C base loss ε) (k : ℕ) : ℕ :=
  loss + hN.ordinaryFlowParameterLoss k

theorem N01Properties.le_ordinaryFlowLoss
    (hN : N01Properties D T S C base loss ε) (k : ℕ) :
    loss ≤ hN.ordinaryFlowLoss k :=
  Nat.le_add_right loss (hN.ordinaryFlowParameterLoss k)

/-- The same chosen loss works for all spatial orders and labels. -/
theorem N01Properties.ordinaryFlowFamily_bound
    (hN : N01Properties D T S C base loss ε) (k s : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ m a b p,
      a + b ≤ s → p.1 ∈ Ioo (C.left m) (C.right m) →
      ∃ J : SmoothDirections (stateNeighborhood S C base ε) (ordinaryFlowFamily S C m a b p),
        ∀ z ∈ stateNeighborhood S C base ε, ∀ v : Fin k → (AnnularState S × ℝ),
          min (p.1 - C.left m) (C.right m - p.1) ^ a * |J.D k z v| ≤
            B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
            T.E0 (T.sample (C.cell m)) ^ B *
            oneHighVariationWeight (pairGrading (stateGrading S) realGrading)
              base (s + hN.ordinaryFlowLoss k) (z - (C.referenceState, 0)) v := by
  simpa only [N01Properties.ordinaryFlowLoss, N01Properties.ordinaryFlowParameterLoss,
    Nat.add_assoc] using (hN.2.2.2.2.2.2.2.2.2.2.2.2 k).choose_spec s

end ContinuousFlexibility.Statements
