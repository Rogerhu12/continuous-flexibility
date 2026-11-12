import ContinuousFlexibility.Statements.Nonlinear

/-!
# Named orders of the existing N01 variation bounds

These definitions are exact aliases for the last two conjuncts of the frozen
`N01Properties`. They make proof elimination independent of repeated expansion
of the projective state space. No new hypothesis or conclusion is introduced.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

/-- One order and one constant in the actual coefficient-variation bound.
Naming this body keeps existential elimination independent of the large
projective-space instance expressions. -/
def N01CoefficientJetBoundAtOrder (D : ReferenceData) (T : MaterialData)
    (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (base loss : ℕ) (ε : ℝ) (k s : ℕ) (B : ℝ) : Prop :=
  ∀ m i a b p, a + b ≤ s → p.1 ∈ D.cells m →
    ∃ J : SmoothDirections (stateNeighborhood S C base ε) (coefficientFamily D S C i a b p),
      ∀ z ∈ stateNeighborhood S C base ε, ∀ v : Fin k → (AnnularState S × ℝ),
        |J.D k z v| ≤ B * T.H (T.sample m) ^ (3 / 4 : ℝ) *
          T.E0 (T.sample m) ^ B *
          oneHighVariationWeight (pairGrading (stateGrading S) realGrading)
            base (s + loss) (z - (C.referenceState, 0)) v

def N01CoefficientJetBounds (D : ReferenceData) (T : MaterialData)
    (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (base loss : ℕ) (ε : ℝ) : Prop :=
  ∀ k s : ℕ, ∃ B : ℝ, 0 < B ∧ N01CoefficientJetBoundAtOrder D T S C base loss ε k s B

/-- The actual collar-weighted flow variation bound at one pair of orders. -/
def N01FlowJetBoundAtOrder (T : MaterialData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (base loss : ℕ) (ε : ℝ) (k s : ℕ) (B : ℝ) : Prop :=
  ∀ m a b p, a + b ≤ s → p.1 ∈ Ioo (C.left m) (C.right m) →
    ∃ J : SmoothDirections (stateNeighborhood S C base ε) (ordinaryFlowFamily S C m a b p),
      ∀ z ∈ stateNeighborhood S C base ε, ∀ v : Fin k → (AnnularState S × ℝ),
        min (p.1 - C.left m) (C.right m - p.1) ^ a * |J.D k z v| ≤
          B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
          T.E0 (T.sample (C.cell m)) ^ B *
          oneHighVariationWeight (pairGrading (stateGrading S) realGrading)
            base (s + loss) (z - (C.referenceState, 0)) v

def N01FlowJetBounds (T : MaterialData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (base loss : ℕ) (ε : ℝ) : Prop :=
  ∀ k s : ℕ, ∃ B : ℝ, 0 < B ∧ N01FlowJetBoundAtOrder T S C base loss ε k s B

theorem n01CoefficientJetBounds_of_properties
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (h : N01Properties D T S C base loss ε) :
    N01CoefficientJetBounds D T S C base loss ε := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hcoefficient, _⟩ := h
  exact hcoefficient

theorem n01FlowJetBounds_of_properties
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (h : N01Properties D T S C base loss ε) :
    N01FlowJetBounds T S C base loss ε := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hflow⟩ := h
  exact hflow

end ContinuousFlexibility.Analysis
