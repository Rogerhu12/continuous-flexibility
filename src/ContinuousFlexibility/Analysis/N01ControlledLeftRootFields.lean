module

public import ContinuousFlexibility.Analysis.N01ControlledLeftRootInput
public import ContinuousFlexibility.Analysis.RootInputOrdinaryJets

/-!
# Actual ordinary left-root fields on a common neighborhood

The same constructed flow and the same actual left angular lift are used
for the smooth extensions. Their ordinary jets obey one fixed loss,
including every root boundary jet. The positive root value is retained
for the subsequent radial power and height constructions.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

def N01ControlledLeftRootFieldsAtState
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (m : ℕ) (g : ℝ → ℝ) {R : ℝ} (hR : 0 < R)
    (κ δ Λ : ℝ) (loss : ℕ) (B : ℕ → ℝ) (z : AnnularState S × ℝ) : Prop :=
  let d := localizedRootDrift D S C (C.left m) 1 hR z
  let c := localizedRootSpeed D S C g (C.left m) 1 hR z
  N04FlowAngularControl (rootRescaledField d c δ) Λ ∧
    ∃ Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ,
      N04FlowEquations (rootRescaledField d c δ) Θ ∧
      let G := rootScaledInverseCoordinate Θ (stateLeftChart S z.1 m) (Real.sqrt δ)
      ContDiff ℝ ∞ G ∧
        (∀ x ζ θ, G (x, ζ, θ + Real.pi) = G (x, ζ, θ) + Real.pi) ∧
        (∀ θ, G (0, 0, θ) = stateLeftChart S z.1 m θ) ∧
        (∀ θ, δ * Real.sqrt δ * κ / 3 ≤ rootOddCoefficient G (0, θ)) ∧
        RootOrdinaryFieldJetBound (pairGrading (stateGrading S) realGrading)
          loss B (z - (C.referenceState, 0)) G

def N01ControlledLeftRootFieldsFamily
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (base loss : ℕ) (ε : ℝ) (m : ℕ) (g : ℝ → ℝ)
    {R : ℝ} (hR : 0 < R) (κ δ Λ : ℝ) (B : ℕ → ℝ) : Prop :=
  ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
    N01ControlledLeftRootFieldsAtState D S C m g hR κ δ Λ loss B z

/-- The angular field and odd coefficient are the genuine fixed smooth
extensions of the actual inverse flow. Constants precede every state,
and the loss increases by exactly one for the odd root substitution. -/
theorem n01_exists_common_left_root_ordinary_fields
    (hFlow : N04FlowJetsTarget)
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε) :
    ∃ newBase outLoss : ℕ, ∃ ε' : ℝ, base ≤ newBase ∧ 0 < ε' ∧ ε' ≤ ε ∧
      ∀ m : ℕ, ∃ g : ℝ → ℝ, ∃ R : ℝ, ∃ hR : 0 < R, ∃ κ : ℝ,
        ContDiff ℝ ∞ g ∧ 0 < g 0 ∧ 0 < κ ∧
        (∀ t : ℝ, -deriv D.w (C.left m + t) = t * g t) ∧
        N01ActualRootFieldGeometry D S C newBase ε' (C.left m) 1 g hR ∧
        ∀ Λ : ℝ, 0 < Λ → ∃ δ : ℝ, ∃ B : ℕ → ℝ,
          0 < δ ∧ δ ≤ R / 4 ∧ δ ≤ 1 ∧ (∀ s, 0 < B s) ∧
          N01ControlledLeftRootFieldsFamily D S C newBase outLoss ε'
            m g hR κ δ Λ B := by
  have hp : Monotone (pairGrading (stateGrading S) realGrading) :=
    tamePairGrading_monotone (stateGrading_monotone S) (fun _ _ _ => le_rfl)
  obtain ⟨newBase, inputLoss, ε', hb, hε', hεε, hroots⟩ :=
    n01_exists_common_left_root_inputs hFlow hS hT hN
  refine ⟨newBase, inputLoss + 1, ε', hb, hε', hεε, ?_⟩
  intro m
  obtain ⟨g, R, hR, κ, hg, hg0, hκ, hdivide, hgeometry, hflow⟩ := hroots m
  refine ⟨g, R, hR, κ, hg, hg0, hκ, hdivide, hgeometry, ?_⟩
  intro Λ hΛ
  obtain ⟨δ, A, hδ, hδR, hδone, hA, hinput⟩ := hflow Λ hΛ
  obtain ⟨B, hB, hordinary⟩ := exists_rootInput_ordinaryField_bound hp inputLoss A hA
  refine ⟨δ, B, hδ, hδR, hδone, hB, ?_⟩
  intro z hz hs
  obtain ⟨hcontrol, Θ, hΘ, hG, hperiod, hzero, hpositive, hjet⟩ := hinput z hz hs
  exact ⟨hcontrol, Θ, hΘ, hG, hperiod, hzero, hpositive,
    hordinary (z - (C.referenceState, 0))
      (rootScaledInverseCoordinate Θ (stateLeftChart S z.1 m) (Real.sqrt δ))
      hG hperiod hjet⟩

end ContinuousFlexibility.Analysis
