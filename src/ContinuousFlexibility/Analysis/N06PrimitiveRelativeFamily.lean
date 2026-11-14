module

public import ContinuousFlexibility.Analysis.N06PrimitiveJetRescaling
public import ContinuousFlexibility.Analysis.N06OperatorExtension

/-!
# Selecting the actual relative family on the retained N05 graph

A relative endomorphism is selected at every admitted actual state, and
is zero elsewhere. The physical operator is the source projection plus
that selected endomorphism. No continuity in the state is required, and
the original N05 inverse right identity identifies its relative operator.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis CanonicalGeometry

set_option backward.isDefEq.respectTransparency true

attribute [local instance]
  n07aNonlinearAnnularGroup n07aNonlinearAnnularModule
  n07aNonlinearAnnularAddGroup n07aNonlinearAnnularSMul n07aNonlinearAnnularSub
  n07aNonlinearAnnularParameterGroup n07aNonlinearAnnularParameterModule
  n07aNonlinearAnnularParameterAddGroup n07aNonlinearAnnularParameterSMul
  n07aNonlinearAnnularParameterSub
  n07aNonlinearDirectionsGroup n07aNonlinearDirectionsModule
  n07aNonlinearDirectionsAddGroup n07aNonlinearDirectionsSMul n07aNonlinearDirectionsSub
  n07aNonlinearSectorParameterGroup n07aNonlinearSectorParameterModule
  n07aNonlinearSectorParameterAddGroup n07aNonlinearSectorParameterSMul
  n07aNonlinearSectorParameterSub

private theorem n06_select_total_relative_family
    {Z E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (admitted : Z → Prop) (ρ : Z → ℝ) (Q : ℝ)
    (Physical : Z → (E →L[ℝ] E) → Prop)
    (h : ∀ z, admitted z → ∃ M : E →L[ℝ] E,
      ‖M‖ ≤ Q * ρ z ∧ Physical z M) :
    ∃ R : Z → E →L[ℝ] E,
      (∀ z, admitted z → ‖R z‖ ≤ Q * ρ z ∧ Physical z (R z)) ∧
      ∀ z, ¬admitted z → R z = 0 := by
  classical
  let R : Z → E →L[ℝ] E := fun z =>
    if hz : admitted z then (h z hz).choose else 0
  refine ⟨R, ?_, ?_⟩
  · intro z hz
    dsimp only [R]
    rw [dif_pos hz]
    exact (h z hz).choose_spec
  · intro z hz
    exact dif_neg hz

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S}
  {V : VolumeModelData S K} {b base loss : ℕ} {ε : ℝ}
  {B : CanonicalDomainData S K V b}

local instance n06PrimitiveRelativeFamilyLevelGroup :
    NormedAddCommGroup (V.level (3 / 4 : ℝ) 0 b) := Submodule.normedAddCommGroup _
local instance n06PrimitiveRelativeFamilyLevelSpace :
    NormedSpace ℝ (V.level (3 / 4 : ℝ) 0 b) := Submodule.normedSpace _
local instance n06PrimitiveRelativeFamilyGraphGroup : NormedAddCommGroup B.Space :=
  Submodule.normedAddCommGroup _
local instance n06PrimitiveRelativeFamilyGraphSpace : NormedSpace ℝ B.Space :=
  Submodule.normedSpace _

/-- Pointwise actual sources give a total physical operator family on the
same graph, with the same uniform order and constant. -/
theorem n06_exists_primitiveRelativeFamily
    (h : NonlinearPropertiesThrough05 D T S C R L K V b B base loss ε)
    (order : ℕ) (Q : ℝ)
    (hstate : ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      ∃ M : V.level (3 / 4 : ℝ) 0 b →L[ℝ] V.level (3 / 4 : ℝ) 0 b,
        ‖M‖ ≤ Q * (stateGrading S order (z.1 - C.referenceState) + |z.2|) ∧
        ∀ u : B.Space, PerturbedCanonicalRelation D S C K L z u.val.1
          (V.forget (3 / 4 : ℝ) 0 b (n06OperatorFromRelative B M u))) :
    ∃ P : AnnularState S × ℝ → B.Space →L[ℝ] V.level (3 / 4 : ℝ) 0 b,
      (∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
        ∀ u : B.Space, PerturbedCanonicalRelation D S C K L z u.val.1
          (V.forget (3 / 4 : ℝ) 0 b (P z u))) ∧
      (∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
        ‖n06RelativeOperator P z‖ ≤
          Q * (stateGrading S order (z.1 - C.referenceState) + |z.2|)) ∧
      ∀ z, ¬(z ∈ stateNeighborhood S C base ε ∧ stateSector S z.1) →
        n06RelativeOperator P z = 0 := by
  obtain ⟨M, hM, hzero⟩ := n06_select_total_relative_family
    (fun z : AnnularState S × ℝ => z ∈ stateNeighborhood S C base ε ∧ stateSector S z.1)
    (fun z => stateGrading S order (z.1 - C.referenceState) + |z.2|) Q
    (fun z M => ∀ u : B.Space, PerturbedCanonicalRelation D S C K L z u.val.1
      (V.forget (3 / 4 : ℝ) 0 b (n06OperatorFromRelative B M u)))
    (fun z hz => hstate z hz.1 hz.2)
  let P : AnnularState S × ℝ → B.Space →L[ℝ] V.level (3 / 4 : ℝ) 0 b :=
    fun z => n06OperatorFromRelative B (M z)
  have hright : ∀ F : V.level (3 / 4 : ℝ) 0 b, (B.inverse F).val.2 = F :=
    h.2.2.2.2.2.2.2.2.1
  have hrelative (z : AnnularState S × ℝ) : n06RelativeOperator P z = M z :=
    n06RelativeOperator_fromRelative B M hright z
  refine ⟨P, fun z hz hs => (hM z ⟨hz, hs⟩).2, ?_, ?_⟩
  · intro z hz hs
    exact (congrArg norm (hrelative z)).le.trans (hM z ⟨hz, hs⟩).1
  · intro z hz
    exact (hrelative z).trans (hzero z hz)

/-- Sector-parameter outputs become actual-state outputs without changing
any state seminorm, the neighborhood, or the selected inverse. -/
theorem n06_primitiveRelativeState_of_sector
    (href : referenceStateConditions D S C) (order : ℕ) (Q : ℝ)
    (hsector : ∀ w ∈ sectorNeighborhood S base ε ε,
      ∃ M : V.level (3 / 4 : ℝ) 0 b →L[ℝ] V.level (3 / 4 : ℝ) 0 b,
        ‖M‖ ≤ Q * parameterGrading S order w ∧
        ∀ u : B.Space, PerturbedCanonicalRelation D S C K L (liftSectorParameter S C w)
          u.val.1 (V.forget (3 / 4 : ℝ) 0 b (n06OperatorFromRelative B M u))) :
    ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      ∃ M : V.level (3 / 4 : ℝ) 0 b →L[ℝ] V.level (3 / 4 : ℝ) 0 b,
        ‖M‖ ≤ Q * (stateGrading S order (z.1 - C.referenceState) + |z.2|) ∧
        ∀ u : B.Space, PerturbedCanonicalRelation D S C K L z u.val.1
          (V.forget (3 / 4 : ℝ) 0 b (n06OperatorFromRelative B M u)) := by
  intro z hz hs
  obtain ⟨M, hM, hphysical⟩ := hsector (n06PrimitiveParameterOfState href z hs)
    (n06PrimitiveParameterOfState_mem href hz hs)
  refine ⟨M, hM.trans_eq (congrArg (fun r : ℝ => Q * r)
    (n06PrimitiveParameterOfState_grading href z hs order)), ?_⟩
  exact n06PrimitiveParameterOfState_lift href z hs ▸ hphysical

end ContinuousFlexibility.Statements
