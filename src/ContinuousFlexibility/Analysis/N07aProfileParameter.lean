module

public import ContinuousFlexibility.Analysis.N07aProfileParameterJets
public import ContinuousFlexibility.Analysis.N07aHeightFamilyTame

/-!
# Smooth tameness of the actual controlled profile in the frozen height model

This instantiates the physical-family lifting theorem with the genuine
N01 q=0 coefficient towers. Its values are the actual profile differences,
and its base and derivative loss are the ones already given by N01.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

local instance n07aProfileParameterStateGroup (S : PhysicalSpacesData) :
    AddCommGroup (AnnularState S) := n07aNonlinearAnnularGroup S
local instance n07aProfileParameterStateModule (S : PhysicalSpacesData) :
    Module ℝ (AnnularState S) := n07aNonlinearAnnularModule S
local instance n07aProfileParameterStateTopology (S : PhysicalSpacesData) :
    TopologicalSpace (AnnularState S) := inferInstance
local instance n07aProfileParameterStateAddGroup (S : PhysicalSpacesData) :
    AddGroup (AnnularState S) := n07aNonlinearAnnularAddGroup S
local instance n07aProfileParameterStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := n07aNonlinearAnnularSMul S
local instance n07aProfileParameterStateSub (S : PhysicalSpacesData) :
    Sub (AnnularState S) := n07aNonlinearAnnularSub S
local instance n07aProfileParameterPairGroup (S : PhysicalSpacesData) :
    AddCommGroup (AnnularState S × ℝ) := n07aNonlinearAnnularParameterGroup S
local instance n07aProfileParameterPairModule (S : PhysicalSpacesData) :
    Module ℝ (AnnularState S × ℝ) := n07aNonlinearAnnularParameterModule S
local instance n07aProfileParameterPairAddGroup (S : PhysicalSpacesData) :
    AddGroup (AnnularState S × ℝ) := n07aNonlinearAnnularParameterAddGroup S
local instance n07aProfileParameterPairSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S × ℝ) := n07aNonlinearAnnularParameterSMul S
local instance n07aProfileParameterPairSub (S : PhysicalSpacesData) :
    Sub (AnnularState S × ℝ) := n07aNonlinearAnnularParameterSub S
local instance n07aProfileParameterTopGroup (S : PhysicalSpacesData) :
    IsTopologicalAddGroup (AnnularState S × ℝ) :=
  (n07aRawParameterGrading_withSeminorms S).isTopologicalAddGroup
local instance n07aProfileParameterContinuousSMul (S : PhysicalSpacesData) :
    ContinuousSMul ℝ (AnnularState S × ℝ) :=
  (n07aRawParameterGrading_withSeminorms S).continuousSMul
local instance n07aProfileParameterFirstCountable (S : PhysicalSpacesData) :
    FirstCountableTopology (AnnularState S × ℝ) :=
  (n07aRawParameterGrading_withSeminorms S).firstCountableTopology

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

/-- The actual profile height, with arbitrary zero values off the open
parameter domain. All assertions below concern the original domain. -/
def n07aProfileParameterHeight
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε) {γ : ℝ} (hγ : γ < 3 / 64)
    (z : AnnularState S × ℝ) : (S.height γ).Space := by
  classical
  exact if hz : z ∈ stateNeighborhood S C base ε then
    n07aProfileDifferenceHeight hS hT h01 hγ z.1
      ⟨hz.1, by simpa only [abs_zero] using (abs_nonneg z.2).trans_lt hz.2⟩ else 0

theorem n07aProfileParameterHeight_decode
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε) {γ : ℝ} (hγ : γ < 3 / 64)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε) :
    (S.height γ).decode (n07aProfileParameterHeight hS hT h01 hγ z) =
      n07aProfileDifferenceField D S C z.1 := by
  classical
  unfold n07aProfileParameterHeight
  rw [dite_eq_left hz]
  exact n07aProfileDifferenceHeight_decode hS hT h01 hγ z.1 _

set_option backward.isDefEq.respectTransparency true in
/-- The original N01 parameter family has a fixed-base, fixed-loss tame
estimate in every requested height weight strictly below 3/64. -/
theorem n07aProfileParameterHeight_fixedNeighborhoodSmoothTame
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε) {γ : ℝ} (hγ : γ < 3 / 64) :
    FixedNeighborhoodSmoothTame (E := AnnularState S × ℝ) (F := (S.height γ).Space)
      (n07aRawParameterGrading S) (S.height γ).grading
      (stateNeighborhood S C base ε) base loss
      (n07aProfileParameterHeight hS hT h01 hγ) := by
  apply n07a_heightFamily_fixedNeighborhoodSmoothTame
    (E := AnnularState S × ℝ) (δ := (3 / 64 : ℝ))
    (p := n07aRawParameterGrading S) (base := base) (loss := loss)
    (x₀ := (C.referenceState, 0))
    (hT := hT) (hA := hS.1 γ)
    (hU := n07aRawParameterNeighborhood_isOpen S C base ε)
    (hp := n07aRawParameterGrading_withSeminorms S)
    (hg := fun x hx => n07aProfileParameterHeight_decode hS hT h01 hγ hx)
    (J := n07aProfileParameterJet hS hT h01)
    (hJ := ?_) (hγδ := hγ) (hmono := n07aRawParameterGrading_monotone S)
  intro k s
  let data := n07aProfileParameterJet_decay_bound hS hT h01 k s
  let B : ℝ := data.choose
  have hB : 0 < B := data.choose_spec.1
  have hb := data.choose_spec.2
  refine ⟨B, hB.le, fun a b p hab x hx v => ?_⟩
  simpa only [oneHighVariationWeight, n07aRawParameterGrading_apply,
    n07aRawParameterVariation, B, data] using hb a b p hab x hx v

theorem n07aProfileParameterHeight_smoothTame
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε) {γ : ℝ} (hγ : γ < 3 / 64) :
    SmoothTameOn (E := AnnularState S × ℝ) (F := (S.height γ).Space)
      (n07aRawParameterGrading S) (S.height γ).grading
      (stateNeighborhood S C base ε)
      (n07aProfileParameterHeight hS hT h01 hγ) :=
  (n07aProfileParameterHeight_fixedNeighborhoodSmoothTame hS hT h01 hγ).1

end ContinuousFlexibility.Analysis
