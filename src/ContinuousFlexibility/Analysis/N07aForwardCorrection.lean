module

public import ContinuousFlexibility.Analysis.N07aTameResidualComposition
public import ContinuousFlexibility.Analysis.N07aReturnCorrection
public import ContinuousFlexibility.Analysis.SolveNewtonBridge
public import ContinuousFlexibility.Analysis.SolveReturnEquations
public import ContinuousFlexibility.Analysis.SolveTameSubspace
public import ContinuousFlexibility.Analysis.TameInverseFamily
public import ContinuousFlexibility.Scalar.WeightedSmoothTameAlgebra
public import ContinuousFlexibility.Scalar.WeightedSmoothTameLinear

/-!
# The actual return correction in the normalized forward operator

The correction is the existing `L.error` evaluated at the existing return
residual.  N02 and N03 already give its two smooth tame ingredients.  Their
composition takes values in the physical source kernel, and its frozen
height maps are continuous linear maps on the whole common height space.

No forward equation or parameter estimate is introduced as an assumption
here: the decoder and the tame assertion are consequences of the frozen
N02 and N03 properties.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped Topology
open ContinuousFlexibility.Statements


section ResidualSubspace

variable {X Y H : Type*}
  [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace H] [AddCommGroup H] [Module ℝ H]
  {F : ℕ → Type*} [∀ n, NormedAddCommGroup (F n)] [∀ n, NormedSpace ℝ (F n)]
  [∀ n, CompleteSpace (F n)] {bond : ∀ n, F (n + 1) →L[ℝ] F n}
  {p : ℕ → Seminorm ℝ X} {q : ℕ → Seminorm ℝ Y} {r : ℕ → Seminorm ℝ H}
  {t : ℕ → Seminorm ℝ (ProjectiveLimit F bond)}
  {U : Set X} {R : X → Y}

local instance n07aForwardCorrectionKernelGroup
    (W : Submodule ℝ (ProjectiveLimit F bond)) : AddCommGroup W :=
  Submodule.addCommGroup W
local instance n07aForwardCorrectionKernelModule
    (W : Submodule ℝ (ProjectiveLimit F bond)) : Module ℝ W :=
  Submodule.module W

theorem n07a_tameResidualComposition_submodule
    (W : Submodule ℝ (ProjectiveLimit F bond))
    (hW : IsClosed (W : Set (ProjectiveLimit F bond)))
    (Q : X → Y → H → W)
    (hp : Monotone p) (hr : Monotone r)
    (htp : WithSeminorms p) (htq : WithSeminorms q) (htr : WithSeminorms r)
    (hR : SmoothTameOn p q U R)
    (hQ : SmoothTameOn (E := (X × Y) × H) (F := W) (pairGrading (pairGrading p q) r)
      (fun n => (t n).comp W.subtype) ((U ×ˢ univ) ×ˢ univ)
      (fun z : (X × Y) × H => Q z.1.1 z.1.2 z.2)) :
    SmoothTameOn (E := X × H) (F := W)
      (pairGrading p r) (fun n => (t n).comp W.subtype) (U ×ˢ univ)
      (fun z : X × H => Q z.1 (R z.1) z.2) := by
  let : IsTopologicalAddGroup X := htp.isTopologicalAddGroup
  let : ContinuousSMul ℝ X := htp.continuousSMul
  let : IsTopologicalAddGroup Y := htq.isTopologicalAddGroup
  let : ContinuousSMul ℝ Y := htq.continuousSMul
  let : IsTopologicalAddGroup H := htr.isTopologicalAddGroup
  let : ContinuousSMul ℝ H := htr.continuousSMul
  have hQv := solve_smoothTameOn_postcomp (r := t) hQ W.subtypeL
    (B := 1) zero_le_one (fun n u => by
      change t n u.val ≤ 1 * t n u.val
      rw [one_mul])
  have hc := n07a_tameResidualComposition (t := t)
    (Q := fun x y h => (Q x y h : ProjectiveLimit F bond)) hp hr htp htq htr hR hQv
  exact solve_smoothTameOn_codRestrict W hW hc
    (fun z : X × H => Q z.1 (R z.1) z.2) (fun _ _ => rfl)

end ResidualSubspace

set_option backward.isDefEq.respectTransparency false

local instance n07aForwardCorrectionStateGroup (S : PhysicalSpacesData) : AddCommGroup (StateDirections S) :=
  n07aNonlinearDirectionsGroup S
local instance n07aForwardCorrectionStateModule (S : PhysicalSpacesData) : Module ℝ (StateDirections S) :=
  n07aNonlinearDirectionsModule S
local instance n07aForwardCorrectionHeightGroup (S : PhysicalSpacesData) : AddCommGroup (HeightPair S) := inferInstance
local instance n07aForwardCorrectionHeightModule (S : PhysicalSpacesData) : Module ℝ (HeightPair S) := inferInstance
local instance n07aForwardCorrectionCircleGroup (S : PhysicalSpacesData) : AddCommGroup (CircleSpace S) := inferInstance
local instance n07aForwardCorrectionCircleModule (S : PhysicalSpacesData) : Module ℝ (CircleSpace S) := inferInstance
local instance n07aForwardCorrectionSourceGroup (S : PhysicalSpacesData) : AddCommGroup S.Source := inferInstance
local instance n07aForwardCorrectionSourceModule (S : PhysicalSpacesData) : Module ℝ S.Source := inferInstance

local instance n07aForwardCorrectionStateTopology (S : PhysicalSpacesData) : TopologicalSpace (StateDirections S) := inferInstance
local instance n07aForwardCorrectionHeightTopology (S : PhysicalSpacesData) : TopologicalSpace (HeightPair S) := inferInstance
local instance n07aForwardCorrectionCircleTopology (S : PhysicalSpacesData) : TopologicalSpace (CircleSpace S) := inferInstance
local instance n07aForwardCorrectionSourceTopology (S : PhysicalSpacesData) : TopologicalSpace S.Source := inferInstance

local instance n07aForwardCorrectionStateAddGroup (S : PhysicalSpacesData) : AddGroup (StateDirections S) :=
  n07aNonlinearDirectionsAddGroup S
local instance n07aForwardCorrectionStateSMul (S : PhysicalSpacesData) : SMul ℝ (StateDirections S) :=
  n07aNonlinearDirectionsSMul S
local instance n07aForwardCorrectionParameterGroup (S : PhysicalSpacesData) :
    AddCommGroup (StateDirections S × ℝ) := n07aNonlinearSectorParameterGroup S
local instance n07aForwardCorrectionParameterModule (S : PhysicalSpacesData) :
    Module ℝ (StateDirections S × ℝ) := n07aNonlinearSectorParameterModule S
local instance n07aForwardCorrectionParameterAddGroup (S : PhysicalSpacesData) :
    AddGroup (StateDirections S × ℝ) := n07aNonlinearSectorParameterAddGroup S
local instance n07aForwardCorrectionParameterSMul (S : PhysicalSpacesData) :
    SMul ℝ (StateDirections S × ℝ) := n07aNonlinearSectorParameterSMul S
local instance n07aForwardCorrectionHeightAddGroup (S : PhysicalSpacesData) :
    AddGroup (HeightPair S) := (inferInstance : AddCommGroup (HeightPair S)).toAddGroup
local instance n07aForwardCorrectionHeightSMul (S : PhysicalSpacesData) :
    SMul ℝ (HeightPair S) := (inferInstance : Module ℝ (HeightPair S)).toSMul
local instance n07aForwardCorrectionCircleAddGroup (S : PhysicalSpacesData) :
    AddGroup (CircleSpace S) := (inferInstance : AddCommGroup (CircleSpace S)).toAddGroup
local instance n07aForwardCorrectionCircleSMul (S : PhysicalSpacesData) :
    SMul ℝ (CircleSpace S) := (inferInstance : Module ℝ (CircleSpace S)).toSMul
local instance n07aForwardCorrectionSourceAddGroup (S : PhysicalSpacesData) :
    AddGroup S.Source := (inferInstance : AddCommGroup S.Source).toAddGroup
local instance n07aForwardCorrectionSourceSMul (S : PhysicalSpacesData) :
    SMul ℝ S.Source := (inferInstance : Module ℝ S.Source).toSMul

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {base : ℕ} {ε : ℝ}

set_option backward.isDefEq.respectTransparency true in
/-- N02 and N03 imply the joint smooth tame assertion for the true
correction. The proof temporarily includes the source kernel in its
physical height space to use the existing projective composition theorem. -/
theorem n07aReturnCorrection_smoothTame
    (hS : IsPhysicalSpaces D T S)
    (h02 : N02Properties D T S C R base ε)
    (h03 : N03Properties D T S C R L base ε) :
    SmoothTameOn (E := (StateDirections S × ℝ) × HeightPair S) (F := S.Source)
      (n07aParameterHeightGrading S)
      S.sourceGrading (sectorNeighborhood S base ε ε ×ˢ univ)
      (fun z : (StateDirections S × ℝ) × HeightPair S =>
        n07aReturnCorrection C R L z.1 z.2) := by
  let : ∀ n, CompleteSpace ((S.height (3 / 4 : ℝ)).level n) := fun n =>
    SobolevModelData.completeSpace_level_of_isSobolevModel (hS.1 _) n
  exact n07a_tameResidualComposition_submodule
    (X := StateDirections S × ℝ) (Y := CircleSpace S) (H := HeightPair S)
    (F := fun n => (S.height (3 / 4 : ℝ)).level n)
    (bond := (S.height (3 / 4 : ℝ)).bond)
    (R := fun z => R.residual (liftSectorParameter S C z))
    (p := n07aParameterGrading S) (q := (S.circle (3 / 4 : ℝ)).grading)
    (r := heightPairGrading S) (t := (S.height (3 / 4 : ℝ)).grading)
    S.Q.toLinearMap.ker S.Q.isClosed_ker
    (fun z r u => L.error (liftSectorParameter S C z) r u)
    (n07aParameterGrading_monotone S)
    (tamePairGrading_monotone (gradedSeminorm_monotone _ _)
      weighted_realGrading_monotone)
    (n07aParameterGrading_withSeminorms S) (withSeminorms_graded _ _)
    (withSeminorms_pairGrading (withSeminorms_graded _ _)
      weighted_realGrading_withSeminorms)
    h02.2.2.2.2.2.2.2.2.2.2 h03.2.2.2.2.2.2.2.1

theorem n07aReturnCorrection_continuousOn
    (hS : IsPhysicalSpaces D T S)
    (h02 : N02Properties D T S C R base ε)
    (h03 : N03Properties D T S C R L base ε) :
    ContinuousOn
      (fun z : (StateDirections S × ℝ) × HeightPair S =>
        n07aReturnCorrection C R L z.1 z.2)
      (sectorNeighborhood S base ε ε ×ˢ univ) := by
  let J := (n07aReturnCorrection_smoothTame hS h02 h03).choose
  exact J.continuousOn

/-- The actual correction, with continuity proved from N02 and N03. -/
def n07aReturnCorrectionCLM
    (hS : IsPhysicalSpaces D T S)
    (h02 : N02Properties D T S C R base ε)
    (h03 : N03Properties D T S C R L base ε)
    (z : StateDirections S × ℝ) : HeightPair S →L[ℝ] S.Source :=
  inverseFamilyContinuousLinearMap (n07aReturnCorrection C R L)
    (n07aReturnCorrection_continuousOn hS h02 h03) z

theorem n07aReturnCorrectionCLM_apply
    (hS : IsPhysicalSpaces D T S)
    (h02 : N02Properties D T S C R base ε)
    (h03 : N03Properties D T S C R L base ε)
    {z : StateDirections S × ℝ} (hz : z ∈ sectorNeighborhood S base ε ε)
    (u : HeightPair S) :
    n07aReturnCorrectionCLM hS h02 h03 z u = n07aReturnCorrection C R L z u :=
  inverseFamilyContinuousLinearMap_apply _ _ hz u

theorem n07aReturnCorrectionCLM_smoothTame
    (hS : IsPhysicalSpaces D T S)
    (h02 : N02Properties D T S C R base ε)
    (h03 : N03Properties D T S C R L base ε) :
    SmoothTameOn (E := (StateDirections S × ℝ) × HeightPair S) (F := S.Source)
      (n07aParameterHeightGrading S)
      S.sourceGrading (sectorNeighborhood S base ε ε ×ˢ univ)
      (fun z : (StateDirections S × ℝ) × HeightPair S =>
        n07aReturnCorrectionCLM hS h02 h03 z.1 z.2) := by
  exact smoothTameOn_congr (n07aReturnCorrection_smoothTame hS h02 h03)
    (fun z hz => (n07aReturnCorrectionCLM_apply hS h02 h03 hz.1 z.2).symm)

end ContinuousFlexibility.Analysis
