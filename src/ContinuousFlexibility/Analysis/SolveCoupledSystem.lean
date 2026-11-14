module

public import ContinuousFlexibility.Analysis.SolveKernelApplication
public import ContinuousFlexibility.Analysis.SolveNormalization
public import ContinuousFlexibility.Analysis.SolveStateSpaces
public import ContinuousFlexibility.Analysis.SolveResidualSpaces
public import ContinuousFlexibility.Analysis.SolveReturnEquations

/-!
# Applying the quadratic-error iteration to the coupled annular system

The generic kernel application runs the iteration on normalized sector
directions. This module supplies the actual integral row, its normalized
reference direction, and the tangency of the actual coupled inverse. All
residual, inverse, and quadratic-error data are the same data supplied by N10.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

theorem solve_coupled_exists_normalized_zero
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {G : ScalarInverseData S}
    {P : ResidualData S} {B : ControlColumnData S} {N : ControlInverseData S}
    {V : CoupledInverseData S} {Q : QuadraticErrorData S}
    {base loss : ℕ} {ε q0 : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h1 : N01Properties D T S C base loss ε)
    (hG : ScalarInverseProperties D S C L G base ε)
    (h8 : N08Properties D T S C R G P B base loss ε)
    (h9 : N09Properties D T S C R G B N V base ε q0)
    (h10 : N10Properties D S C R L P B V Q base ε q0) :
    ∃ x : AnnularState S, ∃ τ : ℝ, τ ≠ 0 ∧
      (x, τ) ∈ stateNeighborhood S C base ε ∧ stateSector S x ∧
      referenceRow D (stateU S x) = 1 ∧ jointResidual S P (x, τ) = 0 := by
  classical
  have h8' := h8
  rcases h8' with ⟨hclosed, _, _, _, hzero, _, _, _, _, _, _, _, _, _, _, _, _, hRTame, _⟩
  have h9' := h9
  rcases h9' with ⟨hq0, hqε, _, _, _, hVident, hVTame⟩
  have h10' := h10
  rcases h10' with ⟨_, _, _, _, hRight, hQTame⟩
  have href := h1.2.2.1
  let _ : ∀ n, CompleteSpace ((S.height (3 / 4 : ℝ)).level n) := fun n =>
    ((hS.1 (3 / 4 : ℝ)).2.1 n).completeSpace_coe
  let _ : ∀ n, CompleteSpace ((S.circle (3 / 4 : ℝ)).level n) := fun n =>
    ((hS.2.1 (3 / 4 : ℝ)).2.1 n).completeSpace_coe
  let _ : IsUniformAddGroup ((S.height (3 / 4 : ℝ)).Space) :=
    (compatibleSubmodule (fun n => (S.height (3 / 4 : ℝ)).level n)
      (S.height (3 / 4 : ℝ)).bond).toAddSubgroup.isUniformAddGroup
  let _ : IsUniformAddGroup ((S.circle (3 / 4 : ℝ)).Space) :=
    (compatibleSubmodule (fun n => (S.circle (3 / 4 : ℝ)).level n)
      (S.circle (3 / 4 : ℝ)).bond).toAddSubgroup.isUniformAddGroup
  let _ : IsUniformAddGroup (StateDirections S) :=
    (stateSectorSubmodule S).toAddSubgroup.isUniformAddGroup
  let _ : CompleteSpace (StateDirections S) := hclosed.completeSpace_coe
  let row : StateDirections S →L[ℝ] ℝ :=
    sectorReferenceRowCLM (D := D) (T := T) (S := S) h1.1 hT hS
  let ψ : StateDirections S := ⟨C.referenceState, href.stateSector⟩
  have hψ : referenceRow D (stateU S ψ.val) = 1 := href.2.2.2.2.2
  have hψrow : row ψ = 1 :=
    (sectorReferenceRowCLM_apply (D := D) (T := T) (S := S) h1.1 hT hS ψ).trans hψ
  have hactual (z : StateDirections S × ℝ)
      (hz : z ∈ sectorNeighborhood S base ε q0) :
      liftSectorParameter S C z ∈ coupledNeighborhood S C base ε q0 := by
    constructor
    · simpa only [liftSectorParameter, add_sub_cancel_left, sectorGrading,
        Seminorm.comp_apply, Submodule.subtype_apply] using hz.1
    · exact hz.2
  have hVrow : ∀ z ∈ sectorNeighborhood S base ε q0, ∀ y : ResidualSpace S,
      row (V.sectorV z y) = 0 := by
    intro z hz y
    refine (sectorReferenceRowCLM_apply (D := D) (T := T) (S := S) h1.1 hT hS
      (V.sectorV z y)).trans ?_
    refine (congrArg (fun a : AnnularState S => referenceRow D (stateU S a))
      (hVident z hz y)).trans ?_
    exact N09Properties.referenceRow_coupledInverse_zero
      (D := D) (T := T) (S := S) (C := C) (R := R) (L := L) (G := G)
      (B := B) (N := N) (V := V) (base := base) (ε := ε) (q0 := q0)
      (z := liftSectorParameter S C z) h9 hG (hactual z hz)
      (referenceStateConditions.liftSectorParameter_sector
        (D := D) (S := S) (C := C) href z) y
  have hzeroSector : sectorJointResidual S C P (0, 0) = 0 := by
    simpa only [sectorJointResidual, liftSectorParameter, ZeroMemClass.coe_zero,
      add_zero] using hzero
  have hpoint : ∃ x : StateDirections S, ∃ τ : ℝ, τ ≠ 0 ∧
      (x, τ) ∈ sectorNeighborhood S base ε q0 ∧ row x = 0 ∧
      sectorJointResidual S C P (x, τ) = 0 :=
    solve_exists_nonzero_zero_in_ker
      (X := StateDirections S) (Y := ResidualSpace S)
      (F := SolveResidualLevel S) (f := solveResidualBond S)
      (sectorGrading S) (residualGrading S)
      (solve_sectorGrading_monotone S) (solve_sectorGrading_withSeminorms S)
      (solveResidualEquiv (D := D) (T := T) (S := S) hS)
      (solveResidualEquiv_grading_le (D := D) (T := T) (S := S) hS)
      (solve_residualGrading_le_two (D := D) (T := T) (S := S) hS)
      base ε q0 h1.2.1 hq0 hqε row ψ hψrow
      (sectorJointResidual S C P) V.sectorV
      (fun z => Q.Q (liftSectorParameter S C z)) hzeroSector
      (solve_sector_hasSmoothing (D := D) (T := T) (S := S) hS)
      (solve_residual_hasSmoothing (D := D) (T := T) (S := S) hS)
      hRTame hVTame hQTame hVrow hRight
  rcases hpoint with ⟨x, τ, hτ, hnear, hrow, hz⟩
  refine ⟨C.referenceState + x.val, τ, hτ, ?_, ?_, ?_, ?_⟩
  · exact liftSectorParameter_mem_stateNeighborhood
      (S := S) (C := C) (base := base) (ε := ε) (q0 := q0) (z := (x, τ)) hnear hqε
  · exact referenceStateConditions.liftSectorParameter_sector
      (D := D) (S := S) (C := C) href (x, τ)
  · exact referenceRow_affine_of_mem_kernel (D := D) (T := T) (S := S) (C := C)
      h1.1 hT hS href x hrow
  · simpa only [sectorJointResidual, liftSectorParameter] using hz

end ContinuousFlexibility.Analysis
