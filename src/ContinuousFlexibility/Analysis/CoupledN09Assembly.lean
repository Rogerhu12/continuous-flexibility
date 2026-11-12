import ContinuousFlexibility.Analysis.CoupledInverseRecovery
import ContinuousFlexibility.Analysis.SolveReturnEquations

/-!
# Assembly of the coupled control inverse

The two analytic inputs are the actual feedback norm bound and the smooth
tame property of the recovered sector map. All other clauses of N09 are
the two Neumann identities and the already proved recovery equations for
that same map.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {G : ScalarInverseData S} {P : ResidualData S} {B : ControlColumnData S}
  {base loss : ℕ} {ε q0 : ℝ}

/-- Translating a sector state by the reference state preserves exactly
the neighborhood used by the feedback estimate. -/
theorem coupled_feedback_smallness_of_sector
    (hRef : referenceStateConditions D S C)
    (hsmall : ∀ z ∈ sectorNeighborhood S base ε q0,
      ‖z.2 • controlFeedback S B G (liftSectorParameter S C z)‖ < (1 / 2 : ℝ)) :
    ∀ z ∈ coupledNeighborhood S C base ε q0, stateSector S z.1 →
      ‖z.2 • controlFeedback S B G z‖ < (1 / 2 : ℝ) := by
  intro z hz hs
  let d : StateDirections S := ⟨z.1 - C.referenceState,
    (stateSectorSubmodule S).sub_mem hs hRef.stateSector⟩
  let a : StateDirections S × ℝ := (d, z.2)
  have ha : a ∈ sectorNeighborhood S base ε q0 := ⟨hz.1, hz.2⟩
  have hlift : liftSectorParameter S C a = z := by
    apply Prod.ext
    · change C.referenceState + (z.1 - C.referenceState) = z.1
      exact (add_sub_assoc C.referenceState z.1 C.referenceState).symm.trans
        (add_sub_cancel_left C.referenceState z.1)
    · rfl
  have h := hsmall a ha
  change ‖(liftSectorParameter S C a).2 •
    controlFeedback S B G (liftSectorParameter S C a)‖ < (1 / 2 : ℝ) at h
  simpa only [hlift] using h

/-- The canonical control inverse and the original guarded recovery
satisfy every clause of N09 on a strip where the two analytic inputs hold. -/
theorem coupled_n09Properties_of_smallness_smoothTame
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h1 : N01Properties D T S C base loss ε)
    (h2 : N02Properties D T S C R base ε)
    (h8 : N08Properties D T S C R G P B base loss ε)
    (hqpos : 0 < q0) (hqle : q0 ≤ ε)
    (hsmall : ∀ z ∈ coupledNeighborhood S C base ε q0, stateSector S z.1 →
      ‖z.2 • controlFeedback S B G z‖ < (1 / 2 : ℝ))
    (htame : SmoothTameOn
      (pairGrading (pairGrading (sectorGrading S) realGrading) (residualGrading S))
      (sectorGrading S) (sectorNeighborhood S base ε q0 ×ˢ univ)
      (fun z : (StateDirections S × ℝ) × ResidualSpace S =>
        (coupledRecoveredInverseData hT hS h1 h2 h8).sectorV z.1 z.2)) :
    N09Properties D T S C R G B (coupledControlInverse S B G)
      (coupledRecoveredInverseData hT hS h1 h2 h8) base ε q0 := by
  refine ⟨hqpos, hqle, hsmall, ?_, ?_, ?_, htame⟩
  · intro z hz hs u
    exact ⟨coupledControlInverse_left B G z (hsmall z hz hs) u,
      coupledControlInverse_right B G z (hsmall z hz hs) u⟩
  · intro z hz hs y
    exact coupledRecoveredInverseData_recovery hT hS h1 h2 h8 hqle hsmall hz hs y
  · intro z _ y
    exact coupledRecoveredInverseData_sectorV hT hS h1 h2 h8 z y

/-- A version using the sector estimate directly, before translating back
to ambient state coordinates. -/
theorem coupled_n09Properties_of_sector_smallness_smoothTame
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h1 : N01Properties D T S C base loss ε)
    (h2 : N02Properties D T S C R base ε)
    (h8 : N08Properties D T S C R G P B base loss ε)
    (hqpos : 0 < q0) (hqle : q0 ≤ ε)
    (hsmall : ∀ z ∈ sectorNeighborhood S base ε q0,
      ‖z.2 • controlFeedback S B G (liftSectorParameter S C z)‖ < (1 / 2 : ℝ))
    (htame : SmoothTameOn
      (pairGrading (pairGrading (sectorGrading S) realGrading) (residualGrading S))
      (sectorGrading S) (sectorNeighborhood S base ε q0 ×ˢ univ)
      (fun z : (StateDirections S × ℝ) × ResidualSpace S =>
        (coupledRecoveredInverseData hT hS h1 h2 h8).sectorV z.1 z.2)) :
    N09Properties D T S C R G B (coupledControlInverse S B G)
      (coupledRecoveredInverseData hT hS h1 h2 h8) base ε q0 :=
  coupled_n09Properties_of_smallness_smoothTame hT hS h1 h2 h8 hqpos hqle
    (coupled_feedback_smallness_of_sector h1.2.2.1 hsmall) htame

end ContinuousFlexibility.Statements
