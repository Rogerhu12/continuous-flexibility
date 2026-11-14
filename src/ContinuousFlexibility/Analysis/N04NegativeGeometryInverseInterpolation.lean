module

public import ContinuousFlexibility.Analysis.CanonicalStateInterpolation
public import ContinuousFlexibility.Analysis.N01cStateSeminorms
public import ContinuousFlexibility.Analysis.SectorParameterGeometry
public import ContinuousFlexibility.Analysis.TameSmoothingCalculus

/-!
# Interpolation for the inverse-circle parameter grading

Restriction of a grading to a linear subspace preserves its interpolation
constants. Applying this abstract fact avoids expanding the physical-state
products in the scalar interpolation argument.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

private theorem inverseBounds_interpolation_submodule
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (V : Submodule ℝ E) (hI : HasInterpolation p) :
    HasInterpolation (fun n => (p n).comp V.subtype) := by
  obtain ⟨b, l, hb⟩ := hI
  refine ⟨b, l, fun a b c ha hab hbc => ?_⟩
  obtain ⟨A, hA, hb⟩ := hb a b c ha hab hbc
  exact ⟨A, hA, fun z => hb z.val⟩

local instance n04NegativeGeometryInverseInterpolationStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

/-- The actual sector parameter has one fixed interpolation loss. -/
theorem n04NegativeGeometry_inverseBounds_parameterInterpolation
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) :
    HasInterpolation (pairGrading realGrading (pairGrading (sectorGrading S) realGrading)) := by
  have hr : Monotone realGrading := fun _ _ _ _ => le_rfl
  have hsector : HasInterpolation (sectorGrading S) :=
    inverseBounds_interpolation_submodule (stateGrading S) (stateSectorSubmodule S)
      (coordinate_hasInterpolation_stateGrading hS)
  exact coordinate_hasInterpolation_pair hr (sectorPairGrading_monotone S)
    coordinate_hasInterpolation_realGrading
    (coordinate_hasInterpolation_pair (sectorGrading_monotone S) hr
      hsector coordinate_hasInterpolation_realGrading)

end ContinuousFlexibility.Statements
