module

public import ContinuousFlexibility.Analysis.N07aParameterGrading
public import ContinuousFlexibility.Analysis.SolveReturnEquations

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

set_option backward.isDefEq.respectTransparency false

local instance n07aReturnCorrectionInst1 (S : PhysicalSpacesData) : AddGroup (StateDirections S) :=
  (Submodule.addCommGroup (stateSectorSubmodule S)).toAddGroup
local instance n07aReturnCorrectionInst2 (S : PhysicalSpacesData) : SMul ℝ (StateDirections S) :=
  (Submodule.module (stateSectorSubmodule S)).toSMul

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {base : ℕ} {ε : ℝ}

/-- The actual N03 correction, with the actual N02 residual inserted. -/
def n07aReturnCorrection (C : NonlinearGeometryData S)
    (R : ReturnEquationData S) (L : ReturnCorrectionData S)
    (z : StateDirections S × ℝ) : HeightPair S →ₗ[ℝ] S.Source :=
  L.error (liftSectorParameter S C z) (R.residual (liftSectorParameter S C z))

theorem n07aReturnCorrection_decode
    (href : referenceStateConditions D S C)
    (h03 : N03Properties D T S C R L base ε)
    {z : StateDirections S × ℝ} (hz : z ∈ sectorNeighborhood S base ε ε)
    (u : HeightPair S) {p : PolarPoint} (hp : p ∈ annularOpen D) :
    (S.height (3 / 4 : ℝ)).decode (n07aReturnCorrection C R L z u).val p =
      divergenceOperator (originalCoefficients D S C (liftSectorParameter S C z))
        (heightPairField S u) p -
      divergenceOperator (L.coefficients (liftSectorParameter S C z))
        (heightPairField S u) p := by
  have herror := h03.2.2.2.2.2.1
  exact (herror _ (liftSectorParameter_mem_stateNeighborhood hz le_rfl)
    (href.liftSectorParameter_sector z) u p hp).symm

end ContinuousFlexibility.Analysis
