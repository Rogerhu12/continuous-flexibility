import ContinuousFlexibility.Analysis.N04PositiveGeometryEndpointBoundsRootMaterial
import ContinuousFlexibility.Analysis.N04PositiveGeometryEndpointBoundsRootPowerCalculus
import ContinuousFlexibility.Analysis.N01cStateInterpolation

/-!
# Fixed intrinsic angular shifts in the actual root inputs

The finite radial prefix is absorbed into one fixed interpolation loss.
Consequently its angular orders, and not the number of radial factors,
determine the spatial scale in each product. The same base is selected
before every parameter prefix. The input maps are the literal four
normalized height fields multiplied by the original scalar parameter.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

local instance n04PositiveRootShiftPowerStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}

/-- One base and one loss suffice for every parameter order of a fixed
finite radial and intrinsic angular prefix. The spatial scale counts
only the additional angular order b. The original `H^(3/4)` gain is kept even at zero
parameter order. -/
theorem n04PositiveGeometry_rootHeightInputs_finiteShift_power
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S)
    (hE : ∀ r ∈ radialCore D, 1 ≤ T.E0 r)
    (x0 : AnnularState S) (N requestedBase : ℕ) :
    N04PositiveGeometryRootHeightFiniteShiftPowerBound (stateGrading S)
      (fun i x => n06RootNormalizedHeightFields D S x.1 i) (annularOpen D)
      (fun q => T.E0 q.1) (fun q => T.H q.1 ^ scalarBeta) x0 N requestedBase := by
  exact n04PositiveGeometry_rootFiniteShift_power_of_raw
    (stateGrading S) (stateGrading_monotone S) (jointStateGrading_hasInterpolation hS)
    (fun i x => n06RootNormalizedHeightFields D S x.1 i) (annularOpen D)
    (fun q => T.E0 q.1) (fun q => T.H q.1 ^ scalarBeta)
    (fun q hq => hE q.1 hq.1)
    (fun q hq => Real.rpow_nonneg (hT.2.1 q.1 hq.1).2.1.le _)
    (fun s => n04PositiveGeometry_rootHeightInputs_material_oneHigh hD hT hS s)
    x0 N requestedBase

end ContinuousFlexibility.Analysis
