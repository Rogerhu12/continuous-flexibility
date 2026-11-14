module

public import ContinuousFlexibility.Analysis.N04PulledFieldsErrorJoint
public import ContinuousFlexibility.Analysis.N04PulledFieldsOriginalJoint
public import ContinuousFlexibility.Analysis.N04PulledFieldsCoefficientReconstruction

/-!
# Joint towers of the retained physical coefficients

The original coefficients and the actual correction error are combined
as literal functions before any inverse-chart substitution. This keeps
the whole physical annulus available for every moving chart point.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

local instance n04PulledFieldsCoefficientJointStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

set_option backward.isDefEq.respectTransparency false

/-- The genuine joint tower is for the retained corrected coefficient,
with the actual N02 residual already substituted. -/
def n04PulledFields_correctedCoefficientJointDirections
    (W : N04RealizationStart) (i : Fin 3) :
    SmoothDirections
      (sectorNeighborhood W.S W.base W.ε W.ε ×ˢ annularOpen W.D)
      (fun x : (StateDirections W.S × ℝ) × PolarPoint =>
        canonicalCoefficientComponent i
          (W.L.coefficients (liftSectorParameter W.S W.C x.1)) x.2) := by
  exact n04PulledFields_jointSubtraction_on
    (n04PulledFields_originalCoefficientJointDirections W.through03.1.1 W.hS W.hT i)
    (n04PulledFields_actualErrorJointDirections W.cutoff W.through03.1.1
      W.hS W.hT W.through03.1.2 (n04PulledFields_errorProjection i))
    (fun x hx => n04PulledFields_startCoefficient_sub_error W i x.1 hx.1 x.2 hx.2)

/-- Auxiliary replacement does not alter the actual physical coefficient
or its joint state/physical tower. -/
def n04PulledFields_gaugeCoefficientJointDirections
    (G : N04RealizationGauge) (η : (G.W.S.height (3 / 4 : ℝ)).Space) (i : Fin 3) :
    SmoothDirections
      (sectorNeighborhood (G.S η) G.W.base G.W.ε G.W.ε ×ˢ annularOpen G.W.D)
      (fun x : CanonicalGeometry.Parameter (G.S η) × PolarPoint =>
        G.coefficientField η i (G.lift η x.1) x.2) :=
  n04PulledFields_correctedCoefficientJointDirections G.W i

end ContinuousFlexibility.Analysis
