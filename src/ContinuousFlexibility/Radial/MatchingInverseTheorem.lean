module

public import ContinuousFlexibility.Radial.MatchingCoreLeftInverse
public import ContinuousFlexibility.Radial.MatchingKernel
public import ContinuousFlexibility.Radial.MatchingRepresentation

/-!
# The exact matched modal inverse

The bounded matching formula is the inverse of the original maximal
weak graph. Homogeneous uniqueness follows from local graph uniqueness
and the matching matrix. Smooth-core left inversion and the bordered
adjoint argument then give the full source and uniqueness properties.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open ContinuousFlexibility.Statements

theorem actualMatchedRepresentation_modeInverseProperties
    {D : ReferenceData} (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D)
    {G : RadialModePair D →L[ℝ] RadialModePair D} {M : RadialMatchingData D}
    (hactual : ActualMatchedRepresentation D G M) :
    ModeInverseProperties D M.frequency G := by
  apply modeInverseProperties_of_core_leftInverse hD hB M.frequency G
  · intro U hU
    exact actualMatchedRepresentation_kernel_eq_zero hD hB hactual hU
  · exact actualMatchedRepresentation_core_leftInverse hD hB hactual

end ContinuousFlexibility.Radial
