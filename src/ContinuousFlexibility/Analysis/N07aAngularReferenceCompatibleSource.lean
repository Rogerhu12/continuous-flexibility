import ContinuousFlexibility.Analysis.N07aAngularReferenceSource

/-!
# The literal compatible source of the transported reference field

The interior differential is extended across the null interface set by
zero and combined with the original radial border column. Both natural
graph membership and canonical source realization use this same function.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements ContinuousFlexibility.Radial

def n07aReferenceCompatibleSource {S : PhysicalSpacesData} (D : ReferenceData)
    (K : CanonicalData S) (v : PolarPoint → ℝ) (μ : ℝ) (p : PolarPoint) : ℝ :=
  n07aReferenceInteriorDifferential D K v p + μ * (referenceColumn D p.1 * cosineMode 2 p.2)

end ContinuousFlexibility.Analysis
