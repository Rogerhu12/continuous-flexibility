module

public import ContinuousFlexibility.Analysis.CanonicalCoefficientIdentities
public import ContinuousFlexibility.Analysis.CoordinateOperatorConstruction
public import ContinuousFlexibility.Analysis.PhysicalTransmissionTrace

/-!
# The actual negative potential and its ordinary jets

The existing constant-test identity identifies the stored potential with
the explicit inverse-chart potential on the whole canonical open piece.
Equality on this open set identifies every actual mixed derivative.
No coefficient regularity or derivative estimate is needed for this
identification; those belong to the subsequent quantitative argument.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint

set_option backward.isDefEq.respectTransparency false

/-- On a negative piece the type sign is positive, so the existing
constant-test formula is exactly the explicit inverse-chart potential. -/
theorem negativeCanonicalPotential_eqOn_inverseChartPotential
    {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hB : N04PartB S C L K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (hm : K.positive m = false) :
    EqOn (K.potential z m)
      (inverseChartPotential (L.coefficients z) (K.chart z m)
        (K.inverseChart z m) (K.height z m)) (canonicalOpen S K m) := by
  intro p hp
  simpa only [hm, Bool.false_eq_true, ite_false, one_mul, canonicalSource,
    inverseChartPotential] using canonicalPotential_eq_source_height hB hz hs m hp

/-- The equality identifies every mixed derivative in the actual open
canonical domain, including order zero. -/
theorem negativeCanonicalPotential_mixedDerivative_eq
    {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hB : N04PartB S C L K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (hm : K.positive m = false)
    (a b : ℕ) {p : PolarPoint} (hp : p ∈ canonicalOpen S K m) :
    mixedDerivative a b (K.potential z m) p =
      mixedDerivative a b
        (inverseChartPotential (L.coefficients z) (K.chart z m)
          (K.inverseChart z m) (K.height z m)) p :=
  mixedDerivative_eqOn_of_isOpen (isOpen_Ioo.prod isOpen_univ)
    (negativeCanonicalPotential_eqOn_inverseChartPotential hB hz hs m hm) a b hp

end ContinuousFlexibility.Analysis
