import ContinuousFlexibility.Blueprint.Statements

/-!
# Geometry is preserved by replacing only operator fields

The actual domains, charts, boundary inverse germs, and normalization do
not depend on the coefficient, potential, or divided-difference fields.
The geometry structure is nevertheless indexed by the whole data record;
its proof must be transported by its fields rather than by definitional
equality of the two structure types.
-/

noncomputable section

namespace ContinuousFlexibility.Blueprint

open ContinuousFlexibility.Statements

/-- Changing precisely the three operator fields preserves the complete
actual-domain geometry, including the closed inverse germ contract. -/
theorem N04PartA.withOperatorFields
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (h : N04PartA D S C K base ε)
    (coefficients : (AnnularState S × ℝ) → ℕ → SymmetricCoefficients)
    (potential : (AnnularState S × ℝ) → ℕ → PolarPoint → ℝ)
    (dividedDifference : (AnnularState S × ℝ) → ℕ → SymmetricCoefficients) :
    N04PartA D S C
      { K with coefficients := coefficients, potential := potential,
        dividedDifference := dividedDifference } base ε :=
  { normalizationOpen := h.normalizationOpen
    normalizationSupport := h.normalizationSupport
    normalization := h.normalization
    referenceBounds := h.referenceBounds
    referencePositive := h.referencePositive
    referenceNegative := h.referenceNegative
    referencePartition := h.referencePartition
    referenceDomain := h.referenceDomain
    domains := h.domains
    partition := h.partition
    charts := h.charts
    boundary := h.boundary
    reflection := h.reflection
    inverseReflection := h.inverseReflection }

end ContinuousFlexibility.Blueprint
