module

public import ContinuousFlexibility.Analysis.CanonicalJetNormalization
public import ContinuousFlexibility.Analysis.N04RealizationPrimitiveNormalization
public import ContinuousFlexibility.Analysis.N07aGeometryJetBounds
public import ContinuousFlexibility.Analysis.SolveReturnEquations

/-!
# Retaining the primitive jet certificate under final normalization

On every actual sector parameter all unit atoms are unchanged. Their
entire difference-jet map is therefore unchanged, so the existing genuine
directional tower and its fixed-loss bounds transport together.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency true

attribute [local instance]
  n07aNonlinearAnnularGroup n07aNonlinearAnnularModule
  n07aNonlinearAnnularAddGroup n07aNonlinearAnnularSMul n07aNonlinearAnnularSub
  n07aNonlinearAnnularParameterGroup n07aNonlinearAnnularParameterModule
  n07aNonlinearAnnularParameterAddGroup n07aNonlinearAnnularParameterSMul
  n07aNonlinearAnnularParameterSub
  n07aNonlinearDirectionsGroup n07aNonlinearDirectionsModule
  n07aNonlinearDirectionsAddGroup n07aNonlinearDirectionsSMul n07aNonlinearDirectionsSub
  n07aNonlinearSectorParameterGroup n07aNonlinearSectorParameterModule
  n07aNonlinearSectorParameterAddGroup n07aNonlinearSectorParameterSMul
  n07aNonlinearSectorParameterSub

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}

/-- Equality of the actual whole atom function, not only its values on a piece. -/
theorem n04Coordinates_atom_normalized_of_sector
    {z : AnnularState S × ℝ} (hz : stateSector S z.1)
    (m : ℕ) (v : CanonicalGeometry.Atom) :
    CanonicalGeometry.atom D T S C L (normalizedCanonicalData S K) z m v =
      CanonicalGeometry.atom D T S C L K z m v :=
  n04Realization_atom_normalized_of_sector hz m v

/-- The same reference, actual tower, auxiliary source and transmission
data satisfy the complete primitive-jet predicate after normalization. -/
theorem n04Coordinates_primitiveGeometryProperties_normalized
    {base : ℕ} {ε : ℝ} (hstate : referenceStateConditions D S C)
    (h : CanonicalGeometry.PrimitiveGeometryProperties D T S C L K base ε) :
    CanonicalGeometry.PrimitiveGeometryProperties D T S C L
      (normalizedCanonicalData S K) base ε :=
  n04Realization_primitiveGeometryProperties_normalized hstate h

end ContinuousFlexibility.Analysis
