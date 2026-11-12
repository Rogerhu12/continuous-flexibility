import ContinuousFlexibility.Analysis.CanonicalJetNormalization
import ContinuousFlexibility.Analysis.N07aGeometryJetBounds
import ContinuousFlexibility.Analysis.SolveReturnEquations

/-!
# Retaining the primitive jet certificate under final normalization

On every actual sector parameter all unit atoms are unchanged. Their
entire difference-jet map is therefore unchanged, so the existing genuine
directional tower and its fixed-loss bounds transport together.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

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
      CanonicalGeometry.atom D T S C L K z m v := by
  funext p
  cases v <;> try rfl
  all_goals
    by_cases hp : K.positive m = true <;>
      simp [CanonicalGeometry.atom, normalizedCanonicalData, hz, hp]

/-- The same reference, actual tower, auxiliary source and transmission
data satisfy the complete primitive-jet predicate after normalization. -/
theorem n04Coordinates_primitiveGeometryProperties_normalized
    {base : ℕ} {ε : ℝ} (hstate : referenceStateConditions D S C)
    (h : CanonicalGeometry.PrimitiveGeometryProperties D T S C L K base ε) :
    CanonicalGeometry.PrimitiveGeometryProperties D T S C L
      (normalizedCanonicalData S K) base ε := by
  rcases h with ⟨hradial, hprincipal, href, hcur, haux, htrans⟩
  have hreference (m : ℕ) (v : CanonicalGeometry.Atom) :
      CanonicalGeometry.atom D T S C L (normalizedCanonicalData S K)
          (C.referenceState, 0) m v =
        CanonicalGeometry.atom D T S C L K (C.referenceState, 0) m v :=
    n04Coordinates_atom_normalized_of_sector hstate.stateSector m v
  have hcurrent (z : CanonicalGeometry.Parameter S) (m : ℕ)
      (v : CanonicalGeometry.Atom) :
      CanonicalGeometry.atom D T S C L (normalizedCanonicalData S K)
          (liftSectorParameter S C z) m v =
        CanonicalGeometry.atom D T S C L K (liftSectorParameter S C z) m v :=
    n04Coordinates_atom_normalized_of_sector (hstate.liftSectorParameter_sector z) m v
  have hdifference :
      CanonicalGeometry.differenceJets D T S C L (normalizedCanonicalData S K) =
        CanonicalGeometry.differenceJets D T S C L K := by
    funext z v m i j p
    simp only [CanonicalGeometry.differenceJets, hcurrent, hreference]
  have href' : CanonicalGeometry.ReferenceJets D T S C L
      (normalizedCanonicalData S K) := by
    simpa only [CanonicalGeometry.ReferenceJets, hreference,
      normalizedCanonicalData_cell] using href
  have hcur' : CanonicalGeometry.CurrentJets D T S C L
      (normalizedCanonicalData S K) base ε := by
    simpa only [CanonicalGeometry.CurrentJets, hcurrent, hdifference,
      normalizedCanonicalData_cell] using hcur
  refine ⟨hradial, ?_, href', hcur', haux, htrans⟩
  rcases hprincipal with ⟨hfields, hbound⟩
  refine ⟨?_, hbound⟩
  intro m p hp
  simpa only [normalizedCanonicalData_coefficients,
    normalizedCanonicalData_potential_of_sector K hstate.stateSector] using hfields m p hp

end ContinuousFlexibility.Analysis
