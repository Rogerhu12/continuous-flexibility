import ContinuousFlexibility.Analysis.CanonicalPrimitivePreservation
import ContinuousFlexibility.Analysis.SolveReturnEquations

/-!
# Preserving the complete primitive payload through operator normalization

The final normalization changes potential values only outside the admissible
sector and divided fields only where their atoms are unused. On every sector
state, every actual geometric atom is therefore the same complete function.
This equality preserves the spatial jets and their genuine directional tower,
with their original loss quantifiers and on the original neighborhood.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S}
  {K : CanonicalData S} {base : ℕ} {ε : ℝ}

/-- Each atom agrees as a complete spatial function on an admissible state.
In particular, no equality of isolated values is used to transport jets. -/
theorem n04Realization_atom_normalized_of_sector
    {z : AnnularState S × ℝ} (hz : stateSector S z.1) (m : ℕ) (a : Atom) :
    atom D T S C L (normalizedCanonicalData S K) z m a =
      atom D T S C L K z m a := by
  classical
  funext p
  cases hm : K.positive m <;> cases a <;>
    simp only [atom, normalizedCanonicalData, hz, hm, Bool.false_eq_true,
      true_and, ite_true, ite_false]

/-- The actual state-dependent difference-jet map is unchanged, including
its values at every spatial order. -/
theorem n04Realization_differenceJets_normalized
    (href : referenceStateConditions D S C) :
    differenceJets D T S C L (normalizedCanonicalData S K) =
      differenceJets D T S C L K := by
  funext z a m i j p
  simp only [differenceJets,
    n04Realization_atom_normalized_of_sector (z := liftSectorParameter S C z)
      (href.liftSectorParameter_sector z),
    n04Realization_atom_normalized_of_sector (z := (C.referenceState, 0)) href.stateSector]

/-- Reference regularity, periodicity and numerical spatial bounds retain
the same atom functions and constants. -/
theorem n04Realization_referenceJets_normalized
    (href : referenceStateConditions D S C)
    (h : ReferenceJets D T S C L K) :
    ReferenceJets D T S C L (normalizedCanonicalData S K) := by
  constructor
  · intro m a
    simpa only [n04Realization_atom_normalized_of_sector (z := (C.referenceState, 0))
      href.stateSector] using h.1 m a
  · intro s
    obtain ⟨B, hB, hb⟩ := h.2 s
    refine ⟨B, hB, ?_⟩
    intro m a p hp i j hij
    simpa only [n04Realization_atom_normalized_of_sector (z := (C.referenceState, 0))
      href.stateSector,
      normalizedCanonicalData_cell] using hb m a p hp i j hij

/-- The original directional tower is retained after equality transport;
no new variation estimate or loss is selected. -/
theorem n04Realization_currentJets_normalized
    (href : referenceStateConditions D S C)
    (h : CurrentJets D T S C L K base ε) :
    CurrentJets D T S C L (normalizedCanonicalData S K) base ε := by
  constructor
  · intro z hz m a
    simpa only [n04Realization_atom_normalized_of_sector
      (z := liftSectorParameter S C z)
      (href.liftSectorParameter_sector z)] using h.1 z hz m a
  · simpa only [n04Realization_differenceJets_normalized href,
      normalizedCanonicalData_cell] using h.2

/-- Reference principal coefficients are not modified. The reference
potential is retained because the reference state belongs to the sector. -/
theorem n04Realization_referencePrincipal_normalized
    (href : referenceStateConditions D S C)
    (h : ReferencePrincipal T S C K) :
    ReferencePrincipal T S C (normalizedCanonicalData S K) := by
  constructor
  · intro m p hp
    simpa only [normalizedCanonicalData_coefficients,
      normalizedCanonicalData_potential_of_sector K (z := (C.referenceState, 0))
        href.stateSector] using h.1 m p hp
  · exact h.2

/-- Every constituent of the construction-stage primitive payload survives
the same final operator normalization on the same witness and neighborhood. -/
theorem n04Realization_primitiveGeometryProperties_normalized
    (href : referenceStateConditions D S C)
    (h : PrimitiveGeometryProperties D T S C L K base ε) :
    PrimitiveGeometryProperties D T S C L (normalizedCanonicalData S K) base ε :=
  ⟨h.1, n04Realization_referencePrincipal_normalized href h.2.1,
    n04Realization_referenceJets_normalized href h.2.2.1,
    n04Realization_currentJets_normalized href h.2.2.2.1,
    h.2.2.2.2.1, h.2.2.2.2.2⟩

end ContinuousFlexibility.Analysis
