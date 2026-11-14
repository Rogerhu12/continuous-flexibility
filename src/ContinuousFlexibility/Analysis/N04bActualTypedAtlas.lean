module

public import ContinuousFlexibility.Analysis.N04bActualNegativePiece
public import ContinuousFlexibility.Analysis.N04bTypedAtlasNegative

/-!
# The actual family of negative functions and the concrete final atlas

Each valid state uses a triple provided by the genuine negative-piece
existence theorem. Outside the required neighborhood and sector the total
functions use the same constructed reference triple. The final record
computes all physical domains, reference optical cuts, positive charts,
and actual coordinate operator fields from these chosen functions.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements

abbrev N04bNegativeFunctionTriple :=
  (PolarPoint → PolarPoint) × (PolarPoint → ℝ) × (PolarPoint → PolarPoint)

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}

theorem n04b_profileGeometry_of_through03
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε) :
    RadialProfileGeometry D := by
  obtain ⟨_, hdata⟩ := hN.1.1.1.1
  exact hdata.1

theorem n04b_reference_valid_of_through03
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε) :
    (C.referenceState, 0) ∈ stateNeighborhood S C base ε ∧
      stateSector S C.referenceState := by
  refine ⟨?_, n04b_referenceState_sector hN.1.1.2.2.1⟩
  have hε : 0 < ε := hN.1.1.2.1
  exact reference_mem_stateNeighborhood S C base hε

variable
  (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
  (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
  (hfield : N04bFieldRegularity D S C L base ε)

include hT hS hN hfield in
theorem n04b_exists_actual_negative_triple
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (side : Bool) :
    ∃ f : N04bNegativeFunctionTriple,
      N04bNegativePieceProperties S C L z m side f.1 f.2.1 f.2.2 := by
  obtain ⟨F, h, J, H⟩ := n04b_exists_actual_negative_piece hT hS hN hfield hz hs m side
  exact ⟨(F, h, J), H⟩

/-- A total family obtained from actual constructed triples, with an
actual reference triple as the harmless value outside the required sector. -/
def n04bActualNegativeFunctions (z : AnnularState S × ℝ) (m : ℕ) (side : Bool) :
    N04bNegativeFunctionTriple := by
  classical
  exact if hz : z ∈ stateNeighborhood S C base ε ∧ stateSector S z.1 then
    Classical.choose (n04b_exists_actual_negative_triple hT hS hN hfield hz.1 hz.2 m side)
  else
    Classical.choose (n04b_exists_actual_negative_triple hT hS hN hfield
      (n04b_reference_valid_of_through03 hN).1
      (n04b_reference_valid_of_through03 hN).2 m side)

def n04bActualNegativeChart (z : AnnularState S × ℝ) (m : ℕ) (side : Bool) :
    PolarPoint → PolarPoint :=
  (n04bActualNegativeFunctions hT hS hN hfield z m side).1

def n04bActualNegativeHeight (z : AnnularState S × ℝ) (m : ℕ) (side : Bool) :
    PolarPoint → ℝ :=
  (n04bActualNegativeFunctions hT hS hN hfield z m side).2.1

def n04bActualNegativeInverse (z : AnnularState S × ℝ) (m : ℕ) (side : Bool) :
    PolarPoint → PolarPoint :=
  (n04bActualNegativeFunctions hT hS hN hfield z m side).2.2

include hT hS hN hfield in
theorem n04bActualNegativeFunctions_spec
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (side : Bool) :
    N04bNegativePieceProperties S C L z m side
      (n04bActualNegativeChart hT hS hN hfield z m side)
      (n04bActualNegativeHeight hT hS hN hfield z m side)
      (n04bActualNegativeInverse hT hS hN hfield z m side) := by
  unfold n04bActualNegativeChart n04bActualNegativeHeight n04bActualNegativeInverse
    n04bActualNegativeFunctions
  rw [dif_pos ⟨hz, hs⟩]
  exact Classical.choose_spec
    (n04b_exists_actual_negative_triple hT hS hN hfield hz hs m side)

/-- The reference radial cut is the actual optical half-travel cut. -/
def n04bActualReferenceCut : ℕ → ℝ :=
  n04bReferenceTravelCut (n04b_profileGeometry_of_through03 hN) hN.1.1.2.2.2.1

theorem n04bActualReferenceCut_mem (m : ℕ) :
    n04bActualReferenceCut hN m ∈ Ioo (C.left m) (C.right m) :=
  (n04bReferenceTravelCut_spec
    (n04b_profileGeometry_of_through03 hN) hN.1.1.2.2.2.1 m).1

/-- One equivalence indexes every field of this genuine atlas. Its
negative functions are the actual existence witnesses chosen above. -/
def n04bActualTypedAtlas (e : ℕ ≃ N04PieceIndex D) : CanonicalData S :=
  n04bTypedAtlasData D S C L (n04bActualReferenceCut hN) e
    (n04bActualNegativeChart hT hS hN hfield)
    (n04bActualNegativeHeight hT hS hN hfield)
    (n04bActualNegativeInverse hT hS hN hfield)

end ContinuousFlexibility.Analysis
