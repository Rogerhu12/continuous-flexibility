module

public import ContinuousFlexibility.Blueprint.CanonicalParts

/-!
# The qualitative coordinate clauses of the actual N04 construction

The reusable coordinate identities take the independently named qualitative
parts. They are literal conjuncts of the frozen cumulative N04 properties.
No coordinate witness is replaced by these projections.
-/

@[expose] public section

namespace ContinuousFlexibility.Statements

open ContinuousFlexibility.Blueprint

theorem n06_N04_qualitative_parts
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ} (h : N04Properties D T S C L K base loss ε) :
    N04PartA D S C K base ε ∧ N04PartB S C L K base ε := by
  exact ⟨h.1, h.2.1⟩

open Set

variable {D : ReferenceData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {K : CanonicalData S}
  {base : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}

/-- This is a consequence of the actual positive-domain clause, not an
additional assumption on the final nonlinear construction. -/
theorem n06_positivePhysicalPiece_eq_reference
    (hA : N04PartA D S C K base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) (hm : K.positive m = true) :
    physicalPieceOpen S K z m = referencePhysicalPieceOpen S K m :=
  (hA.domains z hz hs m).2.2.2.2.2.1 hm

theorem n06_physicalPieceClosed_eq_reference_rectangle
    (hA : N04PartA D S C K base ε) (m : ℕ)
    (hΩ : physicalPieceOpen S K z m = referencePhysicalPieceOpen S K m) :
    physicalPieceClosed S K z m =
      Icc (K.physicalLeft m) (K.physicalRight m) ×ˢ (univ : Set ℝ) := by
  rw [physicalPieceClosed, hΩ, referencePhysicalPieceOpen, closure_prod_eq,
    closure_Ioo (hA.referenceBounds m).1.ne, closure_univ]

theorem n06_mem_physicalPieceClosed_of_reference_rectangle
    (hA : N04PartA D S C K base ε) (m : ℕ)
    (hΩ : physicalPieceOpen S K z m = referencePhysicalPieceOpen S K m)
    {p : PolarPoint} (hp : p.1 ∈ Icc (K.physicalLeft m) (K.physicalRight m)) :
    p ∈ physicalPieceClosed S K z m := by
  rw [n06_physicalPieceClosed_eq_reference_rectangle hA m hΩ]
  exact ⟨hp, mem_univ p.2⟩

end ContinuousFlexibility.Statements
