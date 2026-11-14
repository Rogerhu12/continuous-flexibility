module

public import ContinuousFlexibility.Analysis.N05PrimitiveReferenceValues
public import ContinuousFlexibility.Analysis.N05ReferenceFiberPacking
public import Mathlib.Data.Set.Card
public import Mathlib.MeasureTheory.Measure.Real

/-!
# Finite fibers from the actual primitive physical lengths

Disjoint actual reference intervals with a uniform positive width pack
finitely in the radial core. The primitive inverse-length estimate gives
that width at each prescribed label; no relabelling or bounded-multiplicity
hypothesis is needed. The primitive premise remains explicit here;
producing it from a full nonlinear construction is a separate obligation
of the shared interface.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory
open scoped BigOperators

/-- Explicit primitive jets yield the finite-fiber condition on the same
canonical data, using actual interval packing and the prescribed
inverse-length bound. -/
theorem n05_reference_primitive_piece_fibers
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S}
    {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (h04 : N04Properties D T S C L K base loss ε)
    (hJ : CanonicalGeometry.ReferenceJets D T S C L K) :
    ∃ P : ℝ, 0 < P ∧ ∀ n : ℕ,
      {m | D.cellIndex (K.cell m) = n}.Finite ∧
        ({m | D.cellIndex (K.cell m) = n}.ncard : ℝ) ≤ P * radialE n ^ P := by
  obtain ⟨B, hB, _, hwidth⟩ := n05_reference_primitive_height_ratios_and_width h04 hJ
  obtain ⟨C0, A, hC0, hA, hsample⟩ := n05_material_sample_E0_power_bound hD hT hB.le
  apply n05_referencePieceIndex_count_of_inverse_width h04 (mul_pos hB hC0) hA
  intro m
  exact (hwidth m).trans (by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hsample (K.cell m)) hB.le)

end ContinuousFlexibility.Statements
