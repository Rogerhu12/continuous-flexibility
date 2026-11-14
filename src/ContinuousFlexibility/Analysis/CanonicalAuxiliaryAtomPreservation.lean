import ContinuousFlexibility.Analysis.PhysicalSpacesAuxiliaryColumn
import ContinuousFlexibility.Analysis.MaterialEnvelopeNormalization

/-!
# Actual atoms retained by the auxiliary-column replacement

The replacement changes only the displayed compatibility column.  The
optional material enlargement changes only E0.  Every other atom remains
the exact same function, including its actual inverse point and source
denominator.  The two E0 ratios are explicitly excluded from that second
identity; no estimate for those changed ratios is inferred here.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements
open CanonicalGeometry

theorem canonicalReferenceRadial_replaceAuxiliaryColumn
    {S : PhysicalSpacesData} {C : NonlinearGeometryData S} {K : CanonicalData S}
    (hR : ReferenceRadial S C K) (η : (S.height (3 / 4 : ℝ)).Space) :
    ReferenceRadial (physicalSpacesReplaceAuxiliaryColumn S η)
      (geometryReplaceAuxiliaryColumn C η) (canonicalReplaceAuxiliaryColumn K η) :=
  hR

/-- This is equality of the complete actual scalar functions, rather
than equality of selected values or a new representative. -/
theorem canonicalAtom_replaceAuxiliaryColumn_of_ne
    (D : ReferenceData) (T : MaterialData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (L : ReturnCorrectionData S) (K : CanonicalData S)
    (η : (S.height (3 / 4 : ℝ)).Space) (z : AnnularState S × ℝ)
    (m : ℕ) (a : Atom) (ha : a ≠ .auxiliaryColumn) :
    atom D T (physicalSpacesReplaceAuxiliaryColumn S η)
      (geometryReplaceAuxiliaryColumn C η) (correctionReplaceAuxiliaryColumn L η)
      (canonicalReplaceAuxiliaryColumn K η) z m a = atom D T S C L K z m a := by
  cases a <;> try rfl
  exact (ha rfl).elim

theorem canonicalAtom_enlargedMaterialData_of_ne_ratios
    (D : ReferenceData) (T : MaterialData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (L : ReturnCorrectionData S) (K : CanonicalData S)
    (z : AnnularState S × ℝ) (m : ℕ) (a : Atom)
    (hE : a ≠ .ratioE0) (hEi : a ≠ .ratioE0Inverse) :
    atom D (enlargedMaterialData T) S C L K z m a = atom D T S C L K z m a := by
  cases a <;> try rfl
  · exact (hE rfl).elim
  · exact (hEi rfl).elim

/-- The combined operation preserves all atoms except the new column
and the two explicitly changed E0 ratios. -/
theorem canonicalAtom_auxiliaryReplacement_enlarged_of_ne
    (D : ReferenceData) (T : MaterialData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (L : ReturnCorrectionData S) (K : CanonicalData S)
    (η : (S.height (3 / 4 : ℝ)).Space) (z : AnnularState S × ℝ)
    (m : ℕ) (a : Atom) (ha : a ≠ .auxiliaryColumn)
    (hE : a ≠ .ratioE0) (hEi : a ≠ .ratioE0Inverse) :
    atom D (enlargedMaterialData T) (physicalSpacesReplaceAuxiliaryColumn S η)
      (geometryReplaceAuxiliaryColumn C η) (correctionReplaceAuxiliaryColumn L η)
      (canonicalReplaceAuxiliaryColumn K η) z m a = atom D T S C L K z m a := by
  exact (canonicalAtom_enlargedMaterialData_of_ne_ratios D T
    (physicalSpacesReplaceAuxiliaryColumn S η) (geometryReplaceAuxiliaryColumn C η)
    (correctionReplaceAuxiliaryColumn L η) (canonicalReplaceAuxiliaryColumn K η)
    z m a hE hEi).trans
      (canonicalAtom_replaceAuxiliaryColumn_of_ne D T S C L K η z m a ha)

end ContinuousFlexibility.Analysis
