import ContinuousFlexibility.Analysis.N06PrimitiveJetRescaling
import ContinuousFlexibility.Analysis.N06ActualRelativeJetBounds

/-!
# Identifying the primitive differences with the actual N06 fields

At the reference, the positive cubic quotient is zero by its original
factorization. The left and nu atoms agree with the literal reference
columns. These are identities of the original functions on their actual
open domains, including all current inverse-coordinate factors.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis CanonicalGeometry
open scoped ContDiff

set_option backward.isDefEq.respectTransparency true

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ}

private theorem n06_primitive_unitPoint_mem {m : ℕ}
    (hlen : K.left m < K.right m) {p : PolarPoint} (hp : p ∈ unitStrip) :
    canonicalUnitPoint K m p ∈ canonicalOpen S K m := by
  have hell : 0 < K.right m - K.left m := sub_pos.mpr hlen
  refine ⟨⟨?_, ?_⟩, mem_univ _⟩
  · change K.left m < K.left m + (K.right m - K.left m) * p.1
    exact lt_add_of_pos_right _ (mul_pos hell hp.1.1)
  · change K.left m + (K.right m - K.left m) * p.1 < K.right m
    nlinarith only [mul_pos hell (sub_pos.mpr hp.1.2)]

theorem n06_primitive_reference_divided_zero
    (h01 : N01Properties D T S C base loss ε)
    (h04 : N04Properties D T S C L K base loss ε)
    {m : ℕ} (hm : K.positive m = true) {p : PolarPoint}
    (hp : p ∈ canonicalOpen S K m) :
    (K.dividedDifference (C.referenceState, 0) m).a p = 0 ∧
      (K.dividedDifference (C.referenceState, 0) m).b p = 0 ∧
      (K.dividedDifference (C.referenceState, 0) m).c p = 0 := by
  have h := canonicalDividedDifference_eq_quotient h04.2.1
    (n05_referenceState_mem h01.2.1) (n05_referenceState_sector h01.2.2.1) m hm hp
  simpa only [sub_self, zero_div] using h

/-- The original quotient itself, rather than a new representative, is
the current-minus-reference primitive atom on every positive piece. -/
theorem n06_primitive_divided_unit_identities
    (h01 : N01Properties D T S C base loss ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (z : AnnularState S × ℝ) {m : ℕ} (hm : K.positive m = true) :
    EqOn ((K.dividedDifference z m).a ∘ canonicalUnitPoint K m)
      (fun q => atom D T S C L K z m .dividedA q -
        atom D T S C L K (C.referenceState, 0) m .dividedA q) unitStrip ∧
    EqOn ((K.dividedDifference z m).b ∘ canonicalUnitPoint K m)
      (fun q => atom D T S C L K z m .dividedB q -
        atom D T S C L K (C.referenceState, 0) m .dividedB q) unitStrip ∧
    EqOn ((K.dividedDifference z m).c ∘ canonicalUnitPoint K m)
      (fun q => atom D T S C L K z m .dividedC q -
        atom D T S C L K (C.referenceState, 0) m .dividedC q) unitStrip := by
  have hz (p : PolarPoint) (hp : p ∈ unitStrip) :=
    n06_primitive_reference_divided_zero h01 h04 hm
      (n06_primitive_unitPoint_mem (h04.1.referenceBounds m).2.1 hp)
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    simp only [Function.comp_apply, atom, hm, ↓reduceIte, (hz p hp).1, sub_zero]
  · intro p hp
    simp only [Function.comp_apply, atom, hm, ↓reduceIte, (hz p hp).2.1, sub_zero]
  · intro p hp
    simp only [Function.comp_apply, atom, hm, ↓reduceIte, (hz p hp).2.2, sub_zero]

theorem n06_primitive_potential_unit_identity
    (z : AnnularState S × ℝ) (m : ℕ) :
    EqOn ((fun p => K.potential z m p - K.potential (C.referenceState, 0) m p) ∘
        canonicalUnitPoint K m)
      (fun q => atom D T S C L K z m .potential q -
        atom D T S C L K (C.referenceState, 0) m .potential q) unitStrip :=
  fun _ _ => rfl

private theorem n06_primitive_referenceScalarField_actual
    (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε)
    (i : Fin 3) {p : PolarPoint} (hp : p ∈ annularOpen D) :
    n06ReferenceScalarField D S i p =
      n06CurrentScalarField D S C L (C.referenceState, 0) i p := by
  fin_cases i
  · exact (n06_currentLeftColumn_reference hS h01 h03 p).symm
  · exact n06_referenceScalarField_nu_actual h01.1.1 h01.1.2.2.2.1 h01.2.2.1 hp
  · rfl

/-- The same three current columns used by the existing N06 assembly
are the three primitive source atoms, including coordinate variation. -/
theorem n06_primitive_column_unit_identity
    (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (z : AnnularState S × ℝ) (i : Fin 3) (m : ℕ) :
    EqOn (n06ActualCanonicalColumnDifference D S C L K z i m ∘ canonicalUnitPoint K m)
      (fun q => atom D T S C L K z m (![.leftColumn, .nuColumn, .auxiliaryColumn] i) q -
        atom D T S C L K (C.referenceState, 0) m
          (![.leftColumn, .nuColumn, .auxiliaryColumn] i) q) unitStrip := by
  have hfield (w : AnnularState S × ℝ) (q : PolarPoint) :
      atom D T S C L K w m (![.leftColumn, .nuColumn, .auxiliaryColumn] i) q =
        canonicalSource S K w m (n06CurrentScalarField D S C L w i)
          (canonicalUnitPoint K m q) := by
    fin_cases i <;> rfl
  intro p hp
  have href := n05_referenceState_mem (S := S) (C := C) (base := base) h01.2.1
  have hsref := n05_referenceState_sector h01.2.2.1
  have hcanonical := n06_primitive_unitPoint_mem (h04.1.referenceBounds m).2.1 hp
  have hx := (h04.1.charts (C.referenceState, 0) href hsref m).2.1 hcanonical
  have hxD := (h04.1.domains (C.referenceState, 0) href hsref m).2.2.1 hx
  have he : canonicalSource S K (C.referenceState, 0) m (n06ReferenceScalarField D S i)
        (canonicalUnitPoint K m p) =
      canonicalSource S K (C.referenceState, 0) m
        (n06CurrentScalarField D S C L (C.referenceState, 0) i) (canonicalUnitPoint K m p) := by
    dsimp only [canonicalSource]
    rw [n06_primitive_referenceScalarField_actual hS h01 h03 i hxD]
  rw [hfield z p, hfield (C.referenceState, 0) p]
  change canonicalSource S K z m (n06CurrentScalarField D S C L z i)
      (canonicalUnitPoint K m p) -
    canonicalSource S K (C.referenceState, 0) m (n06ReferenceScalarField D S i)
      (canonicalUnitPoint K m p) = _
  rw [he]

end ContinuousFlexibility.Statements
