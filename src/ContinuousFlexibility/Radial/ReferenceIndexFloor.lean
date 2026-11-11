import ContinuousFlexibility.Radial.ReferenceFiniteIndexFloor

/-!
# Positive radial indices

The positive-index normalization is the value N=1 of the general
finite index floor. All quantitative preservation is proved there.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open ContinuousFlexibility.Statements

def positiveIndexReference (D : ReferenceData) : ReferenceData :=
  floorReferenceIndex D 1

@[simp] theorem positiveIndexReference_index (D : ReferenceData) (m : ℕ) :
    (positiveIndexReference D).cellIndex m = max (D.cellIndex m) 1 := rfl

theorem positiveIndexReference_index_pos (D : ReferenceData) (m : ℕ) :
    1 ≤ (positiveIndexReference D).cellIndex m :=
  Nat.le_max_right _ _

theorem isAccumulatingProfile_positiveIndexReference {D : ReferenceData}
    (hD : IsAccumulatingProfile D) :
    IsAccumulatingProfile (positiveIndexReference D) :=
  isAccumulatingProfile_floorReferenceIndex hD 1 (by decide)

end ContinuousFlexibility.Radial
