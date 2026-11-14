module

public import ContinuousFlexibility.Statements.Radial

/-! The zero endpoint scalar leaves the actual physical output field unchanged. -/

@[expose] public section

namespace ContinuousFlexibility.Radial

open ContinuousFlexibility.Statements

@[simp] theorem n05_outputRemainder_zero (D : ReferenceData) (U : RadialUnknown) :
    outputRemainder D 0 U = U.1 := by
  funext p
  simp only [outputRemainder, zero_mul, sub_zero]

end ContinuousFlexibility.Radial
