module

public import ContinuousFlexibility.Analysis.N06CurrentRelativeSourceIdentity

/-!
# The actual negative source with a zero principal contribution

The original-atlas construction makes its principal source zero on negative
pieces. This gives the literal remainder identity without imposing a
unit-interval cubic-test characterization.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

theorem n06_currentRelativeSource_negative_remainder_ae_of_eq_zero
    {D : ReferenceData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
    {z : AnnularState S × ℝ}
    (u : CanonicalUnknown S K) (F G Fcur : CanonicalSequence S K)
    (m : ℕ) (hm : K.positive m = false)
    (hsource : (Fcur m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      n06CurrentRelativeSourceField D S C L K z u F G m)
    (hG : G m = 0) :
    n06CurrentRemainderSource D S C L K z u Fcur m =ᵐ[canonicalMeasure S K m]
      fun p => n06NegativePrincipalForcing D S C K u F m p + K.potential z m p * u.1 m p := by
  have hGae : (G m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m] fun _ => 0 := by
    rw [hG]
    exact Lp.coeFn_zero ℝ 2 (canonicalMeasure S K m)
  filter_upwards [n06_currentRelativeSource_remainder_ae u F G Fcur m hsource, hGae]
    with p hp hzero
  rw [n06_negativePrincipalForcing_eq_reference]
  simp only [hm, Bool.false_eq_true, ↓reduceIte, one_mul, hzero, add_zero] at hp
  rw [hp]
  ring

end ContinuousFlexibility.Statements
