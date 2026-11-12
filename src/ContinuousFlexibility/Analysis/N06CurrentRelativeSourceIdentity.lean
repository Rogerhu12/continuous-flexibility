import ContinuousFlexibility.Analysis.N06CurrentScalarPairing
import ContinuousFlexibility.Analysis.N06FiniteReferenceColumns
import ContinuousFlexibility.Analysis.N06ReferenceCanonicalEquation
import ContinuousFlexibility.Analysis.N06NegativeReferenceForcingLp
import ContinuousFlexibility.Analysis.N06PositiveCubicPairing
import ContinuousFlexibility.Analysis.N06CanonicalTestSeparation

/-!
# The actual relative source and the two canonical Green signs

The relative source contains the cubic source, the signed actual
potential difference, and all three actual current-minus-reference
columns. Subtracting the current columns gives precisely the remainder
used in the positive and negative Green formulas.

The negative cubic contribution is proved to vanish from its defining
canonical test pairing and separation in the original L2 space. It is
not a further support assumption on the constructed source.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {z : AnnularState S × ℝ}

/-- The literal field of identity plus the cubic, potential, and three
scalar-column contributions on the original source space. -/
def n06CurrentRelativeSourceField (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (L : ReturnCorrectionData S) (K : CanonicalData S)
    (z : AnnularState S × ℝ) (u : CanonicalUnknown S K)
    (F G : CanonicalSequence S K) (m : ℕ) (p : PolarPoint) : ℝ :=
  F m p + G m p +
    (if K.positive m then (-1 : ℝ) else 1) *
      (K.potential z m p - K.potential (C.referenceState, 0) m p) * u.1 m p +
    u.2.1 * (canonicalSource S K z m (n06CurrentScalarField D S C L z 0) p -
      canonicalSource S K (C.referenceState, 0) m (n06ReferenceScalarField D S 0) p) +
    u.2.2.1 * (canonicalSource S K z m (n06CurrentScalarField D S C L z 1) p -
      canonicalSource S K (C.referenceState, 0) m (n06ReferenceScalarField D S 1) p) +
    u.2.2.2 * (canonicalSource S K z m (n06CurrentScalarField D S C L z 2) p -
      canonicalSource S K (C.referenceState, 0) m (n06ReferenceScalarField D S 2) p)

/-- The same three original reference columns occur in the two signs;
the negative principal forcing also removes the reference potential. -/
theorem n06_negativePrincipalForcing_eq_reference
    (u : CanonicalUnknown S K) (F : CanonicalSequence S K) (m : ℕ) (p : PolarPoint) :
    n06NegativePrincipalForcing D S C K u F m p =
      -n06ReferenceCanonicalForcing D S C K u F m p -
        K.potential (C.referenceState, 0) m p * u.1 m p := by
  simp only [n06NegativePrincipalForcing, n06NegativeReferenceForcing,
    n06ReferenceCanonicalForcing]
  ring

/-- A field identification for the actually constructed source yields
the common signed remainder identity; no weak equation is an input. -/
theorem n06_currentRelativeSource_remainder_ae
    (u : CanonicalUnknown S K) (F G Fcur : CanonicalSequence S K) (m : ℕ)
    (hsource : (Fcur m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      n06CurrentRelativeSourceField D S C L K z u F G m) :
    n06CurrentRemainderSource D S C L K z u Fcur m =ᵐ[canonicalMeasure S K m]
      fun p => -n06ReferenceCanonicalForcing D S C K u F m p + G m p +
        (if K.positive m then (-1 : ℝ) else 1) *
          (K.potential z m p - K.potential (C.referenceState, 0) m p) * u.1 m p := by
  filter_upwards [hsource] with p hp
  have href : n06ReferenceCanonicalForcing D S C K u F m p =
      -F m p +
        u.2.1 * canonicalSource S K (C.referenceState, 0) m (n06ReferenceScalarField D S 0) p +
        u.2.2.1 * canonicalSource S K (C.referenceState, 0) m (n06ReferenceScalarField D S 1) p +
        u.2.2.2 * canonicalSource S K (C.referenceState, 0) m (n06ReferenceScalarField D S 2) p :=
    rfl
  simp only [n06CurrentRemainderSource, hp, n06CurrentRelativeSourceField, href]
  ring

/-- The positive Green source has exactly the physical divergence sign:
minus reference forcing, plus cubic source, minus potential difference. -/
theorem n06_currentRelativeSource_positive_remainder_ae
    (u : CanonicalUnknown S K) (F G Fcur : CanonicalSequence S K)
    (m : ℕ) (hm : K.positive m = true)
    (hsource : (Fcur m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      n06CurrentRelativeSourceField D S C L K z u F G m) :
    n06CurrentRemainderSource D S C L K z u Fcur m =ᵐ[canonicalMeasure S K m]
      fun p => -n06ReferenceCanonicalForcing D S C K u F m p + G m p -
        (K.potential z m p - K.potential (C.referenceState, 0) m p) * u.1 m p := by
  filter_upwards [n06_currentRelativeSource_remainder_ae u F G Fcur m hsource] with p hp
  simpa only [hm, ↓reduceIte, neg_mul, one_mul, sub_eq_add_neg] using hp

/-- A source characterized by the actual positive cubic test operator
is the zero L2 element on every negative piece. -/
theorem n06_positiveCubicSource_eq_zero_on_negative
    {A B Cc : ℕ → PolarPoint → ℝ} {m : ℕ}
    (hm : K.positive m = false) (U : PolarPoint → ℝ) (g : CanonicalL2 S K m)
    (hweak : ∀ φ, CanonicalTest S K m φ →
      (∫ p, g p * φ p ∂canonicalMeasure S K m) =
        ∫ p, U p * n06PositiveCubicTestOperator K A B Cc m φ p
          ∂canonicalMeasure S K m) :
    g = 0 := by
  apply n06_canonicalL2_test_ext
  intro φ hφ
  have hleft : (∫ p, g p * φ p ∂canonicalMeasure S K m) = (0 : ℝ) := by
    simpa only [n06PositiveCubicTestOperator, hm, Bool.false_eq_true, ↓reduceIte,
      mul_zero, integral_zero] using hweak φ hφ
  have hright : (∫ p, (0 : CanonicalL2 S K m) p * φ p
      ∂canonicalMeasure S K m) = (0 : ℝ) := by
    apply integral_eq_zero_of_ae
    filter_upwards [Lp.coeFn_zero ℝ 2 (canonicalMeasure S K m)] with p hp
    change (0 : CanonicalL2 S K m) p = 0 at hp
    rw [hp, zero_mul]
    rfl
  exact hleft.trans hright.symm

/-- On a negative piece, the original test characterization removes the
cubic source and leaves the actual principal forcing plus current V U. -/
theorem n06_currentRelativeSource_negative_remainder_ae
    (u : CanonicalUnknown S K) (F G Fcur : CanonicalSequence S K)
    (m : ℕ) (hm : K.positive m = false)
    (hsource : (Fcur m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      n06CurrentRelativeSourceField D S C L K z u F G m)
    {A B Cc : ℕ → PolarPoint → ℝ}
    (hweak : ∀ φ, CanonicalTest S K m φ →
      (∫ p, G m p * φ p ∂canonicalMeasure S K m) =
        ∫ p, u.1 m p * n06PositiveCubicTestOperator K A B Cc m φ p
          ∂canonicalMeasure S K m) :
    n06CurrentRemainderSource D S C L K z u Fcur m =ᵐ[canonicalMeasure S K m]
      fun p => n06NegativePrincipalForcing D S C K u F m p + K.potential z m p * u.1 m p := by
  have hG : G m = 0 := n06_positiveCubicSource_eq_zero_on_negative hm (u.1 m) (G m) hweak
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
