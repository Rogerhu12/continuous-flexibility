module

public import ContinuousFlexibility.Analysis.N07bSourceBound
public import ContinuousFlexibility.Analysis.N07bNeighborhood

/-!
# Absorbing a fixed polynomial state factor in the source geometry

At the one Banach angular order, a finite geometric jet calculation may
produce an arbitrary fixed polynomial of a fixed state seminorm. Both
its order and degree are selected before the state and the source. Raising
the low order and shrinking the radius bounds that polynomial uniformly.
The charts and all previously chosen spaces and inverses are unchanged.

This is a conditional geometric reduction. No coefficient estimate is
asserted to follow from the qualitative frozen chart conditions.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false

/-- A finite-order geometric estimate may use any fixed state order and
any fixed polynomial degree. None of the witnesses depends on the state,
piece, coefficient path, physical point, or source. -/
def N07bSourcePolynomialCoefficientBound (T : MaterialData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (K : CanonicalData S)
    (base : ℕ) (ε : ℝ) (b : ℕ) : Prop :=
  ∃ r d : ℕ, ∃ B A : ℝ, 0 ≤ B ∧ 0 ≤ A ∧
    ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      ∀ m x, x ∈ physicalPieceOpen S K z m →
        ∀ j : Fin (b + 1), ∀ i : n07bAngularChainIndex j.val,
          n07bSourceGeometricWeight T K z m x *
            n07bAngularChainCoefficient T K z m (3 / 4 : ℝ) j.val i x ^ 2 ≤
              B * T.E0 x.1 ^ A *
                (1 + stateGrading S r (z.1 - C.referenceState) + |z.2|) ^ d

/-- Every fixed natural power of a controlled state weight is bounded
uniformly on the same smaller neighborhood. -/
theorem n07b_stateWeight_pow_le_two_pow
    {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {r base d : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}
    (hr : r ≤ base) (hε : ε ≤ (1 / 2 : ℝ))
    (hz : z ∈ stateNeighborhood S C base ε) :
    (1 + stateGrading S r (z.1 - C.referenceState) + |z.2|) ^ d ≤ (2 : ℝ) ^ d :=
  pow_le_pow_left₀
    (add_nonneg (add_nonneg zero_le_one (apply_nonneg _ _)) (abs_nonneg _))
    (n07b_stateWeight_le_two hr hε hz) d

/-- A fixed polynomial coefficient estimate becomes the source geometry
condition on a higher-order, smaller neighborhood. The resulting state
loss is zero: all polynomial growth was absorbed into the low neighborhood. -/
theorem n07b_sourceCoefficientBound_of_polynomial_on_smaller
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {K : CanonicalData S}
    {base base' b r d : ℕ} {ε ε' B A : ℝ}
    (hT : IsMaterialData D T) (hK : N04PartA D S C K base ε)
    (hb : base ≤ base') (hr : r ≤ base') (hε : ε' ≤ ε)
    (hεsmall : ε' ≤ (1 / 2 : ℝ)) (hB : 0 ≤ B) (hA : 0 ≤ A)
    (hcoeff : ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      ∀ m x, x ∈ physicalPieceOpen S K z m →
        ∀ j : Fin (b + 1), ∀ i : n07bAngularChainIndex j.val,
          n07bSourceGeometricWeight T K z m x *
            n07bAngularChainCoefficient T K z m (3 / 4 : ℝ) j.val i x ^ 2 ≤
              B * T.E0 x.1 ^ A *
                (1 + stateGrading S r (z.1 - C.referenceState) + |z.2|) ^ d) :
    N07bSourceCoefficientBound T S C K base' ε' b 0 := by
  have hB' : 0 ≤ B * (2 : ℝ) ^ d := mul_nonneg hB (pow_nonneg (by norm_num) _)
  refine ⟨B * (2 : ℝ) ^ d, A, hB', hA, ?_⟩
  intro z hz hs m x hx j i
  have hzold := n06_stateNeighborhood_mono (C := C) hb hε hz
  have hxcore : x.1 ∈ Ioo D.a D.b := ((hK.domains z hzold hs m).2.2.1 hx).1
  have hE : 0 ≤ T.E0 x.1 ^ A :=
    Real.rpow_nonneg (hT.2.1 x.1 hxcore).2.2.1.le _
  have hpow := n07b_stateWeight_pow_le_two_pow (d := d) hr hεsmall hz
  have hQ : 1 ≤ 1 + stateGrading S b (z.1 - C.referenceState) + |z.2| := by
    linarith [apply_nonneg (stateGrading S b) (z.1 - C.referenceState), abs_nonneg z.2]
  have hQsq : 1 ≤ (1 + stateGrading S b (z.1 - C.referenceState) + |z.2|) ^ 2 := by
    nlinarith
  calc
    _ ≤ B * T.E0 x.1 ^ A *
        (1 + stateGrading S r (z.1 - C.referenceState) + |z.2|) ^ d :=
      hcoeff z hzold hs m x hx j i
    _ ≤ B * T.E0 x.1 ^ A * (2 : ℝ) ^ d :=
      mul_le_mul_of_nonneg_left hpow (mul_nonneg hB hE)
    _ = (B * (2 : ℝ) ^ d * T.E0 x.1 ^ A) * 1 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hQsq (mul_nonneg hB' hE)

/-- For a fixed Banach order, the state order and polynomial degree in a
geometric estimate can be absorbed without changing any geometric data.
The positive radius and the new low order are chosen before every state. -/
theorem n07b_exists_sourceCoefficientBound_of_polynomial
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {K : CanonicalData S}
    {base b : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hK : N04PartA D S C K base ε) (hε : 0 < ε)
    (hpoly : N07bSourcePolynomialCoefficientBound T S C K base ε b) :
    ∃ base' : ℕ, ∃ ε' : ℝ, base ≤ base' ∧ 0 < ε' ∧ ε' ≤ ε ∧ ε' ≤ (1 / 2 : ℝ) ∧
      N07bSourceCoefficientBound T S C K base' ε' b 0 := by
  obtain ⟨r, d, B, A, hB, hA, hcoeff⟩ := hpoly
  refine ⟨max base r, min ε (1 / 2), le_max_left _ _,
    lt_min hε (by norm_num), min_le_left _ _, min_le_right _ _, ?_⟩
  exact n07b_sourceCoefficientBound_of_polynomial_on_smaller hT hK
    (le_max_left _ _) (le_max_right _ _) (min_le_left _ _) (min_le_right _ _) hB hA hcoeff

end ContinuousFlexibility.Analysis
