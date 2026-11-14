module

public import ContinuousFlexibility.Blueprint.CanonicalParts
public import ContinuousFlexibility.Scalar.HeightDerivatives

/-!
# Exact canonical potential and divided-coefficient identities

Testing the actual transformed operator on the constant function identifies
its potential.  On a positive piece the boundary product is strictly
positive in the interior, so the factorization in `N04PartB` uniquely
determines the divided coefficients there.  Interior factorization alone
does not impose any vanishing jet at the boundary: every numerator admits
the same algebraic division on the open interval.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff

/-- The actual divergence operator kills constants, without any
regularity assumptions on its coefficients. -/
@[simp] theorem divergenceOperator_const (L : SymmetricCoefficients)
    (c : ℝ) (p : PolarPoint) : divergenceOperator L (fun _ => c) p = 0 := by
  simp only [divergenceOperator, radialPartial_const, angularPartial_const,
    mul_zero, zero_add]

/-- The canonical potential is fixed by applying the transformed physical
operator to the height factor. -/
theorem canonicalPotential_eq_source_height
    {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hK : N04PartB S C L K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) (m : ℕ) {p : PolarPoint}
    (hp : p ∈ canonicalOpen S K m) :
    K.potential z m p = (if K.positive m then -1 else (1 : ℝ)) *
      canonicalSource S K z m
        (divergenceOperator (L.coefficients z) (K.height z m)) p := by
  have htest := hK.2.2.1 z hz hsector m (fun _ : PolarPoint => (1 : ℝ))
    contDiff_const p hp
  simpa only [canonicalOperator, mul_one, divergenceOperator_const, mul_zero, zero_add]
    using htest.symm

/-- Taking absolute values removes the fixed sign of the canonical type. -/
theorem abs_canonicalPotential_eq_abs_source_height
    {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hK : N04PartB S C L K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) (m : ℕ) {p : PolarPoint}
    (hp : p ∈ canonicalOpen S K m) :
    |K.potential z m p| =
      |canonicalSource S K z m
        (divergenceOperator (L.coefficients z) (K.height z m)) p| := by
  rw [canonicalPotential_eq_source_height hK hz hsector m hp]
  cases K.positive m <;> simp only [Bool.false_eq_true, ↓reduceIte,
    one_mul, neg_mul, abs_neg]

/-- Both distances to the canonical endpoints are positive on the open
piece; no uniform lower bound on their product is asserted. -/
theorem canonicalBoundaryProduct_pos
    {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ} {p : PolarPoint}
    (hp : p ∈ canonicalOpen S K m) :
    0 < (p.1 - K.left m) * (K.right m - p.1) :=
  mul_pos (sub_pos.mpr hp.1.1) (sub_pos.mpr hp.1.2)

/-- Any numerator can be divided algebraically on the open canonical
piece.  Thus this factorization, by itself, contains no endpoint condition. -/
theorem canonicalCubic_factorization_of_quotient
    {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}
    (f : PolarPoint → ℝ) {p : PolarPoint} (hp : p ∈ canonicalOpen S K m) :
    ((p.1 - K.left m) * (K.right m - p.1)) ^ 3 *
        (f p / ((p.1 - K.left m) * (K.right m - p.1)) ^ 3) = f p := by
  exact mul_div_cancel₀ _ (pow_ne_zero 3 (canonicalBoundaryProduct_pos hp).ne')

private theorem factor_eq_div {d f e : ℝ} (hd : d ≠ 0) (hf : f = d * e) :
    e = f / d := by
  apply (eq_div_iff hd).2
  exact (mul_comm e d).trans hf.symm

/-- On a positive piece, the three divided coefficients have their unique
quotient values.  This statement only concerns points in the open piece. -/
theorem canonicalDividedDifference_eq_quotient
    {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hK : N04PartB S C L K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) (m : ℕ) (hm : K.positive m = true)
    {p : PolarPoint} (hp : p ∈ canonicalOpen S K m) :
    let d := (p.1 - K.left m) * (K.right m - p.1)
    (K.dividedDifference z m).a p =
        ((K.coefficients z m).a p - (K.coefficients (C.referenceState, 0) m).a p) / d ^ 3 ∧
    (K.dividedDifference z m).b p =
        ((K.coefficients z m).b p - (K.coefficients (C.referenceState, 0) m).b p) / d ^ 3 ∧
    (K.dividedDifference z m).c p =
        ((K.coefficients z m).c p - (K.coefficients (C.referenceState, 0) m).c p) / d ^ 3 := by
  have hf := hK.2.2.2.2 z hz hsector m hm p hp
  have hd := pow_ne_zero 3 (canonicalBoundaryProduct_pos hp).ne'
  exact ⟨factor_eq_div hd hf.1, factor_eq_div hd hf.2.1, factor_eq_div hd hf.2.2⟩

/-- Division by the boundary cube preserves smoothness in the open piece.
This is only an interior statement; it provides neither boundary values
nor uniform bounds as the boundary is approached. -/
theorem contDiffOn_canonicalCubicQuotient
    {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}
    {f g : PolarPoint → ℝ}
    (hf : ContDiffOn ℝ ∞ f (canonicalOpen S K m))
    (hg : ContDiffOn ℝ ∞ g (canonicalOpen S K m)) :
    ContDiffOn ℝ ∞ (fun p : PolarPoint =>
      (f p - g p) / ((p.1 - K.left m) * (K.right m - p.1)) ^ 3)
      (canonicalOpen S K m) := by
  have hd : ContDiff ℝ ∞ (fun p : PolarPoint =>
      ((p.1 - K.left m) * (K.right m - p.1)) ^ 3) :=
    ((contDiff_fst.sub contDiff_const).mul (contDiff_const.sub contDiff_fst)).pow 3
  exact (hf.sub hg).div hd.contDiffOn
    (fun p hp => pow_ne_zero 3 (canonicalBoundaryProduct_pos hp).ne')

/-- Smooth current and reference coefficients give smooth divided
coefficients in the interior, through their forced quotient formulas. -/
theorem contDiffOn_canonicalDividedDifference
    {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hK : N04PartB S C L K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) (m : ℕ) (hm : K.positive m = true)
    (ha : ContDiffOn ℝ ∞ (K.coefficients z m).a (canonicalOpen S K m))
    (hb : ContDiffOn ℝ ∞ (K.coefficients z m).b (canonicalOpen S K m))
    (hc : ContDiffOn ℝ ∞ (K.coefficients z m).c (canonicalOpen S K m))
    (ha0 : ContDiffOn ℝ ∞ (K.coefficients (C.referenceState, 0) m).a
      (canonicalOpen S K m))
    (hb0 : ContDiffOn ℝ ∞ (K.coefficients (C.referenceState, 0) m).b
      (canonicalOpen S K m))
    (hc0 : ContDiffOn ℝ ∞ (K.coefficients (C.referenceState, 0) m).c
      (canonicalOpen S K m)) :
    ContDiffOn ℝ ∞ (K.dividedDifference z m).a (canonicalOpen S K m) ∧
    ContDiffOn ℝ ∞ (K.dividedDifference z m).b (canonicalOpen S K m) ∧
    ContDiffOn ℝ ∞ (K.dividedDifference z m).c (canonicalOpen S K m) := by
  have hq (p : PolarPoint) (hp : p ∈ canonicalOpen S K m) :=
    canonicalDividedDifference_eq_quotient hK hz hsector m hm hp
  exact ⟨(contDiffOn_canonicalCubicQuotient ha ha0).congr (fun p hp => (hq p hp).1),
    (contDiffOn_canonicalCubicQuotient hb hb0).congr (fun p hp => (hq p hp).2.1),
    (contDiffOn_canonicalCubicQuotient hc hc0).congr (fun p hp => (hq p hp).2.2)⟩

end ContinuousFlexibility.Analysis
