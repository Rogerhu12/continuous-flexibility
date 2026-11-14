module

public import ContinuousFlexibility.Analysis.CanonicalCoefficientIdentities
public import ContinuousFlexibility.Analysis.CanonicalTwoEndpointCubicMixed

/-!
# Actual canonical field jets from explicit source and numerator data

The potential identity determines every interior mixed jet through the
explicit source-height expression.  A single component selector handles
all three positive divided coefficients.  Their estimate uses actual
endpoint zero jets and a numerical bound for the numerator with six more
radial derivatives.  No quantitative canonical-bound predicate is assumed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

private theorem mixedDerivative_mul_constant (c : ℝ) (F : PolarPoint → ℝ)
    (a b : ℕ) (p : PolarPoint) :
    mixedDerivative a b (fun q => c * F q) p = c * mixedDerivative a b F p := by
  simp only [mixedDerivative, iteratedDeriv_const_mul_field]

/-- The actual potential jets are the jets of the explicit transformed
height source, with only the fixed sign of the canonical type. -/
theorem mixedDerivative_canonicalPotential_eq_source_height
    {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hK : N04PartB S C L K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) (m a b : ℕ) {p : PolarPoint}
    (hp : p ∈ canonicalOpen S K m) :
    mixedDerivative a b (K.potential z m) p =
      (if K.positive m then -1 else (1 : ℝ)) *
        mixedDerivative a b
          (canonicalSource S K z m
            (divergenceOperator (L.coefficients z) (K.height z m))) p := by
  calc
    mixedDerivative a b (K.potential z m) p =
        mixedDerivative a b (fun q =>
          (if K.positive m then -1 else (1 : ℝ)) *
            canonicalSource S K z m
              (divergenceOperator (L.coefficients z) (K.height z m)) q) p :=
      mixedDerivative_eq_of_eqOn_radialCylinder
        (fun r hr θ => canonicalPotential_eq_source_height hK hz hsector m
          (p := (r, θ)) ⟨hr, mem_univ θ⟩) a b hp.1
    _ = _ := mixedDerivative_mul_constant _ _ a b p

/-- The sign contributes no loss at any mixed order. -/
theorem abs_mixedDerivative_canonicalPotential_eq_abs_source_height
    {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hK : N04PartB S C L K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) (m a b : ℕ) {p : PolarPoint}
    (hp : p ∈ canonicalOpen S K m) :
    |mixedDerivative a b (K.potential z m) p| =
      |mixedDerivative a b
        (canonicalSource S K z m
          (divergenceOperator (L.coefficients z) (K.height z m))) p| := by
  rw [mixedDerivative_canonicalPotential_eq_source_height hK hz hsector m a b hp]
  cases K.positive m <;> simp only [Bool.false_eq_true, ↓reduceIte,
    one_mul, neg_mul, abs_neg]

/-- One selector for the three symmetric coefficient fields. -/
def canonicalCoefficientComponent (i : Fin 3) (A : SymmetricCoefficients) :
    PolarPoint → ℝ :=
  if i = 0 then A.a else if i = 1 then A.b else A.c

/-- The actual coefficient difference that occurs in positive-piece
cubic division, before dividing by the boundary product. -/
def canonicalCoefficientNumerator (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (K : CanonicalData S)
    (z : AnnularState S × ℝ) (m : ℕ) (i : Fin 3) (p : PolarPoint) : ℝ :=
  canonicalCoefficientComponent i (K.coefficients z m) p -
    canonicalCoefficientComponent i (K.coefficients (C.referenceState, 0) m) p

/-- The three factorization clauses in PartB have one component interface. -/
theorem canonicalCoefficientNumerator_factorization
    {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hK : N04PartB S C L K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) (m : ℕ) (hm : K.positive m = true)
    (i : Fin 3) {p : PolarPoint} (hp : p ∈ canonicalOpen S K m) :
    canonicalCoefficientNumerator S C K z m i p =
      ((p.1 - K.left m) * (K.right m - p.1)) ^ 3 *
        canonicalCoefficientComponent i (K.dividedDifference z m) p := by
  have h := hK.2.2.2.2 z hz hsector m hm p hp
  unfold canonicalCoefficientNumerator canonicalCoefficientComponent
  split_ifs
  · exact h.1
  · exact h.2.1
  · exact h.2.2

/-- A smooth extension of the actual numerator gives a bound for the
actual divided field.  The endpoint jets and the numerical higher-jet
bound are explicit inputs; interior factorization does not supply them. -/
theorem abs_mixedDerivative_canonicalDividedComponent_le_of_extension
    {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hK : N04PartB S C L K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) (m : ℕ) (hm : K.positive m = true) (i : Fin 3)
    {F : PolarPoint → ℝ} (hF : ContDiff ℝ ∞ F)
    (hnum : ∀ q ∈ canonicalOpen S K m, F q = canonicalCoefficientNumerator S C K z m i q)
    (hleft : ∀ θ : ℝ, ∀ j : ℕ, j ≤ 2 →
      iteratedDeriv j (fun r : ℝ => F (r, θ)) (K.left m) = 0)
    (hright : ∀ θ : ℝ, ∀ j : ℕ, j ≤ 2 →
      iteratedDeriv j (fun r : ℝ => F (r, θ)) (K.right m) = 0)
    (a b : ℕ) {M : ℝ} {p : PolarPoint}
    (hbound : ∀ r ∈ Icc (K.left m) (K.right m),
      |mixedDerivative (a + 6) b F (r, p.2)| ≤ M)
    (hp : p ∈ canonicalOpen S K m) :
    |mixedDerivative a b (canonicalCoefficientComponent i (K.dividedDifference z m)) p| ≤
      M / 36 := by
  have hfactor (q : PolarPoint) (hq : q.1 ∈ Ioo (K.left m) (K.right m)) :
      F q = ((q.1 - K.left m) * (K.right m - q.1)) ^ 3 *
        canonicalCoefficientComponent i (K.dividedDifference z m) q :=
    (hnum q ⟨hq, mem_univ q.2⟩).trans
      (canonicalCoefficientNumerator_factorization hK hz hsector m hm i
        ⟨hq, mem_univ q.2⟩)
  exact abs_mixedDerivative_of_twoEndpointCubicFactorization hF
    (hp.1.1.trans hp.1.2) hleft hright hfactor a b hbound hp.1

/-- In particular, a globally smooth actual numerator with the stated
three zero jets at both endpoints gives the fixed-loss-six estimate. -/
theorem abs_mixedDerivative_canonicalDividedComponent_le
    {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hK : N04PartB S C L K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) (m : ℕ) (hm : K.positive m = true) (i : Fin 3)
    (hF : ContDiff ℝ ∞ (canonicalCoefficientNumerator S C K z m i))
    (hleft : ∀ θ : ℝ, ∀ j : ℕ, j ≤ 2 →
      iteratedDeriv j (fun r : ℝ => canonicalCoefficientNumerator S C K z m i (r, θ))
        (K.left m) = 0)
    (hright : ∀ θ : ℝ, ∀ j : ℕ, j ≤ 2 →
      iteratedDeriv j (fun r : ℝ => canonicalCoefficientNumerator S C K z m i (r, θ))
        (K.right m) = 0)
    (a b : ℕ) {M : ℝ} {p : PolarPoint}
    (hbound : ∀ r ∈ Icc (K.left m) (K.right m),
      |mixedDerivative (a + 6) b (canonicalCoefficientNumerator S C K z m i) (r, p.2)| ≤ M)
    (hp : p ∈ canonicalOpen S K m) :
    |mixedDerivative a b (canonicalCoefficientComponent i (K.dividedDifference z m)) p| ≤
      M / 36 :=
  abs_mixedDerivative_canonicalDividedComponent_le_of_extension hK hz hsector m hm i hF
    (fun _ _ => rfl) hleft hright a b hbound hp

end ContinuousFlexibility.Analysis
