import ContinuousFlexibility.Analysis.N07aUnitCoefficientRows
import ContinuousFlexibility.Analysis.N07aCurrentPrincipalBounds
import ContinuousFlexibility.Analysis.N07aReferenceReturn
import ContinuousFlexibility.Analysis.N07aCylinderWeightedNorms

/-!
# The actual cubic factors in unit coordinates

At the reference state the divided difference vanishes on every positive
piece. Thus the current-minus-reference atom is the original divided
coefficient, and the exact principal difference is ℓ⁶ x³(1-x)³ times that
same atom. This retains the factor used by the weak energy estimate.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ}

def n07aCubicPrincipalAtom (i : Fin 3) : Atom := ![.principalA, .principalB, .principalC] i

def n07aCubicDividedAtom (i : Fin 3) : Atom := ![.dividedA, .dividedB, .dividedC] i

def n07aCubicPrincipalField (K : CanonicalData S) (z : AnnularState S × ℝ)
    (m : ℕ) (i : Fin 3) : PolarPoint → ℝ :=
  ![(K.coefficients z m).a, (K.coefficients z m).b, (K.coefficients z m).c] i

def n07aCubicDividedField (K : CanonicalData S) (z : AnnularState S × ℝ)
    (m : ℕ) (i : Fin 3) : PolarPoint → ℝ :=
  ![(K.dividedDifference z m).a, (K.dividedDifference z m).b, (K.dividedDifference z m).c] i

theorem n07a_actual_cubic_difference
    (h04 : N04Properties D T S C L K base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) {m : ℕ} (hm : K.positive m = true)
    {p : PolarPoint} (hp : p ∈ canonicalOpen S K m) (i : Fin 3) :
    n07aCubicPrincipalField K z m i p - n07aCubicPrincipalField K (C.referenceState, 0) m i p =
      ((p.1 - K.left m) * (K.right m - p.1)) ^ 3 * n07aCubicDividedField K z m i p := by
  have h := h04.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 z hz hs m hm p hp
  fin_cases i
  · exact h.1
  · exact h.2.1
  · exact h.2.2

theorem n07a_reference_divided_zero
    (h01 : N01Properties D T S C base loss ε)
    (h04 : N04Properties D T S C L K base loss ε)
    {m : ℕ} (hm : K.positive m = true) {p : PolarPoint}
    (hp : p ∈ canonicalOpen S K m) (i : Fin 3) :
    n07aCubicDividedField K (C.referenceState, 0) m i p = 0 := by
  have h := n07a_actual_cubic_difference h04 (n07a_reference_mem_stateNeighborhood h01)
    h01.2.2.1.stateSector hm hp i
  rw [sub_self] at h
  have hd : ((p.1 - K.left m) * (K.right m - p.1)) ^ 3 ≠ 0 :=
    (pow_pos (mul_pos (sub_pos.mpr hp.1.1) (sub_pos.mpr hp.1.2)) 3).ne'
  exact (mul_eq_zero.mp h.symm).resolve_left hd

theorem n07aUnitDifferenceAtom_divided
    (h01 : N01Properties D T S C base loss ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (z : Parameter S) {m : ℕ} (hm : K.positive m = true)
    (hlen : K.left m < K.right m) {p : PolarPoint} (hp : p ∈ unitStrip) (i : Fin 3) :
    n07aUnitDifferenceAtom D T S C L K z m (n07aCubicDividedAtom i) p =
      n07aCubicDividedField K (liftSectorParameter S C z) m i (canonicalUnitPoint K m p) := by
  have hz := n07a_reference_divided_zero h01 h04 hm (n07aCanonicalUnitPoint_maps m hlen hp) i
  have hfield (z' : AnnularState S × ℝ) : atom D T S C L K z' m (n07aCubicDividedAtom i) p =
      if K.positive m then n07aCubicDividedField K z' m i (canonicalUnitPoint K m p) else 0 := by
    fin_cases i <;> rfl
  rw [n07aUnitDifferenceAtom, hfield, hfield, hm]
  simp only [↓reduceIte, hz, sub_zero]

theorem n07aUnitDifferenceAtom_cubic
    (h01 : N01Properties D T S C base loss ε)
    (h04 : N04Properties D T S C L K base loss ε)
    {z : Parameter S} (hz : z ∈ sectorNeighborhood S base ε ε)
    {m : ℕ} (hm : K.positive m = true) (hlen : K.left m < K.right m) (i : Fin 3) :
    EqOn (n07aUnitDifferenceAtom D T S C L K z m (n07aCubicPrincipalAtom i))
      (fun p => (K.right m - K.left m) ^ 6 * cylinderWeight p.1 ^ 3 *
        n07aUnitDifferenceAtom D T S C L K z m (n07aCubicDividedAtom i) p) unitStrip := by
  intro p hp
  dsimp only
  have h := n07a_actual_cubic_difference h04 (liftSectorParameter_mem_stateNeighborhood hz le_rfl)
    (h01.2.2.1.liftSectorParameter_sector z) hm (n07aCanonicalUnitPoint_maps m hlen hp) i
  have hfun : n07aUnitDifferenceAtom D T S C L K z m (n07aCubicPrincipalAtom i) p =
      n07aCubicPrincipalField K (liftSectorParameter S C z) m i (canonicalUnitPoint K m p) -
        n07aCubicPrincipalField K (C.referenceState, 0) m i (canonicalUnitPoint K m p) := by
    fin_cases i <;> rfl
  rw [hfun, h, n07aUnitDifferenceAtom_divided h01 h04 z hm hlen hp i]
  congr 1
  change (((K.left m + (K.right m - K.left m) * p.1) - K.left m) *
      (K.right m - (K.left m + (K.right m - K.left m) * p.1))) ^ 3 =
        (K.right m - K.left m) ^ 6 * cylinderWeight p.1 ^ 3
  unfold cylinderWeight
  ring

end ContinuousFlexibility.Analysis
