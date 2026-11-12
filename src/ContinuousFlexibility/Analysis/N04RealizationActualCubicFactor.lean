import ContinuousFlexibility.Analysis.N07aActualCubicFactors
import ContinuousFlexibility.Analysis.CanonicalFieldJetReduction
import ContinuousFlexibility.Analysis.StateNeighborhood

/-!
# The actual cubic factor before the quantitative N04 certificate

Only the cut-operator identity and the reference state are needed for
this factorization. The divided field is the original field of the same
atlas. Its reference value vanishes on the open cylinder. No part of
the quantitative N04 estimate or CurrentJets is assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base : ℕ} {ε : ℝ}

/-- The displayed principal difference has the actual divided field as
its cubic factor, using only the qualitative cut-operator clause. -/
theorem n04Realization_actual_cubic_factor
    (hB : CanonicalCutOperatorProperties S C L K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) {m : ℕ} (hm : K.positive m = true)
    {p : PolarPoint} (hp : p ∈ canonicalOpen S K m) (i : Fin 3) :
    n07aCubicPrincipalField K z m i p -
        n07aCubicPrincipalField K (C.referenceState, 0) m i p =
      ((p.1 - K.left m) * (K.right m - p.1)) ^ 3 *
        n07aCubicDividedField K z m i p := by
  have h := canonicalCoefficientNumerator_factorization hB hz hs m hm i hp
  fin_cases i <;> exact h

/-- The genuine unit-coordinate difference has the exact fixed sixth
width power before any estimate is made. The reference divided value is
deduced from the same factorization and the open-cylinder denominator. -/
theorem n04Realization_unitDifference_cubic_factor
    (hB : CanonicalCutOperatorProperties S C L K base ε)
    (href : referenceStateConditions D S C) (hε : 0 < ε)
    {z : Parameter S} (hz : z ∈ sectorNeighborhood S base ε ε)
    {m : ℕ} (hm : K.positive m = true) (hlen : K.left m < K.right m)
    (i : Fin 3) :
    EqOn (n07aUnitDifferenceAtom D T S C L K z m (n07aCubicPrincipalAtom i))
      (fun p => (K.right m - K.left m) ^ 6 * (p.1 * (1 - p.1)) ^ 3 *
        n07aUnitDifferenceAtom D T S C L K z m (n07aCubicDividedAtom i) p) unitStrip := by
  intro p hp
  have hpK := n07aCanonicalUnitPoint_maps m hlen hp
  have hfactor := n04Realization_actual_cubic_factor hB
    (liftSectorParameter_mem_stateNeighborhood hz le_rfl)
    (href.liftSectorParameter_sector z) hm hpK i
  have hrefactor := n04Realization_actual_cubic_factor hB
    (reference_mem_stateNeighborhood S C base hε) href.stateSector hm hpK i
  have hd : ((canonicalUnitPoint K m p).1 - K.left m) *
      (K.right m - (canonicalUnitPoint K m p).1) ≠ 0 :=
    (mul_pos (sub_pos.mpr hpK.1.1) (sub_pos.mpr hpK.1.2)).ne'
  have hzero : n07aCubicDividedField K (C.referenceState, 0) m i
      (canonicalUnitPoint K m p) = 0 := by
    rw [sub_self] at hrefactor
    exact (mul_eq_zero.mp hrefactor.symm).resolve_left (pow_ne_zero 3 hd)
  have hprincipal :
      n07aUnitDifferenceAtom D T S C L K z m (n07aCubicPrincipalAtom i) p =
        n07aCubicPrincipalField K (liftSectorParameter S C z) m i
            (canonicalUnitPoint K m p) -
          n07aCubicPrincipalField K (C.referenceState, 0) m i
            (canonicalUnitPoint K m p) := by
    fin_cases i <;> rfl
  have hatom (z' : AnnularState S × ℝ) :
      atom D T S C L K z' m (n07aCubicDividedAtom i) p =
        if K.positive m then
          n07aCubicDividedField K z' m i (canonicalUnitPoint K m p) else 0 := by
    fin_cases i <;> rfl
  have hdivided :
      n07aUnitDifferenceAtom D T S C L K z m (n07aCubicDividedAtom i) p =
        n07aCubicDividedField K (liftSectorParameter S C z) m i
          (canonicalUnitPoint K m p) := by
    rw [n07aUnitDifferenceAtom, hatom, hatom, hm]
    simp only [↓reduceIte, hzero, sub_zero]
  rw [hprincipal, hfactor, hdivided]
  congr 1
  change (((K.left m + (K.right m - K.left m) * p.1) - K.left m) *
      (K.right m - (K.left m + (K.right m - K.left m) * p.1))) ^ 3 =
    (K.right m - K.left m) ^ 6 * (p.1 * (1 - p.1)) ^ 3
  ring

end ContinuousFlexibility.Analysis
