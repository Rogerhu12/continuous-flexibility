import ContinuousFlexibility.Radial.MatchedOuterWholeHilbert
import ContinuousFlexibility.Radial.MatchedOuterSideGlue
import ContinuousFlexibility.Radial.ModeRegionSources

/-!
# The physical separated inverse from the two whole-tail operators

Each supplied whole-tail operator is transported by the actual restriction
and coordinate isometry, then extended by zero. Their sum, with scalar
coordinate zero, is the single exterior inverse used by the matching data.
The source projection leaves this same operator unchanged.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology ContDiff
open ContinuousFlexibility.Statements ContinuousFlexibility.Analysis

def matchedOuterSideInverse (D : ReferenceData) (right : Bool) (entry : ℝ)
    (R : OuterWholeL2 D right entry →L[ℝ] OuterWholeL2 D right entry) :
    RadialModeL2 D →L[ℝ] RadialModeL2 D :=
  (matchedOuterWholeExtend D right entry).comp
    (R.comp (matchedOuterWholeRestrict D right entry))

theorem matchedOuterSideInverse_apply (D : ReferenceData) (right : Bool) (entry : ℝ)
    (R : OuterWholeL2 D right entry →L[ℝ] OuterWholeL2 D right entry)
    (f : RadialModeL2 D) :
    matchedOuterSideInverse D right entry R f =
      matchedOuterWholeExtend D right entry
        (R (matchedOuterWholeRestrict D right entry f)) := by
  simp only [matchedOuterSideInverse, ContinuousLinearMap.comp_apply]

def matchedOuterSeparatedInverse (D : ReferenceData) (cut : Bool → ℝ)
    (R : ∀ side, OuterWholeL2 D side (cut side) →L[ℝ]
      OuterWholeL2 D side (cut side)) :
    RadialModePair D →L[ℝ] RadialModePair D :=
  (((matchedOuterSideInverse D false (cut false) (R false) +
      matchedOuterSideInverse D true (cut true) (R true)).comp
      (ContinuousLinearMap.fst ℝ (RadialModeL2 D) ℝ)).prod 0)

theorem matchedOuterSeparatedInverse_apply (D : ReferenceData) (cut : Bool → ℝ)
    (R : ∀ side, OuterWholeL2 D side (cut side) →L[ℝ]
      OuterWholeL2 D side (cut side)) (F : RadialModePair D) :
    matchedOuterSeparatedInverse D cut R F =
      (matchedOuterWholeExtend D false (cut false)
          (R false (matchedOuterWholeRestrict D false (cut false) F.1)) +
        matchedOuterWholeExtend D true (cut true)
          (R true (matchedOuterWholeRestrict D true (cut true) F.1)), 0) := by
  simp only [matchedOuterSeparatedInverse, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.add_apply, ContinuousLinearMap.zero_apply,
    matchedOuterSideInverse_apply]

theorem matchedOuterSeparatedInverse_scalar (D : ReferenceData) (cut : Bool → ℝ)
    (R : ∀ side, OuterWholeL2 D side (cut side) →L[ℝ]
      OuterWholeL2 D side (cut side)) (F : RadialModePair D) :
    (matchedOuterSeparatedInverse D cut R F).2 = 0 := by
  rw [matchedOuterSeparatedInverse_apply]

theorem matchedOuterWholeRestrict_sourceOuter (D : ReferenceData)
    (cut : Bool → ℝ) (hcut : cut false < cut true) (right : Bool)
    (F : RadialModePair D) :
    matchedOuterWholeRestrict D right (cut right)
        (modeOuterSource D (cut false) (cut true) F).1 =
      matchedOuterWholeRestrict D right (cut right) F.1 := by
  apply (matchedOuterWholeEquiv D right (cut right)).injective
  rw [matchedOuterWholeRestrict_apply, matchedOuterWholeRestrict_apply,
    LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.apply_symm_apply]
  apply Lp.ext
  filter_upwards [
    l2Restrict_coeFn (radialHilbertMeasure D) (radialTailInterval D right (cut right))
      (modeOuterSource D (cut false) (cut true) F).1,
    l2Restrict_coeFn (radialHilbertMeasure D) (radialTailInterval D right (cut right)) F.1,
    ae_restrict_of_ae (modeRegionSources_spec D (cut false) (cut true) F).2.2.2,
    ae_restrict_mem (show MeasurableSet (radialTailInterval D right (cut right)) by
      cases right <;> exact measurableSet_Ioo)] with r hleft hright hsource hr
  have hout : r ∉ Ioo (cut false) (cut true) := by
    cases right
    · exact fun hi => lt_asymm hi.1 hr.2
    · exact fun hi => lt_asymm hi.2 hr.1
  rw [hleft, hsource, if_neg hout, hright]

theorem matchedOuterSeparatedInverse_sourceOuter (D : ReferenceData) (cut : Bool → ℝ)
    (hcut : cut false < cut true)
    (R : ∀ side, OuterWholeL2 D side (cut side) →L[ℝ]
      OuterWholeL2 D side (cut side)) (F : RadialModePair D) :
    matchedOuterSeparatedInverse D cut R (modeOuterSource D (cut false) (cut true) F) =
      matchedOuterSeparatedInverse D cut R F := by
  rw [matchedOuterSeparatedInverse_apply, matchedOuterSeparatedInverse_apply,
    matchedOuterWholeRestrict_sourceOuter D cut hcut false F,
    matchedOuterWholeRestrict_sourceOuter D cut hcut true F]

theorem matchedOuterSeparatedInverse_representative {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (cut : Bool → ℝ) (hcut : cut false < cut true)
    (R : ∀ side, OuterWholeL2 D side (cut side) →L[ℝ]
      OuterWholeL2 D side (cut side)) (F : RadialModePair D)
    {u : Bool → ℝ → ℝ}
    (hu : ∀ side,
      (R side (matchedOuterWholeRestrict D side (cut side) F.1) : ℝ → ℝ) =ᵐ[
        outerWholeMeasure D side (cut side)] u side) :
    ((matchedOuterSeparatedInverse D cut R F).1 : ℝ → ℝ) =ᵐ[
      radialHilbertMeasure D] matchedOuterSideGlue (cut false) (cut true)
        (fun r => u false (outerOutwardRadius false r))
        (fun r => u true (outerOutwardRadius true r)) := by
  rw [matchedOuterSeparatedInverse_apply]
  have hcore : ∀ᵐ r ∂radialHilbertMeasure D, r ∈ radialCore D :=
    (radialHilbertMeasure_ae_iff hD).mpr (ae_restrict_mem measurableSet_Ioo)
  filter_upwards [
    matchedOuterWholeExtend_representative
      (R false (matchedOuterWholeRestrict D false (cut false) F.1)) (hu false),
    matchedOuterWholeExtend_representative
      (R true (matchedOuterWholeRestrict D true (cut true) F.1)) (hu true),
    Lp.coeFn_add
      (matchedOuterWholeExtend D false (cut false)
        (R false (matchedOuterWholeRestrict D false (cut false) F.1)))
      (matchedOuterWholeExtend D true (cut true)
        (R true (matchedOuterWholeRestrict D true (cut true) F.1))),
    hcore, matching_ae_ne hD (cut false), matching_ae_ne hD (cut true)]
      with r hleft hright hsum hr hneL hneR
  rw [hsum, Pi.add_apply, hleft, hright]
  by_cases hL : r < cut false
  · have hmemL : r ∈ radialTailInterval D false (cut false) := ⟨hr.1, hL⟩
    have hnotR : r ∉ radialTailInterval D true (cut true) :=
      fun h => lt_asymm h.1 (hL.trans hcut)
    rw [indicator_of_mem hmemL, indicator_of_notMem hnotR, add_zero,
      matchedOuterSideGlue_of_le _ _ hL.le]
  · have hgtL : cut false < r := lt_of_le_of_ne (le_of_not_gt hL) hneL.symm
    have hnotL : r ∉ radialTailInterval D false (cut false) := fun h => hL h.2
    by_cases hR : cut true < r
    · have hmemR : r ∈ radialTailInterval D true (cut true) := ⟨hR, hr.2⟩
      rw [indicator_of_notMem hnotL, indicator_of_mem hmemR, zero_add,
        matchedOuterSideGlue_of_ge hcut _ _ hR.le]
    · have hltR : r < cut true := lt_of_le_of_ne (le_of_not_gt hR) hneR
      have hnotR : r ∉ radialTailInterval D true (cut true) := fun h => hR h.1
      rw [indicator_of_notMem hnotL, indicator_of_notMem hnotR, add_zero,
        matchedOuterSideGlue_inner _ _ ⟨hgtL, hltR⟩]

/-- The two actual restricted inverse identities determine the original
physical pair, including its zero inner component. -/
theorem matchedOuterSeparatedInverse_eq_of_restrictions {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (cut : Bool → ℝ) (hcut : cut false < cut true)
    (R : ∀ side, OuterWholeL2 D side (cut side) →L[ℝ]
      OuterWholeL2 D side (cut side)) {U F : RadialModePair D} {u : ℝ → ℝ}
    (hrep : (U.1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] u)
    (hzero : ∀ r ∈ Ioo (cut false) (cut true), u r = 0)
    (hscalar : U.2 = 0)
    (hside : ∀ side,
      R side (matchedOuterWholeRestrict D side (cut side) F.1) =
        matchedOuterWholeRestrict D side (cut side) U.1) :
    matchedOuterSeparatedInverse D cut R F = U := by
  have hlocal (side : Bool) :
      (R side (matchedOuterWholeRestrict D side (cut side) F.1) : ℝ → ℝ) =ᵐ[
        outerWholeMeasure D side (cut side)] fun x => u (outerOutwardRadius side x) := by
    rw [hside side]
    exact matchedOuterWholeRestrict_representative U.1 (ae_restrict_of_ae hrep)
  have hi := matchedOuterSeparatedInverse_representative hD cut hcut R F hlocal
  simp only [outerOutwardRadius_twice] at hi
  have hg : matchedOuterSideGlue (cut false) (cut true) u u = u := by
    funext r
    dsimp only [matchedOuterSideGlue]
    split_ifs with hL hR
    · rfl
    · rfl
    · exact (hzero r ⟨lt_of_not_ge hL, lt_of_not_ge hR⟩).symm
  rw [hg] at hi
  apply Prod.ext
  · apply Lp.ext
    exact hi.trans hrep.symm
  · exact (matchedOuterSeparatedInverse_scalar D cut R F).trans hscalar.symm

end ContinuousFlexibility.Radial
