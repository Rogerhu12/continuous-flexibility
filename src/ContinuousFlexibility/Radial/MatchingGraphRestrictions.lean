import ContinuousFlexibility.Radial.ModeLocalMeasure
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass

/-!
# Restriction of the frozen modal equation to matching regions

The given source maps are the actual Hilbert-space restrictions.
These lemmas transport a global weak solution to the inner
and outer regions and preserve the inner border row.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

theorem matching_ae_ne {D : ReferenceData} (hD : IsAccumulatingProfile D) (c : ℝ) :
    ∀ᵐ r ∂radialHilbertMeasure D, r ≠ c :=
  (radialHilbertMeasure_ae_iff hD).mpr ((volume.restrict (radialCore D)).ae_ne c)

/-- A differential test vanishes away from the topological support of
the original test. -/
theorem matching_radialJacobi_eq_zero_of_notMem_tsupport
    {ψ : ℝ → ℝ} {r : ℝ} (hr : r ∉ tsupport ψ) (w : ℝ → ℝ) (J : ℝ) :
    radialJacobi J w ψ r = 0 := by
  have he : ψ =ᶠ[𝓝 r] fun _ => 0 := notMem_tsupport_iff_eventuallyEq.mp hr
  have hd : deriv ψ =ᶠ[𝓝 r] fun _ => 0 := by
    filter_upwards [he.deriv] with x hx
    simpa only [deriv_const] using hx
  have hp : (fun x => w x * deriv ψ x) =ᶠ[𝓝 r] fun _ => 0 := by
    filter_upwards [hd] with x hx
    simp only [hx, mul_zero]
  have hp' : deriv (fun x => w x * deriv ψ x) r = 0 := by
    simpa only [deriv_const] using hp.deriv_eq
  simp only [radialJacobi, hp', he.eq_of_nhds, mul_zero, sub_self]

theorem matchingInnerRegion_subset_radialCore {D : ReferenceData}
    {M : RadialMatchingData D} (ha : D.a < M.innerLeft) (hb : M.innerRight < D.b) :
    Ioo M.innerLeft M.innerRight ⊆ radialCore D :=
  fun _ hx => ⟨lt_trans ha hx.1, lt_trans hx.2 hb⟩

theorem matchingOuterRegion_subset_radialCore {D : ReferenceData}
    {M : RadialMatchingData D} (ha : D.a < M.innerLeft)
    (hm : M.innerLeft < M.innerRight) (hb : M.innerRight < D.b) :
    matchingOuterRegion D M ⊆ radialCore D := by
  intro r hr
  rcases hr with hr | hr
  · exact ⟨hr.1, lt_trans hr.2 (lt_trans hm hb)⟩
  · exact ⟨lt_trans (lt_trans ha hm) hr.1, hr.2⟩

theorem matching_sources_add {D : ReferenceData} {M : RadialMatchingData D}
    (hM : MatchingLocalRealizations D M) (U : RadialModePair D) :
    M.sourceInner U + M.sourceOuter U = U := by
  have hs := hM.2.2.2.1 U
  apply Prod.ext
  · change (M.sourceInner U).1 + (M.sourceOuter U).1 = U.1
    apply Lp.ext
    filter_upwards [Lp.coeFn_add (M.sourceInner U).1 (M.sourceOuter U).1,
      hs.2.2.1, hs.2.2.2] with r hsum hI hO
    rw [hsum, Pi.add_apply, hI, hO]
    split_ifs <;> simp
  · change (M.sourceInner U).2 + (M.sourceOuter U).2 = U.2
    rw [hs.1, hs.2.1, add_zero]

theorem matchingOuterRegion_not_mem_inner {D : ReferenceData}
    {M : RadialMatchingData D} {r : ℝ} (hr : r ∈ matchingOuterRegion D M) :
    r ∉ Ioo M.innerLeft M.innerRight := by
  intro hi
  rcases hr with hL | hR
  · exact lt_asymm hi.1 hL.2
  · exact lt_asymm hi.2 hR.1

theorem matching_ae_inner_or_outer {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (M : RadialMatchingData D) :
    ∀ᵐ r ∂radialHilbertMeasure D,
      r ∈ Ioo M.innerLeft M.innerRight ∨ r ∈ matchingOuterRegion D M := by
  have hcore : ∀ᵐ r ∂radialHilbertMeasure D, r ∈ radialCore D :=
    (radialHilbertMeasure_ae_iff hD).mpr (ae_restrict_mem measurableSet_Ioo)
  filter_upwards [hcore, matching_ae_ne hD M.innerLeft,
    matching_ae_ne hD M.innerRight] with r hr hL hR
  by_cases hi : r ∈ Ioo M.innerLeft M.innerRight
  · exact Or.inl hi
  · apply Or.inr
    rcases lt_or_gt_of_ne hL with hl | hl
    · exact Or.inl ⟨hr.1, hl⟩
    · have hle : M.innerRight ≤ r := le_of_not_gt (fun h => hi ⟨hl, h⟩)
      exact Or.inr ⟨lt_of_le_of_ne hle hR.symm, hr.2⟩

theorem matching_sourceInner_eq_self_of_support {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {M : RadialMatchingData D}
    (hM : MatchingLocalRealizations D M) {U : RadialModePair D}
    (hzero : (U.1 : ℝ → ℝ) =ᵐ[(radialHilbertMeasure D).restrict
      (matchingOuterRegion D M)] fun _ => 0) :
    M.sourceInner U = U := by
  have hs := hM.2.2.2.1 U
  apply Prod.ext
  · apply Lp.ext
    filter_upwards [hs.2.2.1, ae_imp_of_ae_restrict hzero,
      matching_ae_inner_or_outer hD M] with r hsrc hz hr
    rcases hr with hi | ho
    · rw [hsrc, if_pos hi]
    · rw [hsrc, if_neg (matchingOuterRegion_not_mem_inner ho), hz ho]
  · exact hs.1

theorem matching_sourceOuter_eq_self_of_support {D : ReferenceData}
    {M : RadialMatchingData D} (hM : MatchingLocalRealizations D M)
    {U : RadialModePair D} (hscalar : U.2 = 0)
    (hzero : (U.1 : ℝ → ℝ) =ᵐ[(radialHilbertMeasure D).restrict
      (Ioo M.innerLeft M.innerRight)] fun _ => 0) :
    M.sourceOuter U = U := by
  have hs := hM.2.2.2.1 U
  apply Prod.ext
  · apply Lp.ext
    filter_upwards [hs.2.2.2, ae_imp_of_ae_restrict hzero] with r hsrc hz
    by_cases hi : r ∈ Ioo M.innerLeft M.innerRight
    · rw [hsrc, if_pos hi, hz hi]
    · rw [hsrc, if_neg hi]
  · exact hs.2.1.trans hscalar.symm

theorem matching_sourceInner_innerPoisson {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {M : RadialMatchingData D}
    (hM : MatchingLocalRealizations D M) (i : Fin 2) :
    M.sourceInner (M.innerPoisson i) = M.innerPoisson i :=
  matching_sourceInner_eq_self_of_support hD hM (hM.2.2.2.2.2 i).2.2.1

theorem matching_sourceOuter_outerPoisson {D : ReferenceData}
    {M : RadialMatchingData D} (hM : MatchingLocalRealizations D M) (i : Fin 2) :
    M.sourceOuter (M.outerPoisson i) = M.outerPoisson i :=
  matching_sourceOuter_eq_self_of_support hM
    (hM.2.2.2.2.2 i).2.2.2.2.2.2.1 (hM.2.2.2.2.2 i).2.2.2.1

theorem matching_innerSource_testIntegral_eq {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {M : RadialMatchingData D}
    (hM : MatchingLocalRealizations D M) (F : RadialModePair D) {ψ : ℝ → ℝ}
    (hsupp : Function.support ψ ⊆ Ioo M.innerLeft M.innerRight) :
    (∫ r in D.a..D.b, (12 * D.w r / r ^ 2) * (M.sourceInner F).1 r * ψ r) =
      ∫ r in D.a..D.b, (12 * D.w r / r ^ 2) * F.1 r * ψ r := by
  apply matchingInterval_congr_ae hD
  filter_upwards [(hM.2.2.2.1 F).2.2.1] with r hr
  by_cases hi : r ∈ Ioo M.innerLeft M.innerRight
  · rw [hr, if_pos hi]
  · have hz : ψ r = 0 := by
      by_contra hz
      exact hi (hsupp hz)
    simp only [hz, mul_zero]

theorem matching_outerSource_testIntegral_eq {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {M : RadialMatchingData D}
    (hM : MatchingLocalRealizations D M) (F : RadialModePair D) {ψ : ℝ → ℝ}
    (hsupp : Function.support ψ ⊆ matchingOuterRegion D M) :
    (∫ r in D.a..D.b, (12 * D.w r / r ^ 2) * (M.sourceOuter F).1 r * ψ r) =
      ∫ r in D.a..D.b, (12 * D.w r / r ^ 2) * F.1 r * ψ r := by
  apply matchingInterval_congr_ae hD
  filter_upwards [(hM.2.2.2.1 F).2.2.2] with r hr
  by_cases hi : r ∈ Ioo M.innerLeft M.innerRight
  · have hz : ψ r = 0 := by
      by_contra hz
      exact matchingOuterRegion_not_mem_inner (hsupp hz) hi
    simp only [hz, mul_zero]
  · rw [hr, if_neg hi]

theorem matching_modeLocalEquation_innerSource_iff {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {M : RadialMatchingData D}
    (hM : MatchingLocalRealizations D M) {U F : RadialModePair D} :
    ModeLocalEquation D M.frequency (Ioo M.innerLeft M.innerRight) U (M.sourceInner F) ↔
      ModeLocalEquation D M.frequency (Ioo M.innerLeft M.innerRight) U F := by
  constructor
  · intro h ψ hψ hc hs
    have heq := h ψ hψ hc hs
    rwa [matching_innerSource_testIntegral_eq hD hM F hs] at heq
  · intro h ψ hψ hc hs
    rw [matching_innerSource_testIntegral_eq hD hM F hs]
    exact h ψ hψ hc hs

theorem matching_modeLocalEquation_outerSource_iff {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {M : RadialMatchingData D}
    (hM : MatchingLocalRealizations D M) {U F : RadialModePair D} :
    ModeLocalEquation D M.frequency (matchingOuterRegion D M) U (M.sourceOuter F) ↔
      ModeLocalEquation D M.frequency (matchingOuterRegion D M) U F := by
  constructor
  · intro h ψ hψ hc hs
    have heq := h ψ hψ hc hs
    rwa [matching_outerSource_testIntegral_eq hD hM F hs] at heq
  · intro h ψ hψ hc hs
    rw [matching_outerSource_testIntegral_eq hD hM F hs]
    exact h ψ hψ hc hs

theorem matching_sourceInner_borderRow_eq {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {M : RadialMatchingData D}
    (hM : MatchingLocalRealizations D M)
    (hcolumn : Function.support (referenceColumn D) ⊆ Ioo M.innerLeft M.innerRight)
    (U : RadialModePair D) :
    (∫ r in D.a..D.b, referenceColumn D r * (M.sourceInner U).1 r) =
      ∫ r in D.a..D.b, referenceColumn D r * U.1 r := by
  apply matchingInterval_congr_ae hD
  filter_upwards [(hM.2.2.2.1 U).2.2.1] with r hr
  by_cases hi : r ∈ Ioo M.innerLeft M.innerRight
  · rw [hr, if_pos hi]
  · have hc : referenceColumn D r = 0 := by
      by_contra hc
      exact hi (hcolumn hc)
    simp only [hr, if_neg hi, hc, zero_mul]

theorem matching_modeLocalEquation_sourceInner {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {M : RadialMatchingData D}
    (hM : MatchingLocalRealizations D M)
    (ha : D.a < M.innerLeft) (hb : M.innerRight < D.b)
    {U F : RadialModePair D}
    (hU : ModeLocalEquation D M.frequency (radialCore D) U F) :
    ModeLocalEquation D M.frequency (Ioo M.innerLeft M.innerRight) (M.sourceInner U) F := by
  intro ψ hψ hψc hsupp
  have heq := hU ψ hψ hψc
    (hsupp.trans (matchingInnerRegion_subset_radialCore ha hb))
  have htsupp : tsupport ψ ⊆ Icc M.innerLeft M.innerRight :=
    closure_minimal (hsupp.trans Ioo_subset_Icc_self) isClosed_Icc
  have hs := hM.2.2.2.1 U
  have hi :
      (∫ r in D.a..D.b,
        (M.sourceInner U).1 r * radialJacobi ((M.frequency : ℝ) ^ 2) D.w ψ r) =
      ∫ r in D.a..D.b, U.1 r * radialJacobi ((M.frequency : ℝ) ^ 2) D.w ψ r := by
    apply matchingInterval_congr_ae hD
    filter_upwards [hs.2.2.1, matching_ae_ne hD M.innerLeft,
      matching_ae_ne hD M.innerRight] with r hr hL hR
    by_cases hin : r ∈ Ioo M.innerLeft M.innerRight
    · rw [hr, if_pos hin]
    · have hout : r ∉ Icc M.innerLeft M.innerRight := by
        intro hc
        exact hin ⟨lt_of_le_of_ne hc.1 hL.symm, lt_of_le_of_ne hc.2 hR⟩
      have hz := matching_radialJacobi_eq_zero_of_notMem_tsupport
        (fun ht => hout (htsupp ht)) D.w ((M.frequency : ℝ) ^ 2)
      simp only [hz, mul_zero]
  rw [hi, hs.1]
  exact heq

theorem matching_modeLocalEquation_sourceOuter {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {M : RadialMatchingData D}
    (hM : MatchingLocalRealizations D M)
    (ha : D.a < M.innerLeft) (hm : M.innerLeft < M.innerRight)
    (hb : M.innerRight < D.b)
    (hcolumn : Function.support (referenceColumn D) ⊆ Ioo M.innerLeft M.innerRight)
    {U F : RadialModePair D}
    (hU : ModeLocalEquation D M.frequency (radialCore D) U F) :
    ModeLocalEquation D M.frequency (matchingOuterRegion D M) (M.sourceOuter U) F := by
  intro ψ hψ hψc hsupp
  have heq := hU ψ hψ hψc
    (hsupp.trans (matchingOuterRegion_subset_radialCore ha hm hb))
  have htsupp : tsupport ψ ⊆ Iic M.innerLeft ∪ Ici M.innerRight := by
    apply closure_minimal ?_ (isClosed_Iic.union isClosed_Ici)
    intro r hr
    rcases hsupp hr with hL | hR
    · exact Or.inl hL.2.le
    · exact Or.inr hR.1.le
  have hs := hM.2.2.2.1 U
  have hi :
      (∫ r in D.a..D.b,
        (M.sourceOuter U).1 r * radialJacobi ((M.frequency : ℝ) ^ 2) D.w ψ r) =
      ∫ r in D.a..D.b, U.1 r * radialJacobi ((M.frequency : ℝ) ^ 2) D.w ψ r := by
    apply matchingInterval_congr_ae hD
    filter_upwards [hs.2.2.2] with r hr
    by_cases hin : r ∈ Ioo M.innerLeft M.innerRight
    · have hout : r ∉ Iic M.innerLeft ∪ Ici M.innerRight := by
        rintro (hL | hR)
        · exact (not_le.mpr hin.1) hL
        · exact (not_le.mpr hin.2) hR
      have hz := matching_radialJacobi_eq_zero_of_notMem_tsupport
        (fun ht => hout (htsupp ht)) D.w ((M.frequency : ℝ) ^ 2)
      simp only [hz, mul_zero]
    · rw [hr, if_neg hin]
  have hcol : (fun r => referenceColumn D r * ψ r) = fun _ => 0 := by
    funext r
    by_cases hc : referenceColumn D r = 0
    · simp only [hc, zero_mul]
    · have hin := hcolumn hc
      have hz : ψ r = 0 := by
        by_contra hz
        rcases hsupp hz with hL | hR
        · exact lt_asymm hin.1 hL.2
        · exact lt_asymm hin.2 hR.1
      simp only [hz, mul_zero]
  have hcolint : (∫ r in D.a..D.b, referenceColumn D r * ψ r) = 0 := by
    rw [hcol, intervalIntegral.integral_zero]
  rw [hi, hs.2.1, hcolint]
  simpa only [hcolint, mul_zero, sub_zero, zero_mul] using heq

end ContinuousFlexibility.Radial
