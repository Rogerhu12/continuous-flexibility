import ContinuousFlexibility.Radial.ModeCoreSource
import ContinuousFlexibility.Radial.MatchingGraphRestrictions

/-!
# Regional modal pairings

The Hilbert inner product equals its ordinary weighted integral. The
source projection clauses then localize supported factors to the actual
inner interval, and the outer projection has zero true border row.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace InnerProductSpace
open ContinuousFlexibility.Statements

theorem matchingModeProduct_intervalIntegrable {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (U F : RadialModeL2 D) :
    IntervalIntegrable (fun r => matchingDensity D r * U r * F r) volume D.a D.b := by
  have hi := (matchingDensity_integrable_iff hD (fun r => U r * F r)).mp
    ((Lp.memLp U).integrable_mul (Lp.memLp F))
  apply (intervalIntegrable_iff_integrableOn_Ioo_of_le
    (matchingProfileGeometry hD).2.1.le).mpr
  simpa only [mul_assoc] using hi

theorem matchingMode_inner_eq_integral {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (U F : RadialModeL2 D) :
    ⟪U, F⟫_ℝ = ∫ r in D.a..D.b, matchingDensity D r * U r * F r := by
  rw [L2.inner_def]
  calc
    (∫ r, ⟪U r, F r⟫_ℝ ∂radialHilbertMeasure D) =
        ∫ r, U r * F r ∂radialHilbertMeasure D := by
      apply integral_congr_ae
      filter_upwards with r
      simp only [RCLike.inner_apply, conj_trivial]
      ring
    _ = ∫ r in D.a..D.b, matchingDensity D r * (U r * F r) :=
      matchingDensity_integral hD _
    _ = _ := by
      congr 1
      funext r
      ring

theorem matchingSubinterval_ae {D : ReferenceData} (hD : IsAccumulatingProfile D)
    {l h : ℝ} (hsub : Icc l h ⊆ radialCore D) {f g : ℝ → ℝ}
    (he : f =ᵐ[radialHilbertMeasure D] g) :
    f =ᵐ[volume.restrict (Icc l h)] g :=
  ae_restrict_of_ae_restrict_of_subset hsub ((radialHilbertMeasure_ae_iff hD).mp he)

theorem matchingSubinterval_congr_ae {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {l h : ℝ} (hlh : l ≤ h)
    (hsub : Icc l h ⊆ radialCore D) {f g : ℝ → ℝ}
    (he : f =ᵐ[radialHilbertMeasure D] g) :
    (∫ r in l..h, f r) = ∫ r in l..h, g r := by
  have he' := (ae_restrict_iff' measurableSet_Icc).mp (matchingSubinterval_ae hD hsub he)
  apply intervalIntegral.integral_congr_ae
  filter_upwards [he'] with r hr hri
  apply hr
  simpa only [uIcc_of_le hlh] using uIoc_subset_uIcc hri

/-- An inner-supported modal vector can be replaced by its actual
representative and integrated over the inner interval. No regularity of
the other factor is required. -/
theorem matchingInner_integral_eq_of_fixed {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {M : RadialMatchingData D}
    (hM : MatchingLocalRealizations D M) (hlh : M.innerLeft ≤ M.innerRight)
    (hsub : Icc M.innerLeft M.innerRight ⊆ radialCore D)
    (U : RadialModePair D) (hfix : M.sourceInner U = U)
    {u : ℝ → ℝ} (hu : (U.1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] u)
    (q : ℝ → ℝ) :
    (∫ r in D.a..D.b, U.1 r * q r) =
      ∫ r in M.innerLeft..M.innerRight, u r * q r := by
  classical
  let f : ℝ → ℝ := (Ioo M.innerLeft M.innerRight).indicator (fun r => u r * q r)
  have hs : (U.1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
      (fun r => if r ∈ Ioo M.innerLeft M.innerRight then U.1 r else 0) := by
    simpa only [hfix] using (hM.2.2.2.1 U).2.2.1
  have he : (fun r => U.1 r * q r) =ᵐ[radialHilbertMeasure D] f := by
    filter_upwards [hs, hu] with r hsr hur
    by_cases hr : r ∈ Ioo M.innerLeft M.innerRight
    · simp only [f, Set.indicator_of_mem hr, hur]
    · simp only [hr, if_neg] at hsr
      simp only [f, Set.indicator_of_notMem hr, hsr, zero_mul]
  have hf : Function.support f ⊆ Ioo M.innerLeft M.innerRight := by
    intro r hr
    by_contra hn
    exact hr (by simp only [f, Set.indicator_of_notMem hn])
  calc
    _ = ∫ r in D.a..D.b, f r := matchingInterval_congr_ae hD he
    _ = ∫ r in M.innerLeft..M.innerRight, f r :=
      matchingInterval_eq_subinterval (Ioo_subset_Icc_self.trans hsub) hf
    _ = _ := by
      simp only [intervalIntegral.integral_of_le hlh, integral_Ioc_eq_integral_Ioo]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
      simp only [f, Set.indicator_of_mem hr]

theorem matching_sourceOuter_borderRow_zero {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {M : RadialMatchingData D}
    (hM : MatchingLocalRealizations D M)
    (hcolumn : Function.support (referenceColumn D) ⊆ Ioo M.innerLeft M.innerRight)
    (U : RadialModePair D) :
    (∫ r in D.a..D.b, referenceColumn D r * (M.sourceOuter U).1 r) = 0 := by
  calc
    _ = ∫ _r in D.a..D.b, (0 : ℝ) := by
      apply matchingInterval_congr_ae hD
      filter_upwards [(hM.2.2.2.1 U).2.2.2] with r hr
      by_cases hi : r ∈ Ioo M.innerLeft M.innerRight
      · simp only [hr, if_pos hi, mul_zero]
      · have hc : referenceColumn D r = 0 := by
          by_contra hc
          exact hi (hcolumn hc)
        simp only [hc, zero_mul]
    _ = 0 := by simp

theorem matching_outerPoisson_borderRow_zero {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {M : RadialMatchingData D}
    (hM : MatchingLocalRealizations D M)
    (hcolumn : Function.support (referenceColumn D) ⊆ Ioo M.innerLeft M.innerRight)
    (i : Fin 2) :
    (∫ r in D.a..D.b, referenceColumn D r * (M.outerPoisson i).1 r) = 0 := by
  rw [← matching_sourceOuter_outerPoisson hM i]
  exact matching_sourceOuter_borderRow_zero hD hM hcolumn (M.outerPoisson i)

end ContinuousFlexibility.Radial
