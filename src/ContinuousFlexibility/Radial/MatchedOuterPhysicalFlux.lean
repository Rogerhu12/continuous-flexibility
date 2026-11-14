module

public import ContinuousFlexibility.Radial.MatchedOuterWholeRepresentative
public import ContinuousFlexibility.Radial.MatchedWeakFluxEquation

/-!
# The outward Green equation on the original physical interval

The reflection changes the flux sign and the interval order together.
The actual source density has no orientation factor. These identities
give the complete physical modal equation for the same representatives.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology ContDiff
open ContinuousFlexibility.Statements ContinuousFlexibility.Analysis

theorem matchedOuterWhole_weakFlux_physical {D : ReferenceData}
    {right : Bool} {entry : ℝ} {j : ℕ} {u f : ℝ → ℝ}
    (h : HasIntervalWeakDerivative (outerOutwardRadius right entry)
      (outerOutwardRadius right (tailPhysicalEndpoint D right))
      (fun x => outerTailOutwardWeight D right x * deriv u x)
      (fun x => (j : ℝ) ^ 2 * deriv (outerTailOutwardWeight D right) x / x * u x -
        outerWholeDensity D right x * f x)) :
    HasIntervalWeakDerivative (if right then entry else D.a)
      (if right then D.b else entry)
      (fun r => D.w r * deriv (fun x => u (outerOutwardRadius right x)) r)
      (fun r => matchingPotential D j r * u (outerOutwardRadius right r) -
        matchingDensity D r * f (outerOutwardRadius right r)) := by
  cases right
  · have hw : outerTailOutwardWeight D false = fun x => D.w (-x) := by
      funext x
      simp only [outerTailOutwardWeight, outerTailSign, Bool.false_eq_true, ite_false,
        neg_one_mul]
    rw [hw] at h
    simp only [outerOutwardRadius, tailPhysicalEndpoint, Bool.false_eq_true, ite_false,
      outerTailOutwardWeight, outerTailSign, neg_one_mul] at h ⊢
    have hr := h.reflect
    simp only [neg_neg] at hr
    apply hr.congr_restrict
    · exact ae_of_all _ (fun r => by
        dsimp only
        rw [deriv_comp_neg]
        ring)
    · exact ae_of_all _ (fun r => by
        dsimp only [outerWholeDensity, outerOutwardRadius, matchingPotential,
          matchingDensity]
        simp only [Bool.false_eq_true, ite_false, deriv_comp_neg, neg_neg, neg_sq,
          div_neg, neg_div]
        ring)
  · have hw : outerTailOutwardWeight D true = D.w := by
      funext x
      simp only [outerTailOutwardWeight, outerTailSign, ite_true, one_mul]
    rw [hw] at h
    simpa only [outerOutwardRadius, tailPhysicalEndpoint, ite_true,
      outerTailOutwardWeight, outerTailSign, one_mul, outerWholeDensity,
      matchingPotential, matchingDensity] using h

theorem matchedOuterWhole_contDiff_physical {D : ReferenceData}
    {right : Bool} {entry : ℝ} {u : ℝ → ℝ} {n : ℕ∞ω}
    (hu : ContDiffOn ℝ n u (Ico (outerOutwardRadius right entry)
      (outerOutwardRadius right (tailPhysicalEndpoint D right)))) :
    ContDiffOn ℝ n (fun r => u (outerOutwardRadius right r))
      (if right then Ico entry D.b else Ioc D.a entry) := by
  cases right
  · simp only [outerOutwardRadius, tailPhysicalEndpoint, Bool.false_eq_true, ite_false]
      at hu ⊢
    apply hu.comp (contDiff_id.neg.contDiffOn)
    intro r hr
    exact ⟨neg_le_neg hr.2, neg_lt_neg hr.1⟩
  · exact hu

theorem matchedOuterWhole_modeLocalEquation {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D)
    {right : Bool} {entry : ℝ} (hentry : entry ∈ radialCore D)
    {j : ℕ} {U F : RadialModePair D} {u f : ℝ → ℝ}
    (hscalar : U.2 = 0)
    (hU : (U.1 : ℝ → ℝ) =ᵐ[(radialHilbertMeasure D).restrict
      (radialTailInterval D right entry)] fun r => u (outerOutwardRadius right r))
    (hF : (F.1 : ℝ → ℝ) =ᵐ[(radialHilbertMeasure D).restrict
      (radialTailInterval D right entry)] fun r => f (outerOutwardRadius right r))
    (hu : ContDiffOn ℝ 1 u (Ico (outerOutwardRadius right entry)
      (outerOutwardRadius right (tailPhysicalEndpoint D right))))
    (hweak : HasIntervalWeakDerivative (outerOutwardRadius right entry)
      (outerOutwardRadius right (tailPhysicalEndpoint D right))
      (fun x => outerTailOutwardWeight D right x * deriv u x)
      (fun x => (j : ℝ) ^ 2 * deriv (outerTailOutwardWeight D right) x / x * u x -
        outerWholeDensity D right x * f x)) :
    ModeLocalEquation D j (radialTailInterval D right entry) U F := by
  have hs : radialTailInterval D right entry ⊆ radialCore D := by
    cases right
    · exact fun r hr => ⟨hr.1, hr.2.trans hentry.2⟩
    · exact fun r hr => ⟨hentry.1.trans hr.1, hr.2⟩
  have hUv := (matching_restrict_ae_iff hD (by
    cases right <;> exact measurableSet_Ioo) hs).mp hU
  have hFv := (matching_restrict_ae_iff hD (by
    cases right <;> exact measurableSet_Ioo) hs).mp hF
  have hsource :
      (fun r => matchingPotential D j r * u (outerOutwardRadius right r) -
        matchingDensity D r * f (outerOutwardRadius right r)) =ᵐ[
        volume.restrict (radialTailInterval D right entry)] matchingPrincipalSource D j U F := by
    filter_upwards [hUv, hFv] with r hUr hFr
    simp only [matchingPrincipalSource, hscalar, zero_mul, add_zero, hUr, hFr]
  have hw := matchedOuterWhole_weakFlux_physical hweak
  have hc := matchedOuterWhole_contDiff_physical hu
  cases right
  · exact modeLocalEquation_of_weakFlux hD hB hentry.1 hs
      (hc.mono Ioo_subset_Ioc_self) hU
      (hw.congr_restrict EventuallyEq.rfl hsource)
  · exact modeLocalEquation_of_weakFlux hD hB hentry.2 hs
      (hc.mono Ioo_subset_Ico_self) hU
      (hw.congr_restrict EventuallyEq.rfl hsource)

end ContinuousFlexibility.Radial
