import ContinuousFlexibility.Radial.MatchedRadiusMultipliers
import ContinuousFlexibility.Radial.MatchedOuterModalCells

/-!
# Exact localization under the retained radius isometry

The localizers are those of the two actual reference data.  Their
coordinate identity intertwines the existing multipliers and the
existing transported inverse, hence preserves every localized norm.
Only points in the actual whole-tail measure are used.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open ContinuousFlexibility.Statements

variable {D E : ReferenceData} {μ ν : Measure ℝ} {κ β : ℝ}

/-- The same order-coordinate retained by the geometry constructor gives
the localizer identity on the entire restricted outer tail, for every
cell label, including the initial labels. -/
theorem matchedOuter_localizer_radius_ae
    (e : ℝ ≃o ℝ) (hlocal : E.localizer = fun m r => D.localizer m (e r))
    (right : Bool) (cut : ℝ)
    (he : ∀ r ∈ radialTailInterval D right cut, e.symm r = κ * r)
    (m : ℕ) :
    (fun x => E.localizer m (outerOutwardRadius right (κ * x))) =ᵐ[
      outerWholeMeasure D right cut]
      fun x => D.localizer m (outerOutwardRadius right x) := by
  apply (measurableEmbedding_outerOutwardRadius right).ae_map_iff.mpr
  have hmem : ∀ᵐ r ∂(radialHilbertMeasure D).restrict (radialTailInterval D right cut),
      r ∈ radialTailInterval D right cut :=
    ae_restrict_mem (by cases right <;> exact measurableSet_Ioo)
  filter_upwards [hmem] with r hr
  have hreflect : outerOutwardRadius right (κ * outerOutwardRadius right r) = κ * r := by
    cases right <;> simp [outerOutwardRadius]
  change E.localizer m (outerOutwardRadius right (κ * outerOutwardRadius right r)) =
    D.localizer m (outerOutwardRadius right (outerOutwardRadius right r))
  rw [hreflect, outerOutwardRadius_twice, hlocal, ← he r hr]
  change D.localizer m (e (e.symm r)) = D.localizer m r
  rw [e.apply_symm_apply]

theorem inverseRadiusEquiv_matchedOuterCell
    (hD : RadialPartition D) (hE : RadialPartition E) (right : Bool)
    (hκ : κ ≠ 0) (hβ : 0 < β)
    (hm : ν = ENNReal.ofReal β • μ.map (fun r => κ * r))
    (m : ℕ)
    (hlocal : (fun x => E.localizer m (outerOutwardRadius right (κ * x))) =ᵐ[μ]
      fun x => D.localizer m (outerOutwardRadius right x))
    (f : Lp ℝ 2 ν) :
    inverseRadiusEquiv hκ hβ hm (matchedOuterCell E hE right ν m f) =
      matchedOuterCell D hD right μ m (inverseRadiusEquiv hκ hβ hm f) := by
  exact inverseRadiusEquiv_multiplier hκ hβ hm
    (matchedOuter_localizer_measurable hD right μ m)
    (matchedOuter_localizer_measurable hE right ν m)
    (Eventually.of_forall fun x => matchedRadialLocalizer_abs_le_one hD m
      (outerOutwardRadius right x))
    (Eventually.of_forall fun x => matchedRadialLocalizer_abs_le_one hE m
      (outerOutwardRadius right x))
    hlocal f

/-- Localization commutes with the very operator used by the selected
inverse constructor. -/
theorem inverseRadiusOperator_matchedOuterCells
    (hD : RadialPartition D) (hE : RadialPartition E) (right : Bool)
    (hκ : κ ≠ 0) (hβ : 0 < β)
    (hm : ν = ENNReal.ofReal β • μ.map (fun r => κ * r))
    (R : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (k m : ℕ)
    (hk : (fun x => E.localizer k (outerOutwardRadius right (κ * x))) =ᵐ[μ]
      fun x => D.localizer k (outerOutwardRadius right x))
    (hmχ : (fun x => E.localizer m (outerOutwardRadius right (κ * x))) =ᵐ[μ]
      fun x => D.localizer m (outerOutwardRadius right x)) :
    (matchedOuterCell E hE right ν k).comp
        ((inverseRadiusOperator hκ hβ hm R).comp (matchedOuterCell E hE right ν m)) =
      inverseRadiusOperator hκ hβ hm
        ((matchedOuterCell D hD right μ k).comp
          (R.comp (matchedOuterCell D hD right μ m))) := by
  let U := inverseRadiusEquiv hκ hβ hm
  have hcommk := inverseRadiusEquiv_matchedOuterCell hD hE right hκ hβ hm k hk
  have hcommm := inverseRadiusEquiv_matchedOuterCell hD hE right hκ hβ hm m hmχ
  apply ContinuousLinearMap.ext
  intro f
  apply U.injective
  simp only [ContinuousLinearMap.comp_apply, inverseRadiusOperator_apply]
  change U (matchedOuterCell E hE right ν k
      (U.symm (R (U (matchedOuterCell E hE right ν m f))))) =
    U (U.symm (matchedOuterCell D hD right μ k
      (R (matchedOuterCell D hD right μ m (U f)))))
  rw [hcommk, U.apply_symm_apply, hcommm, U.apply_symm_apply]

theorem norm_inverseRadiusOperator_matchedOuterCells
    (hD : RadialPartition D) (hE : RadialPartition E) (right : Bool)
    (hκ : κ ≠ 0) (hβ : 0 < β)
    (hm : ν = ENNReal.ofReal β • μ.map (fun r => κ * r))
    (R : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (k m : ℕ)
    (hk : (fun x => E.localizer k (outerOutwardRadius right (κ * x))) =ᵐ[μ]
      fun x => D.localizer k (outerOutwardRadius right x))
    (hmχ : (fun x => E.localizer m (outerOutwardRadius right (κ * x))) =ᵐ[μ]
      fun x => D.localizer m (outerOutwardRadius right x)) :
    ‖(matchedOuterCell E hE right ν k).comp
        ((inverseRadiusOperator hκ hβ hm R).comp (matchedOuterCell E hE right ν m))‖ =
      ‖(matchedOuterCell D hD right μ k).comp
        (R.comp (matchedOuterCell D hD right μ m))‖ := by
  rw [inverseRadiusOperator_matchedOuterCells hD hE right hκ hβ hm R k m hk hmχ,
    norm_inverseRadiusOperator]

theorem norm_matchedOuterCell_inverseRadiusEquiv
    (hD : RadialPartition D) (hE : RadialPartition E) (right : Bool)
    (hκ : κ ≠ 0) (hβ : 0 < β)
    (hm : ν = ENNReal.ofReal β • μ.map (fun r => κ * r))
    (m : ℕ)
    (hlocal : (fun x => E.localizer m (outerOutwardRadius right (κ * x))) =ᵐ[μ]
      fun x => D.localizer m (outerOutwardRadius right x))
    (f : Lp ℝ 2 ν) :
    ‖matchedOuterCell E hE right ν m f‖ =
      ‖matchedOuterCell D hD right μ m (inverseRadiusEquiv hκ hβ hm f)‖ := by
  rw [← (inverseRadiusEquiv hκ hβ hm).norm_map,
    inverseRadiusEquiv_matchedOuterCell hD hE right hκ hβ hm m hlocal]

/-- Forward transport of the supplied boundary-normalized representative,
without choosing another natural solution or dividing by its cut value. -/
theorem inverseRadiusEquiv_normalized_ae
    (hκ : κ ≠ 0) (hβ : 0 < β)
    (hm : ν = ENNReal.ofReal β • μ.map (fun r => κ * r))
    {f : Lp ℝ 2 ν} {V : ℝ → ℝ} {lam : ℝ}
    (hf : (f : ℝ → ℝ) =ᵐ[ν] fun r => V (r / κ) / sqrt (β * lam)) :
    (inverseRadiusEquiv hκ hβ hm f : ℝ → ℝ) =ᵐ[μ]
      fun r => V r / sqrt lam := by
  filter_upwards [inverseRadiusEquiv_ae_of_ae hκ hβ hm hf] with r hr
  have hcancel : κ * r / κ = r := by field_simp [hκ]
  rw [hr, hcancel, sqrt_mul hβ.le]
  rw [← mul_div_assoc, mul_div_mul_left _ _ (sqrt_pos.mpr hβ).ne']

end ContinuousFlexibility.Radial
