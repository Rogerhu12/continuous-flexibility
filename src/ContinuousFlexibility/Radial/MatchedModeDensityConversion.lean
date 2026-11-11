import ContinuousFlexibility.Radial.MatchedModeLocalization

/-!
# Cellwise conversion of physical sources and Hilbert fields

The modal inverse acts in varpi dr with varpi = 12 w / r². A physical
source f is represented by -f / varpi. Both this source conversion and
the return of a Hilbert field to ordinary dr cost one power of the
reciprocal density on a cell. These are actual local L² statements,
including measurability, rather than estimates of formal integrals.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory Statements
open scoped ENNReal RealInnerProductSpace InnerProductSpace

theorem matchedModeLebesgue_absolutelyContinuous {D : ReferenceData}
    (hD : IsAccumulatingProfile D) :
    volume.restrict (radialCore D) ≪ radialHilbertMeasure D := by
  change volume.restrict (radialCore D) ≪
    (volume.restrict (radialCore D)).withDensity
      (fun r => ENNReal.ofReal (matchingDensity D r))
  apply withDensity_absolutelyContinuous'
    (matchingDensity_measurable hD).ennreal_ofReal.aemeasurable
  filter_upwards [ae_restrict_mem (show MeasurableSet (radialCore D) from measurableSet_Ioo)]
    with r hr
  exact ne_of_gt (ENNReal.ofReal_pos.mpr (matchingDensity_pos hD hr))

theorem matchedDensity_integral_restrict {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (f : ℝ → ℝ) :
    (∫ r, f r ∂radialHilbertMeasure D) =
      ∫ r, matchingDensity D r * f r ∂volume.restrict (radialCore D) := by
  simpa only [intervalIntegral.integral_of_le (matchingProfileGeometry hD).2.1.le,
    integral_Ioc_eq_integral_Ioo, radialCore] using matchingDensity_integral hD f

/-- Returning a localized Hilbert field to ordinary dr costs the reciprocal
density, including genuine local L² membership. -/
theorem matchedMode_output_cell {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hP : RadialPartition D)
    (m : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ r ∈ D.cells m, (matchingDensity D r)⁻¹ ≤ B)
    (f : ℝ → ℝ)
    (hf : MemLp (fun r => D.localizer m r * f r) 2 (radialHilbertMeasure D)) :
    MemLp (fun r => D.localizer m r * f r) 2 (volume.restrict (radialCore D)) ∧
      (∫ r, (D.localizer m r * f r) ^ 2 ∂volume.restrict (radialCore D)) ≤
        B * ∫ r, (D.localizer m r * f r) ^ 2 ∂radialHilbertMeasure D := by
  let g : ℝ → ℝ := fun r => D.localizer m r * f r
  have hg : AEStronglyMeasurable g (volume.restrict (radialCore D)) :=
    hf.aestronglyMeasurable.mono_ac (matchedModeLebesgue_absolutelyContinuous hD)
  have hweighted : Integrable (fun r => matchingDensity D r * g r ^ 2)
      (volume.restrict (radialCore D)) :=
    (matchingDensity_integrable_iff hD (fun r => g r ^ 2)).mp hf.integrable_sq
  have hpoint : ∀ᵐ r ∂volume.restrict (radialCore D),
      g r ^ 2 ≤ B * (matchingDensity D r * g r ^ 2) := by
    filter_upwards [ae_restrict_mem (show MeasurableSet (radialCore D) from measurableSet_Ioo)]
      with r hr
    by_cases hz : D.localizer m r = 0
    · simp only [g, hz, zero_mul, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero]
    · have hc : r ∈ D.cells m := hP.2.2.1 m hz
      have hρ : 0 < matchingDensity D r := matchingDensity_pos hD hr
      have hone : 1 ≤ B * matchingDensity D r := by
        have hb := mul_le_mul_of_nonneg_right (hbound r hc) hρ.le
        rwa [inv_mul_cancel₀ hρ.ne'] at hb
      have hb := mul_le_mul_of_nonneg_right hone (sq_nonneg (g r))
      simpa only [one_mul, mul_assoc] using hb
  have hsq : Integrable (fun r => g r ^ 2) (volume.restrict (radialCore D)) := by
    apply (hweighted.const_mul B).mono' (hg.pow 2)
    filter_upwards [hpoint] with r hr
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (g r))] using hr
  refine ⟨(memLp_two_iff_integrable_sq hg).mpr hsq, ?_⟩
  have hle := integral_mono_ae hsq (hweighted.const_mul B) hpoint
  rw [integral_const_mul, ← matchedDensity_integral_restrict hD (fun r => g r ^ 2)] at hle
  exact hle

/-- The physical source enters the Hilbert inverse with its actual sign and
reciprocal density. Its local square norm has the same coefficient cost. -/
theorem matchedMode_source_cell {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hP : RadialPartition D)
    (m : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ r ∈ D.cells m, (matchingDensity D r)⁻¹ ≤ B)
    (f : ℝ → ℝ)
    (hf : MemLp (fun r => D.localizer m r * f r) 2
      (volume.restrict (radialCore D))) :
    MemLp (fun r => -(D.localizer m r * f r) / matchingDensity D r) 2
        (radialHilbertMeasure D) ∧
      (∫ r, (-(D.localizer m r * f r) / matchingDensity D r) ^ 2
        ∂radialHilbertMeasure D) ≤
        B * ∫ r, (D.localizer m r * f r) ^ 2
          ∂volume.restrict (radialCore D) := by
  let g : ℝ → ℝ := fun r => D.localizer m r * f r
  let q : ℝ → ℝ := fun r => -g r / matchingDensity D r
  have hq : AEStronglyMeasurable q (volume.restrict (radialCore D)) :=
    hf.aestronglyMeasurable.neg.div (matchingDensity_measurable hD).aestronglyMeasurable
  have hqμ : AEStronglyMeasurable q (radialHilbertMeasure D) :=
    hq.mono_ac (withDensity_absolutelyContinuous _ _)
  have hpoint : ∀ᵐ r ∂volume.restrict (radialCore D),
      matchingDensity D r * q r ^ 2 ≤ B * g r ^ 2 := by
    filter_upwards [ae_restrict_mem (show MeasurableSet (radialCore D) from measurableSet_Ioo)]
      with r hr
    by_cases hz : D.localizer m r = 0
    · simp only [q, g, hz, zero_mul, neg_zero, zero_div,
        zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero]
    · have hc : r ∈ D.cells m := hP.2.2.1 m hz
      have hρ : 0 < matchingDensity D r := matchingDensity_pos hD hr
      calc
        matchingDensity D r * q r ^ 2 = (matchingDensity D r)⁻¹ * g r ^ 2 := by
          dsimp only [q]
          field_simp [hρ.ne']
          <;> ring
        _ ≤ B * g r ^ 2 := mul_le_mul_of_nonneg_right (hbound r hc) (sq_nonneg _)
  have hweighted : Integrable (fun r => matchingDensity D r * q r ^ 2)
      (volume.restrict (radialCore D)) := by
    apply (hf.integrable_sq.const_mul B).mono'
      ((matchingDensity_measurable hD).aestronglyMeasurable.mul (hq.pow 2))
    filter_upwards [hpoint,
      ae_restrict_mem (show MeasurableSet (radialCore D) from measurableSet_Ioo)]
      with r hr hcore
    simpa only [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (matchingDensity_pos hD hcore).le (sq_nonneg (q r)))] using hr
  have hsq : Integrable (fun r => q r ^ 2) (radialHilbertMeasure D) :=
    (matchingDensity_integrable_iff hD (fun r => q r ^ 2)).mpr hweighted
  refine ⟨(memLp_two_iff_integrable_sq hqμ).mpr hsq, ?_⟩
  have hle := integral_mono_ae hweighted (hf.integrable_sq.const_mul B) hpoint
  rw [integral_const_mul, ← matchedDensity_integral_restrict hD (fun r => q r ^ 2)] at hle
  exact hle

/-- The preceding output estimate, for the actual localized modal L² class. -/
theorem matchedModeCell_physical_square_le {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hP : RadialPartition D)
    (m : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ r ∈ D.cells m, (matchingDensity D r)⁻¹ ≤ B)
    (u : RadialModeL2 D) :
    MemLp (fun r => D.localizer m r * u r) 2
        (volume.restrict (radialCore D)) ∧
      (∫ r, (D.localizer m r * u r) ^ 2 ∂volume.restrict (radialCore D)) ≤
        B * ‖matchedModeCellL2 D hP m u‖ ^ 2 := by
  have hu : MemLp (fun r => D.localizer m r * u r) 2 (radialHilbertMeasure D) :=
    (memLp_congr_ae (matchedModeCellL2_ae D hP m u)).mp
      (Lp.memLp (matchedModeCellL2 D hP m u))
  have h := matchedMode_output_cell hD hP m hB hbound u hu
  refine ⟨h.1, ?_⟩
  simpa only [matchedModeCellL2_norm_sq] using h.2

/-- One coefficient exponent works simultaneously for every radial cell
and every actual physical source or Hilbert field. -/
theorem exists_matchedMode_densityConversion {D : ReferenceData}
    (hD : IsAccumulatingProfile D) :
    ∃ K : ℝ, 0 < K ∧ ∀ m (f : ℝ → ℝ),
      (MemLp (fun r => D.localizer m r * f r) 2 (radialHilbertMeasure D) →
        MemLp (fun r => D.localizer m r * f r) 2 (volume.restrict (radialCore D)) ∧
          (∫ r, (D.localizer m r * f r) ^ 2 ∂volume.restrict (radialCore D)) ≤
            (K * radialE (D.cellIndex m) ^ K) *
              ∫ r, (D.localizer m r * f r) ^ 2 ∂radialHilbertMeasure D) ∧
      (MemLp (fun r => D.localizer m r * f r) 2 (volume.restrict (radialCore D)) →
        MemLp (fun r => -(D.localizer m r * f r) / matchingDensity D r) 2
            (radialHilbertMeasure D) ∧
          (∫ r, (-(D.localizer m r * f r) / matchingDensity D r) ^ 2
            ∂radialHilbertMeasure D) ≤
            (K * radialE (D.cellIndex m) ^ K) *
              ∫ r, (D.localizer m r * f r) ^ 2 ∂volume.restrict (radialCore D)) := by
  obtain ⟨K, hK, hbound⟩ := matchedDensity_inv_coefficient_bound hD
  have hP : RadialPartition D := by
    obtain ⟨C, hC⟩ := hD
    exact hC.2.1
  refine ⟨K, hK, ?_⟩
  intro m f
  have hB : 0 ≤ K * radialE (D.cellIndex m) ^ K := by
    exact mul_nonneg hK.le (Real.rpow_nonneg (Real.exp_pos _).le _)
  exact ⟨matchedMode_output_cell hD hP m hB (hbound m) f,
    matchedMode_source_cell hD hP m hB (hbound m) f⟩

end ContinuousFlexibility.Radial
