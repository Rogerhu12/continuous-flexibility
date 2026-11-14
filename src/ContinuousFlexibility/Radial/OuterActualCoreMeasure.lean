module

public import ContinuousFlexibility.Radial.OuterTransitionCoordinates

/-!
# The actual core Hilbert mass in the whole outward measure

The closed outward core pulls back to a half-open radial interval.
The endpoint convention is immaterial to the Lebesgue density integral,
and the resulting mass is exactly the one in the existing Morse bounds.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set MeasureTheory
open ContinuousFlexibility.Statements

theorem outer_radial_setIntegral_density {D : ReferenceData}
    (hD : RadialProfileGeometry D) {s : Set ℝ} (hs : MeasurableSet s)
    (hsub : s ⊆ radialCore D) (f : ℝ → ℝ) :
    (∫ x in s, f x ∂radialHilbertMeasure D) =
      ∫ x in s, (12 * D.w x / x ^ 2) * f x := by
  have hc : ContinuousOn (fun x => 12 * D.w x / x ^ 2) (radialCore D) :=
    (continuousOn_const.mul hD.2.2.1.1.continuous.continuousOn).div
      (continuousOn_id.pow 2) (fun x hx => (pow_pos (hD.1.trans hx.1) 2).ne')
  have hm : AEMeasurable (fun x => ENNReal.ofReal (12 * D.w x / x ^ 2))
      (volume.restrict s) :=
    ((hc.mono hsub).aemeasurable hs).ennreal_ofReal
  rw [radialHilbertMeasure, restrict_withDensity hs,
    Measure.restrict_restrict_of_subset hsub,
    integral_withDensity_eq_integral_toReal_smul₀ hm (by simp)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem hs] with x hx
  have hpos : 0 ≤ 12 * D.w x / x ^ 2 :=
    div_nonneg (mul_nonneg (by norm_num) (hD.2.2.2.2.1 x (hsub hx)).le) (sq_nonneg _)
  simp only [ENNReal.toReal_ofReal hpos, smul_eq_mul]

theorem outer_radial_measure_real {D : ReferenceData}
    (hD : RadialProfileGeometry D) {s : Set ℝ} (hs : MeasurableSet s)
    (hsub : s ⊆ radialCore D) :
    (radialHilbertMeasure D).real s = ∫ x in s, 12 * D.w x / x ^ 2 := by
  calc
    _ = ∫ x in s, (1 : ℝ) ∂radialHilbertMeasure D := by
      rw [integral_const, measureReal_restrict_apply_univ, smul_eq_mul, mul_one]
    _ = _ := by
      rw [outer_radial_setIntegral_density hD hs hsub]
      simp only [mul_one]

theorem outer_radial_measure_real_Ioc {D : ReferenceData}
    (hD : RadialProfileGeometry D) {l r : ℝ} (hlr : l ≤ r)
    (hsub : Icc l r ⊆ radialCore D) :
    (radialHilbertMeasure D).real (Ioc l r) = radialHilbertIntervalMass D l r := by
  rw [outer_radial_measure_real hD measurableSet_Ioc
      (Ioc_subset_Icc_self.trans hsub),
    radialHilbertIntervalMass, intervalIntegral.integral_of_le hlr]

theorem outer_radial_measure_real_Ico {D : ReferenceData}
    (hD : RadialProfileGeometry D) {l r : ℝ} (hlr : l ≤ r)
    (hsub : Icc l r ⊆ radialCore D) :
    (radialHilbertMeasure D).real (Ico l r) = radialHilbertIntervalMass D l r := by
  rw [outer_radial_measure_real hD measurableSet_Ico
      (Ico_subset_Icc_self.trans hsub),
    radialHilbertIntervalMass, intervalIntegral.integral_of_le hlr,
    integral_Ico_eq_integral_Ioc]

/-- The core mass in the whole Hilbert space equals its actual radial
density integral for either outward orientation. -/
theorem outerWholeMeasure_core_mass {D : ReferenceData}
    (hD : RadialProfileGeometry D) (right : Bool) {l r : ℝ} (hlr : l ≤ r)
    (hsub : Icc l r ⊆ radialCore D) :
    (outerWholeMeasure D right (if right then l else r)).real
      (Icc (if right then l else -r) (if right then r else -l)) =
        radialHilbertIntervalMass D l r := by
  have hl := hsub (left_mem_Icc.mpr hlr)
  have hr := hsub (right_mem_Icc.mpr hlr)
  have hs : outerOutwardRadius right ⁻¹'
        Icc (if right then l else -r) (if right then r else -l) ∩
      radialTailInterval D right (if right then l else r) =
        if right then Ioc l r else Ico l r := by
    cases right
    · ext x
      change (((-r ≤ -x ∧ -x ≤ -l) ∧ (D.a < x ∧ x < r)) ↔
        (l ≤ x ∧ x < r))
      constructor
      · intro hx
        exact ⟨by linarith only [hx.1.2], hx.2.2⟩
      · intro hx
        exact ⟨⟨by linarith only [hx.2], by linarith only [hx.1]⟩,
          hl.1.trans_le hx.1, hx.2⟩
    · ext x
      change (((l ≤ x ∧ x ≤ r) ∧ (l < x ∧ x < D.b)) ↔
        (l < x ∧ x ≤ r))
      constructor
      · intro hx
        exact ⟨hx.2.1, hx.1.2⟩
      · intro hx
        exact ⟨⟨hx.1.le, hx.2⟩, hx.1, hx.2.trans_lt hr.2⟩
  rw [measureReal_def, outerWholeMeasure,
    Measure.map_apply (measurableEmbedding_outerOutwardRadius right).measurable measurableSet_Icc,
    Measure.restrict_apply
      ((measurableEmbedding_outerOutwardRadius right).measurable measurableSet_Icc), hs]
  cases right
  · exact outer_radial_measure_real_Ico hD hlr hsub
  · exact outer_radial_measure_real_Ioc hD hlr hsub

theorem morseTransitionCore_measure_mass
    {M : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ}
    (h : MorseChainRealization M σ D C) {entry : ℝ}
    (he : entry ∈ morseInitialMiddle M) (right : Bool) (n : ℕ) (hn : M.index ≤ n) :
    (outerWholeMeasure D right (morseTransitionPhysicalEntry M entry right n)).real
      (Icc (morseTransitionOutwardLeft M entry right n)
        (morseTransitionOutwardRight M entry right n)) =
      radialHilbertIntervalMass D (morseTransitionCoreLeft M entry right n)
        (morseTransitionCoreRight M entry right n) := by
  have hi := morseTransitionCore_interval h he right n hn
  exact outerWholeMeasure_core_mass h.geometry right hi.1.le hi.2

end ContinuousFlexibility.Radial
