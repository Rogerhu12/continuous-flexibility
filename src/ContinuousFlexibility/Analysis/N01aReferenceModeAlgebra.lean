import ContinuousFlexibility.Analysis.N01aReferenceModeL2

/-!
# Almost-everywhere linearity of reference modes

The statements use actual representatives and the product measure, so
linearity is asserted on the radial full-measure set where the angular
integrals exist.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology

theorem referenceMode_sub_ae {D : ReferenceData} {u v : PolarPoint → ℝ}
    (hu : MemLp u 2 (radialPhysicalMeasure D))
    (hv : MemLp v 2 (radialPhysicalMeasure D)) (j : ℕ) :
    referenceMode (fun p => u p - v p) j =ᵐ[volume.restrict (radialCore D)]
      fun r => referenceMode u j r - referenceMode v j r := by
  have hc : Continuous (fun p : PolarPoint => Radial.cosineMode j p.2) := by
    unfold Radial.cosineMode
    fun_prop
  have hc2 : MemLp (fun p : PolarPoint => Radial.cosineMode j p.2) 2
      (radialPhysicalMeasure D) := continuous_memLp_radialPhysicalMeasure hc
  have hui := hu.integrable_mul hc2
  have hvi := hv.integrable_mul hc2
  rw [radialPhysicalMeasure_eq_prod] at hui hvi
  filter_upwards [hui.prod_right_ae, hvi.prod_right_ae] with r hur hvr
  have hur' : IntervalIntegrable (fun θ => u (r, θ) * Radial.cosineMode j θ)
      volume 0 (2 * Real.pi) := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)).mpr
    exact hur
  have hvr' : IntervalIntegrable (fun θ => v (r, θ) * Radial.cosineMode j θ)
      volume 0 (2 * Real.pi) := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)).mpr
    exact hvr
  simp only [referenceMode, radialAngularMean, sub_mul]
  rw [intervalIntegral.integral_sub hur' hvr', mul_sub]

theorem referenceMode_radial_zero (a : ℝ → ℝ) (j : ℕ) (hj : 0 < j) (r : ℝ) :
    referenceMode (fun p : PolarPoint => a p.1) j r = 0 :=
  referenceMode_eq_zero_of_angle_constant (fun _ => rfl) j hj

theorem referenceMode_outputRemainder_ae {D : ReferenceData}
    (hchi : Continuous D.chiLeft) {U : RadialUnknown}
    (hU : MemLp U.1 2 (radialPhysicalMeasure D)) (aL : ℝ) (j : ℕ) (hj : 0 < j) :
    referenceMode (outputRemainder D aL U) j =ᵐ[volume.restrict (radialCore D)]
      referenceMode U.1 j := by
  have hleft : MemLp (fun p : PolarPoint => aL * D.chiLeft p.1) 2
      (radialPhysicalMeasure D) :=
    continuous_memLp_radialPhysicalMeasure
      (continuous_const.mul (hchi.comp continuous_fst))
  have h := referenceMode_sub_ae hU hleft j
  filter_upwards [h] with r hr
  simpa only [referenceMode_radial_zero (fun x => aL * D.chiLeft x) j hj r,
    sub_zero] using hr

theorem referenceMode_congr_ae {D : ReferenceData} {u v : PolarPoint → ℝ}
    (h : u =ᵐ[radialPhysicalMeasure D] v) (j : ℕ) :
    referenceMode u j =ᵐ[volume.restrict (radialCore D)] referenceMode v j := by
  rw [radialPhysicalMeasure_eq_prod] at h
  filter_upwards [ae_ae_of_ae_prod h] with r hr
  unfold referenceMode radialAngularMean
  rw [intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi),
    intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
  congr 1
  exact integral_congr_ae (hr.mono fun θ hθ => by rw [hθ])

/-- The natural radial Hilbert measure is bounded above by a finite constant
times ordinary radial measure on the fixed physical core. -/
theorem memLp_radialHilbertMeasure_of_memLp {D : ReferenceData}
    (hgeo : RadialProfileGeometry D) {f : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (radialCore D))) :
    MemLp f 2 (radialHilbertMeasure D) := by
  have hρ : ContinuousOn (fun r => 12 * D.w r / r ^ 2) (Icc D.a D.b) :=
    (continuousOn_const.mul hgeo.2.2.1.1.continuous.continuousOn).div
      (continuousOn_id.pow 2)
      (fun r hr => pow_ne_zero 2 (hgeo.1.trans_le hr.1).ne')
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hρ
  have hmeasure : radialHilbertMeasure D ≤ ENNReal.ofReal B •
      volume.restrict (radialCore D) := by
    unfold radialHilbertMeasure
    rw [← Measure.withDensity_const]
    apply Measure.withDensity_mono
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    apply ENNReal.ofReal_le_ofReal
    exact (le_abs_self _).trans (hB r ⟨hr.1.le, hr.2.le⟩)
  exact hf.of_measure_le_smul ENNReal.ofReal_ne_top hmeasure

/-- Positivity of the physical density makes its null sets exactly the
ordinary radial null sets in the open core. -/
theorem radialHilbertMeasure_ae_iff {D : ReferenceData}
    (hgeo : RadialProfileGeometry D) {p : ℝ → Prop} :
    (∀ᵐ r ∂radialHilbertMeasure D, p r) ↔
      ∀ᵐ r ∂volume.restrict (radialCore D), p r := by
  have hm : Measurable (fun r => ENNReal.ofReal (12 * D.w r / r ^ 2)) :=
    ((measurable_const.mul hgeo.2.2.1.1.continuous.measurable).div
      (measurable_id.pow_const 2)).ennreal_ofReal
  rw [radialHilbertMeasure, ae_withDensity_iff hm]
  constructor
  · intro h
    filter_upwards [h, ae_restrict_mem measurableSet_Ioo] with r hr hrI
    apply hr
    apply ne_of_gt
    apply ENNReal.ofReal_pos.mpr
    exact div_pos (mul_pos (by norm_num) (hgeo.2.2.2.2.1 r hrI))
      (sq_pos_of_pos (hgeo.1.trans hrI.1))
  · intro h
    exact h.mono fun r hr _ => hr

end ContinuousFlexibility.Statements
