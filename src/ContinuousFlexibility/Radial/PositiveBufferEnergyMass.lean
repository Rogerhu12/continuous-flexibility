import ContinuousFlexibility.Radial.PositiveBufferEnergyBufferProfiles
import ContinuousFlexibility.Radial.PositiveBufferComparisonCoordinates
import ContinuousFlexibility.Radial.PositiveBufferComparisonDomains
import ContinuousFlexibility.Radial.PositiveBufferComparisonScaling
import ContinuousFlexibility.Radial.BufferCutGlue

/-!
# Square-mass control by the genuine positive-buffer energy

Positive potential bounds the square-mass integral by the physical energy.
The same positivity recovers derivative and weighted L² membership from
the actual energy density. Affine changes preserve these concrete local
energy data, including for measurable derivative representatives.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

theorem positiveBuffer_cutGlue_memLp {f g : ℝ → ℝ} (c : ℝ)
    (hf : MemLp f 2 (volume.restrict (Iic c)))
    (hg : MemLp g 2 (volume.restrict (Ioi c))) :
    MemLp (bufferCutGlue c f g) 2 volume := by
  classical
  have h := MemLp.piecewise measurableSet_Iic hf
    (by simpa only [compl_Iic] using hg)
  have heq : (Iic c).piecewise f g = bufferCutGlue c f g := by
    funext x
    by_cases hx : x ≤ c
    · rw [piecewise_eq_of_mem _ _ _ (mem_Iic.mpr hx), bufferCutGlue_of_le _ _ _ hx]
    · rw [piecewise_eq_of_notMem _ _ _ (fun h => hx (mem_Iic.mp h)),
        bufferCutGlue_of_lt _ _ _ (lt_of_not_ge hx)]
  rwa [heq] at h

theorem positiveBuffer_square_mass_bound {V p d : ℝ → ℝ} {m : ℝ}
    (s : Set ℝ) (hs : MeasurableSet s) (hVm : ∀ x ∈ s, m ^ 2 ≤ V x)
    (hp : IntegrableOn (fun x => p x ^ 2) s volume)
    (hE : IntegrableOn (fun x => d x ^ 2 + V x * p x ^ 2) s volume) :
    m ^ 2 * (∫ x in s, p x ^ 2) ≤ ∫ x in s, d x ^ 2 + V x * p x ^ 2 := by
  rw [← integral_const_mul]
  apply integral_mono_ae (hp.const_mul (m ^ 2)) hE
  filter_upwards [ae_restrict_mem hs] with x hx
  have hpot := mul_le_mul_of_nonneg_right (hVm x hx) (sq_nonneg (p x))
  linarith [sq_nonneg (d x)]

/-- Nonnegative potential makes both derivative energy and weighted
potential energy individually integrable. -/
theorem positiveBuffer_energy_memLp {V p d : ℝ → ℝ}
    (hV : Continuous V) (hp : Continuous p) (hd : Continuous d)
    (s : Set ℝ) (hs : MeasurableSet s) (hpos : ∀ x ∈ s, 0 ≤ V x)
    (hpLp : MemLp p 2 (volume.restrict s))
    (hE : IntegrableOn (fun x => d x ^ 2 + V x * p x ^ 2) s volume) :
    MemLp d 2 (volume.restrict s) ∧
      MemLp (fun x => sqrt (1 + |V x|) * p x) 2 (volume.restrict s) := by
  have hdSq : IntegrableOn (fun x => d x ^ 2) s volume := by
    apply hE.mono' (hd.pow 2).aestronglyMeasurable
    filter_upwards [ae_restrict_mem hs] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact le_add_of_nonneg_right (mul_nonneg (hpos x hx) (sq_nonneg _))
  have hw : Continuous (fun x => sqrt (1 + |V x|) * p x) :=
    (continuous_const.add hV.abs).sqrt.mul hp
  have hwSq : IntegrableOn (fun x => (sqrt (1 + |V x|) * p x) ^ 2) s volume := by
    apply (hpLp.integrable_sq.add hE).mono' (hw.pow 2).aestronglyMeasurable
    filter_upwards [ae_restrict_mem hs] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), mul_pow,
      sq_sqrt (by positivity), abs_of_nonneg (hpos x hx)]
    nlinarith [sq_nonneg (d x)]
  exact ⟨(memLp_two_iff_integrable_sq hd.aestronglyMeasurable).mpr hdSq,
    (memLp_two_iff_integrable_sq hw.aestronglyMeasurable).mpr hwSq⟩

theorem positiveBuffer_affine_integrableOn {f : ℝ → ℝ} {s : Set ℝ}
    (hs : MeasurableSet s) (hf : IntegrableOn f s volume)
    (a : ℝ) {b : ℝ} (hb : b ≠ 0) :
    IntegrableOn (fun x => f (a + b * x)) ((fun x : ℝ => a + b * x) ⁻¹' s) volume := by
  have haff : Measurable (fun x : ℝ => a + b * x) :=
    measurable_const.add (measurable_const.mul measurable_id)
  apply (integrable_indicator_iff (hs.preimage haff)).mp
  have h := positiveBuffer_affine_integrable ((integrable_indicator_iff hs).mpr hf) a hb
  have heq : ((fun x : ℝ => a + b * x) ⁻¹' s).indicator (fun x => f (a + b * x)) =
      fun x => s.indicator f (a + b * x) := by
    funext x
    simp only [indicator_apply, mem_preimage]
  rw [heq]
  exact h

/-- The restricted affine L² transfer does not require continuity. It
therefore applies to the actual derivative of a glued Green profile. -/
theorem positiveBuffer_affine_memLp_two_restrict {f : ℝ → ℝ} {s : Set ℝ}
    (hs : MeasurableSet s) (hf : MemLp f 2 (volume.restrict s))
    (a : ℝ) {b : ℝ} (hb : b ≠ 0) :
    MemLp (fun x => f (a + b * x)) 2
      (volume.restrict ((fun x : ℝ => a + b * x) ⁻¹' s)) := by
  have hq : QuasiMeasurePreserving (fun x : ℝ => a + b * x) volume volume := by
    simpa only [Function.comp_def, smul_eq_mul] using
      (measurePreserving_add_left (volume : Measure ℝ) a).quasiMeasurePreserving.comp
        (Measure.quasiMeasurePreserving_smul (volume : Measure ℝ) hb)
  have hqr := hq.restrict (show MapsTo (fun x : ℝ => a + b * x)
      ((fun x : ℝ => a + b * x) ⁻¹' s) s from fun _ hx => hx)
  have hmeas := hf.aestronglyMeasurable.comp_quasiMeasurePreserving hqr
  apply (memLp_two_iff_integrable_sq hmeas).mpr
  exact positiveBuffer_affine_integrableOn hs hf.integrable_sq a hb

theorem positiveBufferPoint_integrableOn {B : BufferData}
    (hB : BufferHypotheses B) (i : Fin 2) {f : ℝ → ℝ} {s : Set ℝ}
    (hs : MeasurableSet s) (hf : IntegrableOn f s volume) :
    IntegrableOn (fun t => f (positiveBufferPoint B i t))
      ((positiveBufferPoint B i) ⁻¹' s) volume := by
  simpa only [← positiveBufferPoint_affine] using positiveBuffer_affine_integrableOn hs hf
    (bufferCut B i) (positiveBufferPoint_slope_ne_zero hB i)

/-- The normalized finite and exterior square-mass integrals are bounded
by the sum of the actual conormal energies divided by the mass. -/
theorem positiveBuffer_normalized_profile_square_mass {B : BufferData}
    (hB : BufferHypotheses B) (i : Fin 2) {pin pout : ℝ → ℝ} {αin αout : ℝ}
    (hpin : Continuous pin)
    (hpout : MemLp pout 2 (volume.restrict (bufferExterior B i)))
    (hEin : IntervalIntegrable (fun x => deriv pin x ^ 2 + B.potential x * pin x ^ 2)
      volume (bufferCut B i) (bufferInnerWall B i))
    (hEout : IntegrableOn (fun x => deriv pout x ^ 2 + B.potential x * pout x ^ 2)
      (bufferExterior B i) volume)
    (hαin : αin = ∫ x in min (bufferCut B i) (bufferInnerWall B i)..
      max (bufferCut B i) (bufferInnerWall B i), deriv pin x ^ 2 + B.potential x * pin x ^ 2)
    (hαout : αout = ∫ x in bufferExterior B i,
      deriv pout x ^ 2 + B.potential x * pout x ^ 2) :
    IntegrableOn (fun t => pout (positiveBufferPoint B i (-t)) ^ 2) (Ici 0) volume ∧
      (∫ t in Icc 0 (B.action i + 6), pin (positiveBufferPoint B i t) ^ 2) +
        (∫ t in Ici 0, pout (positiveBufferPoint B i (-t)) ^ 2) ≤
          (αin + αout) / B.mass i := by
  have hm := buffer_mass_pos hB i
  have hs : MeasurableSet (bufferExterior B i) := by
    unfold bufferExterior
    split_ifs
    · exact measurableSet_Iio
    · exact measurableSet_Ioi
  have hinI : IntegrableOn (fun x => deriv pin x ^ 2 + B.potential x * pin x ^ 2)
      (uIcc (bufferCut B i) (bufferInnerWall B i)) volume := intervalIntegrable_iff'.mp hEin
  have hinE : (∫ x in uIcc (bufferCut B i) (bufferInnerWall B i),
      deriv pin x ^ 2 + B.potential x * pin x ^ 2) = αin := by
    simpa only [intervalIntegral.integral_of_le
      (min_le_max (bufferCut B i) (bufferInnerWall B i)),
      ← integral_Icc_eq_integral_Ioc, Icc_min_max] using hαin.symm
  have hFin := positiveBuffer_square_mass_bound
    (uIcc (bufferCut B i) (bufferInnerWall B i)) measurableSet_uIcc
    (fun x hx => positiveBuffer_potential_lower_span hB i hx)
    (hpin.pow 2).integrableOn_Icc hinI
  rw [hinE] at hFin
  have hExt := positiveBuffer_square_mass_bound (bufferExterior B i) hs
    (fun x hx => positiveBuffer_potential_lower_exterior hB i (subset_closure hx))
    hpout.integrable_sq hEout
  rw [← hαout] at hExt
  have hFinChange := positiveBufferPoint_setIntegral hB i (fun x => pin x ^ 2)
    (s := uIcc (bufferCut B i) (bufferInnerWall B i)) measurableSet_uIcc
  rw [positiveBufferPoint_preimage_span hB i] at hFinChange
  have hOutChange := positiveBufferPoint_setIntegral hB i (fun x => pout x ^ 2) hs
  rw [positiveBufferPoint_preimage_exterior hB i] at hOutChange
  have hOutEq : (∫ t in Ici 0, pout (positiveBufferPoint B i (-t)) ^ 2) =
      B.mass i * ∫ x in bufferExterior B i, pout x ^ 2 := by
    calc
      _ = ∫ t in Iio 0, pout (positiveBufferPoint B i t) ^ 2 := by
        rw [integral_Ici_eq_integral_Ioi]
        simpa only [neg_zero, integral_Iic_eq_integral_Iio] using
          integral_comp_neg_Ioi (0 : ℝ) (fun t => pout (positiveBufferPoint B i t) ^ 2)
      _ = _ := hOutChange
  have hPointI := positiveBufferPoint_integrableOn hB i hs hpout.integrable_sq
  rw [positiveBufferPoint_preimage_exterior hB i] at hPointI
  have hOutI : IntegrableOn (fun t => pout (positiveBufferPoint B i (-t)) ^ 2)
      (Ici 0) volume := by
    have hcomp := positiveBuffer_affine_integrableOn measurableSet_Iio hPointI
      (0 : ℝ) (by norm_num : (-1 : ℝ) ≠ 0)
    have hpre : (fun x : ℝ => 0 + -1 * x) ⁻¹' Iio 0 = Ioi 0 := by ext x; simp
    have hio : IntegrableOn (fun t => pout (positiveBufferPoint B i (-t)) ^ 2)
        (Ioi 0) volume := by
      simpa only [hpre, zero_add, neg_one_mul] using hcomp
    change Integrable _ (volume.restrict (Ioi (0 : ℝ))) at hio
    change Integrable _ (volume.restrict (Ici (0 : ℝ)))
    rwa [restrict_Ioi_eq_restrict_Ici] at hio
  refine ⟨hOutI, ?_⟩
  rw [hFinChange, hOutEq]
  apply (le_div_iff₀ hm).mpr
  nlinarith only [hFin, hExt]

end ContinuousFlexibility.Radial
