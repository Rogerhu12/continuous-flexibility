import ContinuousFlexibility.Radial.PositiveBufferComparisonCutoffL2
import ContinuousFlexibility.Radial.PositiveBufferComparisonCoordinates
import ContinuousFlexibility.Radial.PositiveBufferComparisonScaling
import ContinuousFlexibility.Radial.BufferCutGlue

/-!
# The normalized cutoff Green profile

The exterior profile is written in the outward coordinate, and the
interior profile in the inward coordinate.  The common cut is zero.
The profile uses the same measurable gluing operation as the weak
derivative and point-source identities.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter Real MeasureTheory
open ContinuousFlexibility.Statements
open scoped Topology

def positiveBufferGreenProfile (σ : ℝ) (pin pout : ℝ → ℝ) : ℝ → ℝ :=
  bufferCutGlue 0 (fun t => pout (-t)) (fun t => positiveBufferCutoff σ t * pin t)

theorem positiveBufferGreenProfile_cut {σ : ℝ} {pin pout : ℝ → ℝ}
    (hpout : pout 0 = 1) : positiveBufferGreenProfile σ pin pout 0 = 1 := by
  simp only [positiveBufferGreenProfile, bufferCutGlue, le_refl, ite_true, neg_zero, hpout]

theorem positiveBufferGreenProfile_continuous {σ : ℝ} {pin pout : ℝ → ℝ}
    (hσ : 0 < σ) (hpin : Continuous pin) (hpout : Continuous pout)
    (hpin0 : pin 0 = 1) (hpout0 : pout 0 = 1) :
    Continuous (positiveBufferGreenProfile σ pin pout) := by
  change Continuous (fun t : ℝ =>
    if t ≤ 0 then pout (-t) else positiveBufferCutoff σ t * pin t)
  apply (hpout.comp continuous_neg).if_le
    ((positiveBufferCutoff_contDiff σ).continuous.mul hpin) continuous_id continuous_const
  intro t ht
  change t = 0 at ht
  subst t
  change pout (-0) = positiveBufferCutoff σ 0 * pin 0
  rw [neg_zero, hpout0, positiveBufferCutoff_one (by linarith), hpin0, mul_one]

theorem positiveBufferGreenProfile_zero {σ t : ℝ} {pin pout : ℝ → ℝ}
    (hσ : 0 < σ) (ht : σ + 4 ≤ t) :
    positiveBufferGreenProfile σ pin pout t = 0 := by
  have ht0 : 0 < t := by linarith
  rw [positiveBufferGreenProfile, bufferCutGlue_of_lt _ _ _ ht0,
    positiveBufferCutoff_zero ht, zero_mul]

/-- The two square-integrable pieces dominate the cutoff profile. -/
theorem positiveBufferGreenProfile_square_majorant {σ : ℝ} (hσ : 0 < σ)
    (pin pout : ℝ → ℝ) (t : ℝ) :
    positiveBufferGreenProfile σ pin pout t ^ 2 ≤
      (Iic (0 : ℝ)).indicator (fun x => pout (-x) ^ 2) t +
        (Icc 0 (σ + 6)).indicator (fun x => pin x ^ 2) t := by
  by_cases ht : t ≤ 0
  · rw [positiveBufferGreenProfile, bufferCutGlue_of_le _ _ _ ht,
      indicator_of_mem (show t ∈ Iic (0 : ℝ) from ht)]
    by_cases hti : t ∈ Icc 0 (σ + 6)
    · rw [indicator_of_mem hti]
      linarith [sq_nonneg (pin t)]
    · rw [indicator_of_notMem hti, add_zero]
  · have htpos : 0 < t := lt_of_not_ge ht
    rw [positiveBufferGreenProfile, bufferCutGlue_of_lt _ _ _ htpos,
      indicator_of_notMem (show t ∉ Iic (0 : ℝ) from ht), zero_add]
    by_cases htw : t ≤ σ + 6
    · have hti : t ∈ Icc 0 (σ + 6) := ⟨htpos.le, htw⟩
      rw [indicator_of_mem hti, mul_pow]
      have hχ := positiveBufferCutoff_bounds σ t
      have hχsq : positiveBufferCutoff σ t ^ 2 ≤ 1 := by nlinarith
      exact mul_le_of_le_one_left (sq_nonneg (pin t)) hχsq
    · rw [positiveBufferCutoff_zero (by linarith), zero_mul, zero_pow (by norm_num),
        indicator_of_notMem (show t ∉ Icc 0 (σ + 6) from fun h => htw h.2)] <;> exact le_rfl

theorem positiveBufferGreenProfile_majorant_integrable {σ : ℝ} {pin pout : ℝ → ℝ}
    (hpin : Continuous pin)
    (hpout : IntegrableOn (fun t => pout t ^ 2) (Ici 0) volume) :
    Integrable (fun t : ℝ =>
      (Iic (0 : ℝ)).indicator (fun x => pout (-x) ^ 2) t +
        (Icc 0 (σ + 6)).indicator (fun x => pin x ^ 2) t) volume := by
  have hleft0 : Integrable ((Ici (0 : ℝ)).indicator (fun t => pout t ^ 2)) volume :=
    (integrable_indicator_iff measurableSet_Ici).2 hpout
  have hleft : Integrable ((Iic (0 : ℝ)).indicator (fun t => pout (-t) ^ 2)) volume := by
    apply hleft0.comp_neg.congr
    filter_upwards [] with t
    change (Ici (0 : ℝ)).indicator (fun x => pout x ^ 2) (-t) =
      (Iic (0 : ℝ)).indicator (fun x => pout (-x) ^ 2) t
    simp only [indicator_apply, mem_Ici, mem_Iic, neg_nonneg]
  have hright : Integrable ((Icc 0 (σ + 6)).indicator (fun t => pin t ^ 2)) volume :=
    (integrable_indicator_iff measurableSet_Icc).2 (hpin.pow 2).integrableOn_Icc
  exact hleft.add hright

theorem positiveBufferGreenProfile_memLp {σ : ℝ} {pin pout : ℝ → ℝ}
    (hσ : 0 < σ) (hpin : Continuous pin) (hpout : Continuous pout)
    (hpin0 : pin 0 = 1) (hpout0 : pout 0 = 1)
    (hpoutI : IntegrableOn (fun t => pout t ^ 2) (Ici 0) volume) :
    MemLp (positiveBufferGreenProfile σ pin pout) 2 volume := by
  have hc := positiveBufferGreenProfile_continuous hσ hpin hpout hpin0 hpout0
  apply (memLp_two_iff_integrable_sq hc.aestronglyMeasurable).2
  apply (positiveBufferGreenProfile_majorant_integrable (σ := σ) hpin hpoutI).mono'
    (hc.pow 2).aestronglyMeasurable
  filter_upwards [] with t
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact positiveBufferGreenProfile_square_majorant hσ pin pout t

/-- The raw cutoff profile costs at most the sum of the two genuine
square-mass integrals.  Positivity converts these integrals to energies
in the later physical normalization. -/
theorem positiveBufferGreenProfile_toLp_norm_sq_le {σ : ℝ} {pin pout : ℝ → ℝ}
    (hσ : 0 < σ) (hpin : Continuous pin) (hpout : Continuous pout)
    (hpin0 : pin 0 = 1) (hpout0 : pout 0 = 1)
    (hpoutI : IntegrableOn (fun t => pout t ^ 2) (Ici 0) volume) :
    ‖(positiveBufferGreenProfile_memLp hσ hpin hpout hpin0 hpout0 hpoutI).toLp
      (positiveBufferGreenProfile σ pin pout)‖ ^ 2 ≤
      (∫ t in Icc 0 (σ + 6), pin t ^ 2) + ∫ t in Ici 0, pout t ^ 2 := by
  rw [positiveBuffer_toLp_norm_sq]
  have hmajor := positiveBufferGreenProfile_majorant_integrable (σ := σ) hpin hpoutI
  have hle := integral_mono_ae
    (positiveBufferGreenProfile_memLp hσ hpin hpout hpin0 hpout0 hpoutI).integrable_sq
    hmajor (Eventually.of_forall (positiveBufferGreenProfile_square_majorant hσ pin pout))
  have hleft0 : Integrable ((Ici (0 : ℝ)).indicator (fun t => pout t ^ 2)) volume :=
    (integrable_indicator_iff measurableSet_Ici).2 hpoutI
  have hleft : Integrable ((Iic (0 : ℝ)).indicator (fun t => pout (-t) ^ 2)) volume := by
    apply hleft0.comp_neg.congr
    filter_upwards [] with t
    change (Ici (0 : ℝ)).indicator (fun x => pout x ^ 2) (-t) =
      (Iic (0 : ℝ)).indicator (fun x => pout (-x) ^ 2) t
    simp only [indicator_apply, mem_Ici, mem_Iic, neg_nonneg]
  have hright : Integrable ((Icc 0 (σ + 6)).indicator (fun t => pin t ^ 2)) volume :=
    (integrable_indicator_iff measurableSet_Icc).2 (hpin.pow 2).integrableOn_Icc
  rw [integral_add hleft hright, integral_indicator measurableSet_Iic,
    integral_indicator measurableSet_Icc, integral_comp_neg_Iic, neg_zero,
    ← integral_Ici_eq_integral_Ioi] at hle
  simpa only [add_comm] using hle

/-- The actual Green kernel in the physical variable, with point-source
normalization `A = alphaIn + alphaOut`. -/
def positiveBufferGreenKernel (B : BufferData) (i : Fin 2) (A : ℝ)
    (pin pout : ℝ → ℝ) (x : ℝ) : ℝ :=
  A⁻¹ * positiveBufferGreenProfile (B.action i) pin pout (positiveBufferCoordinate B i x)

theorem positiveBufferGreenKernel_at_cut (B : BufferData) (i : Fin 2) (A : ℝ)
    {pin pout : ℝ → ℝ} (hpout0 : pout 0 = 1) :
    positiveBufferGreenKernel B i A pin pout (bufferCut B i) = A⁻¹ := by
  rw [positiveBufferGreenKernel, positiveBufferCoordinate_cut,
    positiveBufferGreenProfile_cut hpout0, mul_one]

theorem positiveBufferGreenKernel_memLp {B : BufferData} (hB : BufferHypotheses B)
    (i : Fin 2) (A : ℝ) {pin pout : ℝ → ℝ}
    (hpin : Continuous pin) (hpout : Continuous pout)
    (hpin0 : pin 0 = 1) (hpout0 : pout 0 = 1)
    (hpoutI : IntegrableOn (fun t => pout t ^ 2) (Ici 0) volume) :
    MemLp (positiveBufferGreenKernel B i A pin pout) 2 volume := by
  unfold positiveBufferGreenKernel
  have hσ := buffer_action_pos hB i
  have hc := positiveBufferGreenProfile_continuous hσ hpin hpout hpin0 hpout0
  have hf := positiveBufferGreenProfile_memLp hσ hpin hpout hpin0 hpout0 hpoutI
  simpa only [positiveBufferGreenKernel, ← positiveBufferCoordinate_affine] using
    (positiveBuffer_affine_memLp_two hc hf
      (bufferSign i * B.mass i * bufferCut B i)
      (positiveBufferCoordinate_slope_ne_zero hB i)).const_mul A⁻¹

theorem positiveBufferGreenKernel_toLp_norm {B : BufferData} (hB : BufferHypotheses B)
    (i : Fin 2) (A : ℝ) {pin pout : ℝ → ℝ}
    (hpin : Continuous pin) (hpout : Continuous pout)
    (hpin0 : pin 0 = 1) (hpout0 : pout 0 = 1)
    (hpoutI : IntegrableOn (fun t => pout t ^ 2) (Ici 0) volume) :
    ‖(positiveBufferGreenKernel_memLp hB i A hpin hpout hpin0 hpout0 hpoutI).toLp
      (positiveBufferGreenKernel B i A pin pout)‖ =
      |A⁻¹| * sqrt ((B.mass i)⁻¹) *
        ‖(positiveBufferGreenProfile_memLp (buffer_action_pos hB i)
          hpin hpout hpin0 hpout0 hpoutI).toLp
          (positiveBufferGreenProfile (B.action i) pin pout)‖ := by
  unfold positiveBufferGreenKernel
  simpa only [ ← positiveBufferCoordinate_affine,
    positiveBufferCoordinate_abs_slope hB i] using
    positiveBuffer_affine_scaled_toLp_norm
      (positiveBufferGreenProfile_continuous (buffer_action_pos hB i) hpin hpout hpin0 hpout0)
      (positiveBufferGreenProfile_memLp (buffer_action_pos hB i)
        hpin hpout hpin0 hpout0 hpoutI)
      (bufferSign i * B.mass i * bufferCut B i) A⁻¹
      (positiveBufferCoordinate_slope_ne_zero hB i)

/-- Positivity of the original energy gives the sharp normalization
`1 / (mass * sqrt A)` for the actual Green kernel. -/
theorem positiveBufferGreenKernel_energy_norm_bound {B : BufferData}
    (hB : BufferHypotheses B) (i : Fin 2) {A : ℝ} (hA : 0 < A)
    {pin pout : ℝ → ℝ} (hpin : Continuous pin) (hpout : Continuous pout)
    (hpin0 : pin 0 = 1) (hpout0 : pout 0 = 1)
    (hpoutI : IntegrableOn (fun t => pout t ^ 2) (Ici 0) volume)
    (henergy : (∫ t in Icc 0 (B.action i + 6), pin t ^ 2) +
      (∫ t in Ici 0, pout t ^ 2) ≤ A / B.mass i) :
    ‖(positiveBufferGreenKernel_memLp hB i A hpin hpout hpin0 hpout0 hpoutI).toLp
      (positiveBufferGreenKernel B i A pin pout)‖ ≤ 1 / (B.mass i * sqrt A) := by
  have hm := buffer_mass_pos hB i
  have hraw := (positiveBufferGreenProfile_toLp_norm_sq_le (buffer_action_pos hB i)
    hpin hpout hpin0 hpout0 hpoutI).trans henergy
  apply (sq_le_sq₀ (norm_nonneg _)
    (one_div_nonneg.mpr (mul_nonneg hm.le (sqrt_nonneg _)))).mp
  rw [positiveBufferGreenKernel_toLp_norm hB i A hpin hpout hpin0 hpout0 hpoutI,
    abs_of_nonneg (inv_nonneg.mpr hA.le), mul_pow, mul_pow,
    sq_sqrt (inv_nonneg.mpr hm.le), div_pow, one_pow, mul_pow, sq_sqrt hA.le]
  calc
    _ ≤ A⁻¹ ^ 2 * (B.mass i)⁻¹ * (A / B.mass i) :=
      mul_le_mul_of_nonneg_left hraw (by positivity)
    _ = 1 / (B.mass i ^ 2 * A) := by
      field_simp [hm.ne', hA.ne']
      <;> ring

theorem positiveBufferGreenKernel_mass_norm_bound {B : BufferData}
    (hB : BufferHypotheses B) (i : Fin 2) {A : ℝ} (hA : B.mass i ≤ A)
    {pin pout : ℝ → ℝ} (hpin : Continuous pin) (hpout : Continuous pout)
    (hpin0 : pin 0 = 1) (hpout0 : pout 0 = 1)
    (hpoutI : IntegrableOn (fun t => pout t ^ 2) (Ici 0) volume)
    (henergy : (∫ t in Icc 0 (B.action i + 6), pin t ^ 2) +
      (∫ t in Ici 0, pout t ^ 2) ≤ A / B.mass i) :
    ‖(positiveBufferGreenKernel_memLp hB i A hpin hpout hpin0 hpout0 hpoutI).toLp
      (positiveBufferGreenKernel B i A pin pout)‖ ≤ 1 / (B.mass i * sqrt (B.mass i)) := by
  have hm := buffer_mass_pos hB i
  apply (positiveBufferGreenKernel_energy_norm_bound hB i (hm.trans_le hA)
    hpin hpout hpin0 hpout0 hpoutI henergy).trans
  exact one_div_le_one_div_of_le (mul_pos hm (sqrt_pos.mpr hm))
    (mul_le_mul_of_nonneg_left (sqrt_le_sqrt hA) hm.le)

end ContinuousFlexibility.Radial
