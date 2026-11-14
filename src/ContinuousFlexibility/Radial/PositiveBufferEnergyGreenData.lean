module

public import ContinuousFlexibility.Radial.PositiveBufferEnergyNormalized
public import ContinuousFlexibility.Radial.BufferGreenEnergy
public import ContinuousFlexibility.Radial.PositiveBufferComparisonGreenRegularity

/-!
# Actual Green columns assembled from the variational endpoint profiles

The finite and exterior minimizers produce a genuine weighted energy
column and an actual L² cutoff source. The source is globally smooth,
compactly supported and absent in both comparison buffers. The column
has unit point-source identity against every energy test, and the
physical norm estimates retain the conormal normalization.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open ContinuousFlexibility.Statements
open scoped Topology ContDiff RealInnerProductSpace InnerProductSpace

theorem positiveBufferGreenKernel_border_product {B : BufferData}
    (hB : BufferHypotheses B) (i : Fin 2) (A : ℝ) (pin pout : ℝ → ℝ) (x : ℝ) :
    B.borderFunction x * positiveBufferGreenKernel B i A pin pout x = 0 := by
  by_cases ht : positiveBufferCoordinate B i x ≤ B.action i + 6
  · have hz := positiveBufferPoint_border_eq_zero hB i ht
    rw [positiveBufferPoint_coordinate hB i x] at hz
    rw [hz, zero_mul]
  · have hz := positiveBufferGreenProfile_zero (pin := pin) (pout := pout)
      (buffer_action_pos hB i) (show B.action i + 4 ≤ positiveBufferCoordinate B i x by
        linarith [lt_of_not_ge ht])
    simp only [positiveBufferGreenKernel, hz, mul_zero]

/-- The source and energy column are constructed from the physical
minimizers, with no abstract Green function supplied as an assumption. -/
theorem positiveBuffer_green_column_of_profiles {B : BufferData}
    (hB : BufferHypotheses B) (i : Fin 2) {C αin αout : ℝ}
    (hC : 0 ≤ C)
    (hcut : ∀ t, |deriv (positiveBufferCutoff (B.action i)) t| ≤ C ∧
      |deriv (deriv (positiveBufferCutoff (B.action i))) t| ≤ C)
    {pin pout : ℝ → ℝ}
    (hpin : ContDiff ℝ ∞ pin) (hpout : ContDiff ℝ ∞ pout)
    (hpin0 : pin (bufferCut B i) = 1) (hpinw : pin (bufferInnerWall B i) = 0)
    (hpout0 : pout (bufferCut B i) = 1)
    (hpoutLp : MemLp pout 2 (volume.restrict (bufferExterior B i)))
    (hEin : IntervalIntegrable (fun x => deriv pin x ^ 2 + B.potential x * pin x ^ 2)
      volume (bufferCut B i) (bufferInnerWall B i))
    (hEout : IntegrableOn (fun x => deriv pout x ^ 2 + B.potential x * pout x ^ 2)
      (bufferExterior B i) volume)
    (hin : ∀ x ∈ radialOpenSpan (bufferCut B i) (bufferInnerWall B i),
      -deriv (deriv pin) x + B.potential x * pin x = 0)
    (hout : ∀ x ∈ bufferExterior B i,
      -deriv (deriv pout) x + B.potential x * pout x = 0)
    (hαin : αin = bufferSign i * deriv pin (bufferCut B i))
    (hαout : αout = -bufferSign i * deriv pout (bufferCut B i))
    (hαinE : αin = ∫ x in min (bufferCut B i) (bufferInnerWall B i)..
      max (bufferCut B i) (bufferInnerWall B i), deriv pin x ^ 2 + B.potential x * pin x ^ 2)
    (hαoutE : αout = ∫ x in bufferExterior B i,
      deriv pout x ^ 2 + B.potential x * pout x ^ 2)
    (hαinlow : B.mass i ≤ αin) (hαoutlow : B.mass i ≤ αout) :
    let u := fun t => pin (positiveBufferPoint B i t)
    let v := fun t => pout (positiveBufferPoint B i (-t))
    let A := αin + αout
    ∃ e : PositiveBufferEnergy B.potential, ∃ f : RadialL2,
      (positiveBufferEnergyCoordinate B.potential 0 e : ℝ → ℝ) =ᵐ[volume]
        positiveBufferGreenKernel B i A u v ∧
      (f : ℝ → ℝ) =ᵐ[volume] positiveBufferGreenError B i A u (deriv u) ∧
      ContDiff ℝ ∞ (positiveBufferGreenError B i A u (deriv u)) ∧
      HasCompactSupport (positiveBufferGreenError B i A u (deriv u)) ∧
      (∀ j : Fin 2, ∀ t : ℝ, t < B.action j + 2 →
        positiveBufferGreenError B i A u (deriv u) (positiveBufferPoint B j t) = 0) ∧
      ⟪B.border, positiveBufferEnergyCoordinate B.potential 0 e⟫_ℝ = 0 ∧
      positiveBufferTraceAt B.potential (bufferCut B i) e = A⁻¹ ∧
      ‖positiveBufferEnergyCoordinate B.potential 0 e‖ ≤ 1 / (B.mass i * sqrt A) ∧
      ‖f‖ ≤ 6 * C * sqrt (B.mass i) * exp (-B.action i) ∧
      ∀ w : PositiveBufferEnergy B.potential,
        positiveBufferEnergyForm B.potential hB.2.2.2.2.1.continuous e w =
          ⟪f, positiveBufferEnergyCoordinate B.potential 0 w⟫_ℝ +
            positiveBufferTraceAt B.potential (bufferCut B i) w := by
  dsimp only
  let u := fun t => pin (positiveBufferPoint B i t)
  let v := fun t => pout (positiveBufferPoint B i (-t))
  let A := αin + αout
  have hm := buffer_mass_pos hB i
  have hA : B.mass i ≤ A := by dsimp [A]; linarith
  have hApos : 0 < A := hm.trans_le hA
  have hu : ContDiff ℝ ∞ u := positiveBuffer_normalized_inner_contDiff i hpin
  have hv : ContDiff ℝ ∞ v := positiveBuffer_normalized_outer_contDiff i hpout
  have hdu := (contDiff_infty_iff_deriv.mp hu).2
  have hu0 : u 0 = 1 := by simpa only [u, positiveBufferPoint_zero] using hpin0
  have hv0 : v 0 = 1 := by simpa only [v, neg_zero, positiveBufferPoint_zero] using hpout0
  have huw : u (B.action i + 6) = 0 := by
    simpa only [u, positiveBufferPoint_innerWall] using hpinw
  have huODE := positiveBuffer_normalized_inner_equation hB i hpin hin
  have hvODE := positiveBuffer_normalized_outer_equation hB i hpout hout
  have hAnorm : A = B.mass i * (-deriv v 0 - deriv u 0) :=
    positiveBuffer_normalized_conormal_sum hB i hpin hpout hαin hαout
  have hnorm := positiveBuffer_normalized_profile_square_mass hB i hpin.continuous
    hpoutLp hEin hEout hαinE hαoutE
  obtain ⟨hvLp, hdvLp, hwvLp⟩ := positiveBuffer_outward_profile_memLp hB i hpout hpoutLp hEout
  have hu' : ∀ t ∈ Ioo 0 (B.action i + 6), HasDerivAt u (deriv u t) t :=
    fun t _ => (hu.differentiable (by simp) t).hasDerivAt
  have hu'' : ∀ t ∈ Ioo 0 (B.action i + 6), HasDerivAt (deriv u)
      ((B.potential (positiveBufferPoint B i t) / B.mass i ^ 2) * u t) t := by
    intro t ht
    convert (hdu.differentiable (by simp) t).hasDerivAt using 1
    linarith [huODE t ht]
  let hsource := positiveBufferGreenError_memLp hB i A hu' hu''
  let f : RadialL2 := hsource.toLp (positiveBufferGreenError B i A u (deriv u))
  have hf : (f : ℝ → ℝ) =ᵐ[volume] positiveBufferGreenError B i A u (deriv u) :=
    MemLp.coeFn_toLp hsource
  obtain ⟨e, he, hidentity⟩ := positiveBufferGreenKernel_exists_energy hB i hApos hu hv hu0 hv0
    hvLp hdvLp hwvLp huODE (fun t ht => hvODE t (mem_Ioi.mpr ht)) hAnorm f hf
  have hKcont : Continuous (positiveBufferGreenKernel B i A u v) := by
    exact continuous_const.mul
      ((positiveBufferGreenProfile_continuous (buffer_action_pos hB i)
        hu.continuous hv.continuous hu0 hv0).comp
        (positiveBufferCoordinate_contDiff B i).continuous)
  let hK := positiveBufferGreenKernel_memLp hB i A hu.continuous hv.continuous hu0 hv0 hnorm.1
  have heLp : positiveBufferEnergyCoordinate B.potential 0 e =
      hK.toLp (positiveBufferGreenKernel B i A u v) := by
    apply Lp.ext
    exact he.trans (MemLp.coeFn_toLp hK).symm
  refine ⟨e, f, he, hf, positiveBufferGreenError_contDiff B i A hu hdu,
    positiveBufferGreenError_hasCompactSupport hB i A u (deriv u),
    ?_, ?_, ?_, ?_, ?_, hidentity⟩
  · intro j t ht
    exact positiveBufferGreenError_zero_on_buffer hB j i A u (deriv u) ht
  · rw [positiveBufferL2_inner_integral]
    have hz : (fun x => B.border x * positiveBufferEnergyCoordinate B.potential 0 e x) =ᵐ[volume]
        (fun _ => 0) := by
      filter_upwards [hB.2.2.2.2.2.2.2.2.1, he] with x hborder hfield
      rw [hborder, hfield]
      exact positiveBufferGreenKernel_border_product hB i A u v x
    rw [integral_congr_ae hz, integral_zero]
  · rw [positiveBufferTraceAt_eq B.potential (bufferCut B i) e hKcont he]
    exact positiveBufferGreenKernel_at_cut B i A hv0
  · rw [heLp]
    exact positiveBufferGreenKernel_energy_norm_bound hB i hApos
      hu.continuous hv.continuous hu0 hv0 hnorm.1 hnorm.2
  · exact positiveBufferGreenError_toLp_norm_bound hB i hA hC hcut hu.continuous.continuousOn
      hu' hu'' (fun t ht => positiveBufferPoint_normalized_potential_lower hB i ht.2.le) hu0 huw

end ContinuousFlexibility.Radial
