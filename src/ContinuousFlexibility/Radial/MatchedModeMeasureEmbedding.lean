import ContinuousFlexibility.Radial.ReferenceRadialMeasureComparison
import ContinuousFlexibility.Radial.MatchedModeLocalization
import ContinuousFlexibility.Radial.ZeroModeEndpointWeight
import ContinuousFlexibility.Radial.ModeTestIntegrability

/-!
# Embedding the actual radial weights into the modal Hilbert space

Positive attenuation controls the model measure for every output loss.
For sources, one fixed sufficiently large coefficient exponent controls
the reciprocal density uniformly for every nonnegative attenuation.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal
open ContinuousFlexibility.Statements

def matchedModeInverseDensityMeasure (D : ReferenceData) : Measure ℝ :=
  (volume.restrict (radialCore D)).withDensity
    (fun r => ENNReal.ofReal ((matchingDensity D r)⁻¹))

theorem matchedMode_density_bounded {D : ReferenceData} (hD : IsAccumulatingProfile D) :
    ∃ P : ℝ, 0 < P ∧ ∀ r ∈ radialCore D, matchingDensity D r ≤ P := by
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (matchingDensity_continuousOn hD)
  refine ⟨max B 1, zero_lt_one.trans_le (le_max_right _ _), ?_⟩
  intro r hr
  have hh : |matchingDensity D r| ≤ B := by
    simpa only [Real.norm_eq_abs] using hB r ⟨hr.1.le, hr.2.le⟩
  exact (le_abs_self _).trans (hh.trans (le_max_left _ _))

theorem matchedMode_density_le_outputWeight {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {γlo : ℝ} (hγlo : 0 < γlo) (M : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ γ, γlo ≤ γ →
      ∀ m r, r ∈ D.cells m →
      matchingDensity D r ≤ K * Real.exp
        (2 * (-M) * radialQ (D.cellIndex m) + 2 * γ * radialS (D.cellIndex m)) := by
  obtain ⟨C, hC⟩ := hD
  have hg := hC.1
  have hpart := hC.2.1
  obtain ⟨P, hP, hρ⟩ := matchedMode_density_bounded ⟨C, hC⟩
  obtain ⟨K, hK, hk⟩ := zeroMode_endpoint_inv_sq_le_outputWeight hC hγlo M
  let L : ℝ := D.b - D.a
  have hL : 0 < L := sub_pos.mpr hg.2.1
  refine ⟨P * L ^ 2 * K, by positivity, ?_⟩
  intro γ hγ m r hr
  have hcore := hpart.2.2.2.1 m hr
  let δ : ℝ := min (r - D.a) (D.b - r)
  have hδ : 0 < δ := lt_min (sub_pos.mpr hcore.1) (sub_pos.mpr hcore.2)
  have hδL : δ ≤ L := by
    have hd := min_le_left (r - D.a) (D.b - r)
    dsimp only [δ, L]
    linarith [hcore.2]
  have hsq : δ ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ hδ.le hδL 2
  have hone : 1 ≤ L ^ 2 * δ⁻¹ ^ 2 := by
    have hh := mul_le_mul_of_nonneg_right hsq (sq_nonneg δ⁻¹)
    have hc : δ ^ 2 * δ⁻¹ ^ 2 = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ hδ.ne', one_pow]
    rwa [hc] at hh
  calc
    matchingDensity D r ≤ P := hρ r hcore
    _ ≤ (P * L ^ 2) * δ⁻¹ ^ 2 := by nlinarith [mul_le_mul_of_nonneg_left hone hP.le]
    _ ≤ (P * L ^ 2) * (K * Real.exp
        (2 * (-M) * radialQ (D.cellIndex m) + 2 * γ * radialS (D.cellIndex m))) :=
      mul_le_mul_of_nonneg_left (hk γ hγ m r hr) (by positivity)
    _ = _ := by ring

/-- Uniform in all attenuation exponents above one positive lower bound. -/
theorem matchedMode_measure_le_outputWeighted {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {γlo : ℝ} (hγlo : 0 < γlo) (M : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ γ, γlo ≤ γ →
      radialHilbertMeasure D ≤
        ENNReal.ofReal K • referenceRadialWeightedMeasure D γ (-M) := by
  have hp : RadialPartition D := hD.choose_spec.2.1
  obtain ⟨B, hB, hcmp⟩ := referenceRadial_withDensity_le_weighted hp
  obtain ⟨K, hK, hcell⟩ := matchedMode_density_le_outputWeight hD hγlo M
  refine ⟨K * B, mul_pos hK hB, ?_⟩
  intro γ hγ
  exact hcmp γ (-M) K (matchingDensity D) hK.le
    (fun r hr => (matchingDensity_pos hD hr).le) (hcell γ hγ)

/-- One lower bound for M suffices for every source and every γ ≥ 0. -/
theorem matchedMode_inverseDensity_le_sourceWeighted {D : ReferenceData}
    (hD : IsAccumulatingProfile D) :
    ∃ Mmin K : ℝ, 0 < Mmin ∧ 0 < K ∧ ∀ M, Mmin ≤ M → ∀ γ, 0 ≤ γ →
      matchedModeInverseDensityMeasure D ≤
        ENNReal.ofReal K • referenceRadialWeightedMeasure D γ M := by
  have hp : RadialPartition D := hD.choose_spec.2.1
  obtain ⟨A, hA, hρ⟩ := matchedDensity_inv_coefficient_bound hD
  obtain ⟨B, hB, hcmp⟩ := referenceRadial_withDensity_le_weighted hp
  refine ⟨A, A * B, hA, mul_pos hA hB, ?_⟩
  intro M hM γ hγ
  apply hcmp γ M A (fun r => (matchingDensity D r)⁻¹) hA.le
    (fun r hr => (inv_pos.mpr (matchingDensity_pos hD hr)).le)
  intro m r hr
  have hh := hρ m r hr
  rw [radialE, ← Real.exp_mul] at hh
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ hA.le
  apply Real.exp_le_exp.mpr
  have hq := radialQ_nonneg (D.cellIndex m)
  have hS : 0 ≤ radialS (D.cellIndex m) := by unfold radialS; positivity
  have hAM : A ≤ 2 * M := by linarith
  have hcoef := mul_le_mul_of_nonneg_right hAM hq
  nlinarith [mul_nonneg hγ hS]

theorem matchedModeInverseDensity_absolutelyContinuous {D : ReferenceData}
    (hD : IsAccumulatingProfile D) :
    volume.restrict (radialCore D) ≪ matchedModeInverseDensityMeasure D := by
  apply withDensity_absolutelyContinuous'
    ((matchingDensity_measurable hD).inv.ennreal_ofReal.aemeasurable)
  filter_upwards [ae_restrict_mem (show MeasurableSet (radialCore D) from measurableSet_Ioo)]
    with r hr
  exact ne_of_gt (ENNReal.ofReal_pos.mpr (inv_pos.mpr (matchingDensity_pos hD hr)))

/-- The reciprocal-density source norm is exactly the norm needed after
division by the model density. -/
theorem matchedMode_source_memLp_of_inverseDensity {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {f : ℝ → ℝ}
    (hf : MemLp f 2 (matchedModeInverseDensityMeasure D)) :
    MemLp (fun r => -f r / matchingDensity D r) 2 (radialHilbertMeasure D) := by
  have hfm : AEStronglyMeasurable f (radialHilbertMeasure D) :=
    (hf.aestronglyMeasurable.mono_ac
      (matchedModeInverseDensity_absolutelyContinuous hD)).mono_ac
      (withDensity_absolutelyContinuous _ _)
  have hm : AEStronglyMeasurable (fun r => -f r / matchingDensity D r)
      (radialHilbertMeasure D) :=
    hfm.neg.div₀ (matchingDensity_measurable hD).aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq hm).mpr
  apply (matchingDensity_integrable_iff hD _).mpr
  have hi₀ := hf.integrable_sq
  change Integrable (fun r => f r ^ 2)
    ((volume.restrict (radialCore D)).withDensity
      (fun r => ENNReal.ofReal ((matchingDensity D r)⁻¹))) at hi₀
  have hi := (integrable_withDensity_iff_integrable_smul'
    (matchingDensity_measurable hD).inv.ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))).mp hi₀
  apply hi.congr
  filter_upwards [ae_restrict_mem (show MeasurableSet (radialCore D) from measurableSet_Ioo)]
    with r hr
  have hρ := matchingDensity_pos hD hr
  simp only [Pi.inv_apply, ENNReal.toReal_ofReal (inv_nonneg.mpr hρ.le), smul_eq_mul]
  field_simp [hρ.ne']
  <;> ring

theorem matchedMode_memLp_of_outputWeighted {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {γ M : ℝ} (hγ : 0 < γ)
    {f : ℝ → ℝ} (hf : MemLp f 2 (referenceRadialWeightedMeasure D γ (-M))) :
    MemLp f 2 (radialHilbertMeasure D) := by
  obtain ⟨K, _, hK⟩ := matchedMode_measure_le_outputWeighted hD hγ M
  exact hf.of_measure_le_smul (by simp) (hK γ le_rfl)

theorem exists_matchedMode_source_memLp {D : ReferenceData}
    (hD : IsAccumulatingProfile D) :
    ∃ Mmin : ℝ, 0 < Mmin ∧ ∀ M, Mmin ≤ M → ∀ γ, 0 ≤ γ →
      ∀ f : ℝ → ℝ, MemLp f 2 (referenceRadialWeightedMeasure D γ M) →
        MemLp (fun r => -f r / matchingDensity D r) 2 (radialHilbertMeasure D) := by
  obtain ⟨Mmin, K, hMmin, _, hK⟩ := matchedMode_inverseDensity_le_sourceWeighted hD
  refine ⟨Mmin, hMmin, ?_⟩
  intro M hM γ hγ f hf
  exact matchedMode_source_memLp_of_inverseDensity hD
    (hf.of_measure_le_smul (by simp) (hK M hM γ hγ))

end ContinuousFlexibility.Radial
