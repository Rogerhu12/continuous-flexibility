import ContinuousFlexibility.Radial.ZeroModeEndpointWeight
import ContinuousFlexibility.Radial.ReferenceRadialMeasureComparison

/-!
# Endpoint L2 control from the frozen radial weighted measure

The finite overlap and the partition identity convert the cellwise
endpoint estimate into domination of the inverse-square-distance measure.
This proves ordinary L2 integrability of the endpoint quotient for every
member of the actual radial output space, including its measurability.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real Filter MeasureTheory
open scoped ENNReal
open ContinuousFlexibility.Statements

theorem zeroMode_endpoint_measure_le_weighted
    {D : ReferenceData} {C : ℕ → ℝ}
    (hD : AccumulatingProfileBounds D C)
    {γlo : ℝ} (hγlo : 0 < γlo) (M : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ γ : ℝ, γlo ≤ γ →
      (volume.restrict (radialCore D)).withDensity
        (fun r => ENNReal.ofReal ((min (r - D.a) (D.b - r))⁻¹ ^ 2)) ≤
      ENNReal.ofReal K • referenceRadialWeightedMeasure D γ (-M) := by
  obtain ⟨K, hK, hcell⟩ := zeroMode_endpoint_inv_sq_le_outputWeight hD hγlo M
  obtain ⟨B, hB, hcompare⟩ := referenceRadial_withDensity_le_weighted hD.2.1
  refine ⟨K * B, mul_pos hK hB, ?_⟩
  intro γ hγ
  exact hcompare γ (-M) K
    (fun r => (min (r - D.a) (D.b - r))⁻¹ ^ 2) hK.le
    (fun _ _ => sq_nonneg _) (hcell γ hγ)

/-- Membership in the actual radial output measure gives ordinary L2
control after division by the endpoint distance. -/
theorem zeroMode_memLp_div_endpointDistance
    {D : ReferenceData} {C : ℕ → ℝ}
    (hD : AccumulatingProfileBounds D C)
    {γ M : ℝ} (hγ : 0 < γ) {u : ℝ → ℝ}
    (hu : MemLp u 2 (referenceRadialWeightedMeasure D γ (-M))) :
    MemLp (fun r => u r / min (r - D.a) (D.b - r)) 2
      (volume.restrict (radialCore D)) := by
  obtain ⟨K, _, hK⟩ := zeroMode_endpoint_measure_le_weighted hD hγ M
  let d (r : ℝ) : ℝ := min (r - D.a) (D.b - r)
  let σ (r : ℝ) : ℝ≥0∞ := ENNReal.ofReal ((d r)⁻¹ ^ 2)
  have hd : Measurable d :=
    (measurable_id.sub measurable_const).min (measurable_const.sub measurable_id)
  have hσ : Measurable σ := (hd.inv.pow_const 2).ennreal_ofReal
  have hum : MemLp u 2 ((volume.restrict (radialCore D)).withDensity σ) :=
    hu.of_measure_le_smul ENNReal.ofReal_ne_top (hK γ le_rfl)
  have hσne : ∀ᵐ r ∂volume.restrict (radialCore D), σ r ≠ 0 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    apply ne_of_gt
    apply ENNReal.ofReal_pos.mpr
    apply sq_pos_of_pos
    apply inv_pos.mpr
    exact lt_min (sub_pos.mpr hr.1) (sub_pos.mpr hr.2)
  have hua : AEStronglyMeasurable u (volume.restrict (radialCore D)) :=
    hum.aestronglyMeasurable.mono_ac (withDensity_absolutelyContinuous' hσ.aemeasurable hσne)
  have hquot : AEStronglyMeasurable (fun r => u r / d r)
      (volume.restrict (radialCore D)) :=
    hua.div₀ hd.aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq hquot).mpr
  have hisq := (integrable_withDensity_iff_integrable_smul' hσ
    (ae_of_all _ (fun r => ENNReal.ofReal_lt_top))).mp hum.integrable_sq
  convert hisq using 1
  funext r
  simp only [σ, ENNReal.toReal_ofReal (sq_nonneg _), smul_eq_mul, div_eq_mul_inv]
  ring

end ContinuousFlexibility.Radial
