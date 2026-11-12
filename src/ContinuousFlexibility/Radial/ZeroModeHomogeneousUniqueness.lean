import ContinuousFlexibility.Radial.ZeroModeEndpointExclusion
import ContinuousFlexibility.Radial.ZeroModeResistanceGrowth

/-!
# Uniqueness of the homogeneous zero channel in the actual output space

A homogeneous weak representative is a constant plus a constant times
the actual resistance primitive. The latter diverges at the right
endpoint. Both possibilities are excluded by the radial output norm,
after using the actual border's vanishing near that endpoint.

The left endpoint constant in `OutputRealization` is retained throughout;
the proof never assumes that the uncorrected height belongs to the
weighted L2 space.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real Filter MeasureTheory
open scoped Topology ENNReal
open ContinuousFlexibility.Statements

theorem zeroMode_affine_resistance_coefficients_eq_zero
    {D : ReferenceData} {C : ℕ → ℝ}
    (hD : AccumulatingProfileBounds D C) (hborder : RadialTrueBorder D)
    {γ M : ℝ} (hγ : 0 < γ) {c : ℝ} (hc : c ∈ radialCore D)
    {A B aL : ℝ}
    (hu : MemLp (fun r => A + B * (∫ s in c..r, (D.w s)⁻¹) -
        aL * D.chiLeft r) 2 (referenceRadialWeightedMeasure D γ (-M))) :
    A = 0 ∧ B = 0 := by
  obtain ⟨ε, hε, _, hχ⟩ := hborder.2.2.2.2.2
  let l₀ : ℝ := max c (D.b - ε)
  have hl₀a : D.a < l₀ := hc.1.trans_le (le_max_left _ _)
  have hl₀b : l₀ < D.b := max_lt hc.2 (by linarith)
  have hχtail (r : ℝ) (hr : r ∈ Ioo l₀ D.b) : D.chiLeft r = 0 :=
    hχ r ⟨(le_max_right c (D.b - ε)).trans_lt hr.1, hr.2⟩
  let R (r : ℝ) : ℝ := ∫ s in c..r, (D.w s)⁻¹
  have hR : Tendsto R (𝓝[<] D.b) atTop := zeroMode_resistance_tendsto_atTop hD.1 hc
  have hB : B = 0 := by
    by_contra hB
    have hBp : 0 < |B| := abs_pos.mpr hB
    have hev : ∀ᶠ r in 𝓝[<] D.b, 1 ≤ |A + B * R r| := by
      filter_upwards [hR.eventually (eventually_ge_atTop ((|A| + 1) / |B|))] with r hr
      have hR0 : 0 ≤ R r := (div_nonneg (by positivity) hBp.le).trans hr
      have hh := (div_le_iff₀ hBp).mp hr
      have ht := abs_sub (A + B * R r) A
      rw [show A + B * R r - A = B * R r by ring, abs_mul, abs_of_nonneg hR0] at ht
      nlinarith only [hh, ht]
    obtain ⟨l, hl, hcut⟩ :=
      (mem_nhdsLT_iff_exists_mem_Ico_Ioo_subset hl₀b).mp hev
    have hlow : ∀ᵐ r ∂volume.restrict (Ioo l D.b),
        1 ≤ |A + B * R r - aL * D.chiLeft r| := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
      rw [hχtail r ⟨hl.1.trans_lt hr.1, hr.2⟩, mul_zero, sub_zero]
      exact hcut hr
    exact zeroMode_right_lower_bound_impossible hD hγ hu
      (hl₀a.trans_le hl.1) hl.2 (by norm_num) hlow
  refine ⟨?_, hB⟩
  by_contra hA
  have hu₀ : MemLp (fun r => A - aL * D.chiLeft r) 2
      (referenceRadialWeightedMeasure D γ (-M)) := by
    simpa only [hB, zero_mul, add_zero] using hu
  have hlow : ∀ᵐ r ∂volume.restrict (Ioo l₀ D.b), |A| ≤ |A - aL * D.chiLeft r| := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    rw [hχtail r hr, mul_zero, sub_zero]
  exact zeroMode_right_lower_bound_impossible hD hγ hu₀ hl₀a hl₀b (abs_pos.mpr hA) hlow

/-- The same conclusion for an arbitrary almost-everywhere representative.
This is the form used after local weak ODE regularity. -/
theorem zeroMode_homogeneous_representative_eq_zero
    {D : ReferenceData} {C : ℕ → ℝ}
    (hD : AccumulatingProfileBounds D C) (hborder : RadialTrueBorder D)
    {γ M : ℝ} (hγ : 0 < γ) {c : ℝ} (hc : c ∈ radialCore D)
    {u : ℝ → ℝ} {A B aL : ℝ}
    (hu : MemLp (fun r => u r - aL * D.chiLeft r) 2
      (referenceRadialWeightedMeasure D γ (-M)))
    (hrep : u =ᵐ[volume.restrict (radialCore D)]
      (fun r => A + B * (∫ s in c..r, (D.w s)⁻¹))) :
    A = 0 ∧ B = 0 ∧ u =ᵐ[volume.restrict (radialCore D)] (fun _ => (0 : ℝ)) := by
  have hrem :
      (fun r => u r - aL * D.chiLeft r) =ᵐ[volume.restrict (radialCore D)]
        (fun r => A + B * (∫ s in c..r, (D.w s)⁻¹) - aL * D.chiLeft r) :=
    hrep.mono (fun r h => congrArg (fun z => z - aL * D.chiLeft r) h)
  have hremw :
      (fun r => u r - aL * D.chiLeft r) =ᵐ[referenceRadialWeightedMeasure D γ (-M)]
        (fun r => A + B * (∫ s in c..r, (D.w s)⁻¹) - aL * D.chiLeft r) := by
    exact hrem.filter_mono
      (referenceRadialWeightedMeasure_absolutelyContinuous D γ (-M)).ae_le
  obtain ⟨hA, hB⟩ := zeroMode_affine_resistance_coefficients_eq_zero hD hborder hγ hc
    ((memLp_congr_ae hremw).mp hu)
  refine ⟨hA, hB, ?_⟩
  simpa only [hA, hB, zero_mul, zero_add] using hrep

end ContinuousFlexibility.Radial
