module

public import ContinuousFlexibility.Radial.R11bAngularL2Bridge
public import ContinuousFlexibility.Radial.R11bLpConvergence

/-!
# Returning normalized angular L² convergence to physical measure

Both sides use the same raw representatives. The physical measure is exactly
two pi times the normalized angular product measure.
-/

@[expose] public section

namespace ContinuousFlexibility.Radial

noncomputable section

open Set MeasureTheory Filter
open scoped Topology
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

theorem r11b_physicalMeasure_eq_smul_radial_angularMean (D : ReferenceData) :
    radialPhysicalMeasure D =
      ENNReal.ofReal (2 * Real.pi) •
        ((volume.restrict (radialCore D)).prod angularMeanMeasure) := by
  have hcancel : (2 * Real.pi) * (1 / (2 * Real.pi)) = 1 := by
    rw [mul_comm]
    exact div_mul_cancel₀ 1 (by positivity)
  rw [r11b_radial_prod_angularMeanMeasure, smul_smul,
    ← ENNReal.ofReal_mul (by positivity), hcancel, ENNReal.ofReal_one, one_smul]

theorem r11b_memLp_of_radial_angularMean {D : ReferenceData} {f : PolarPoint → ℝ}
    (hf : MemLp f 2 ((volume.restrict (radialCore D)).prod angularMeanMeasure)) :
    MemLp f 2 (radialPhysicalMeasure D) := by
  rw [r11b_physicalMeasure_eq_smul_radial_angularMean]
  exact hf.smul_measure ENNReal.ofReal_ne_top

theorem r11b_ae_of_radial_angularMean {D : ReferenceData} {β : Type*}
    {f g : PolarPoint → β}
    (hfg : f =ᵐ[(volume.restrict (radialCore D)).prod angularMeanMeasure] g) :
    f =ᵐ[radialPhysicalMeasure D] g := by
  rw [r11b_physicalMeasure_eq_smul_radial_angularMean]
  exact Measure.ae_smul_measure hfg _

theorem r11b_integral_sq_physical_eq (D : ReferenceData) (f : PolarPoint → ℝ) :
    (∫ z, f z ^ 2 ∂radialPhysicalMeasure D) =
      (2 * Real.pi) * ∫ z, f z ^ 2
        ∂(volume.restrict (radialCore D)).prod angularMeanMeasure := by
  rw [r11b_physicalMeasure_eq_smul_radial_angularMean, integral_smul_measure,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * Real.pi), smul_eq_mul]

/-- Normalized angular product convergence gives physical L² convergence
of the identical raw representatives. -/
theorem r11b_tendsto_toLp_physical_of_radial_angularMean
    {ι : Type*} {l : Filter ι} {D : ReferenceData}
    {f : ι → PolarPoint → ℝ} {g : PolarPoint → ℝ}
    (hf : ∀ i, MemLp (f i) 2
      ((volume.restrict (radialCore D)).prod angularMeanMeasure))
    (hg : MemLp g 2 ((volume.restrict (radialCore D)).prod angularMeanMeasure))
    (hlim : Tendsto (fun i => (hf i).toLp (f i)) l (𝓝 (hg.toLp g))) :
    Tendsto (fun i => (r11b_memLp_of_radial_angularMean (hf i)).toLp (f i)) l
      (𝓝 ((r11b_memLp_of_radial_angularMean hg).toLp g)) := by
  apply (r11b_tendsto_toLp_iff_integral_sq_sub
    (fun i => r11b_memLp_of_radial_angularMean (hf i))
    (r11b_memLp_of_radial_angularMean hg)).mpr
  have hres := (r11b_tendsto_toLp_iff_integral_sq_sub hf hg).mp hlim
  simp_rw [r11b_integral_sq_physical_eq]
  simpa only [mul_zero] using hres.const_mul (2 * Real.pi)

end

end ContinuousFlexibility.Radial
