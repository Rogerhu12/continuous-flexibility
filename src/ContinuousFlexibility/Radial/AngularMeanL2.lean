import ContinuousFlexibility.Radial.FourierOrthogonality
import Mathlib.MeasureTheory.Function.L2Space

/-!
# The actual normalized angular integral as an L² inner product

The measure is the ordinary interval measure multiplied by 1/(2π).
This identifies the existing angularAverage and angularPairing with genuine
integrals and L² inner products, so finite Hilbert-space estimates apply
directly to the manuscript's coefficient normalization.
-/

namespace ContinuousFlexibility.Radial

noncomputable section

open Set MeasureTheory
open scoped RealInnerProductSpace

def angularMeanMeasure : Measure ℝ :=
  ENNReal.ofReal (1 / (2 * Real.pi)) •
    volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))

theorem angularAverage_eq_integral_angularMeanMeasure (f : ℝ → ℝ) :
    angularAverage f = ∫ θ, f θ ∂angularMeanMeasure := by
  unfold angularAverage angularMeanMeasure
  rw [integral_smul_measure, ENNReal.toReal_ofReal (by positivity)]
  rw [intervalIntegral.integral_of_le (by positivity)]
  rfl

theorem memLp_angularMeanMeasure {f : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))) :
    MemLp f 2 angularMeanMeasure :=
  hf.smul_measure ENNReal.ofReal_ne_top

/-- Continuity is only used on the compact closure of one angular period. -/
theorem angularInterval_memLp_of_continuous {f : ℝ → ℝ} (hf : Continuous f) :
    MemLp f 2 (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))) := by
  have hK : IsCompact (Icc (0 : ℝ) (2 * Real.pi)) := isCompact_Icc
  letI : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))) :=
    ⟨by
      rw [Measure.restrict_apply_univ]
      exact (measure_mono Ioc_subset_Icc_self).trans_lt hK.measure_lt_top⟩
  obtain ⟨M, hM⟩ := hK.bddAbove_image hf.norm.continuousOn
  apply MemLp.of_bound hf.aestronglyMeasurable M
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
  exact hM ⟨θ, Ioc_subset_Icc_self hθ, rfl⟩

theorem angularMean_inner_toLp {f g : ℝ → ℝ}
    (hf : MemLp f 2 angularMeanMeasure) (hg : MemLp g 2 angularMeanMeasure) :
    ⟪hf.toLp f, hg.toLp g⟫_ℝ = angularPairing f g := by
  calc
    _ = ∫ θ, f θ * g θ ∂angularMeanMeasure := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with θ hθf hθg
      rw [Real.inner_apply, hθf, hθg]
    _ = angularPairing f g :=
      (angularAverage_eq_integral_angularMeanMeasure (fun θ => f θ * g θ)).symm

theorem angularMean_norm_sq_toLp {f : ℝ → ℝ} (hf : MemLp f 2 angularMeanMeasure) :
    ‖hf.toLp f‖ ^ 2 = angularAverage (fun θ => f θ ^ 2) := by
  calc
    _ = ⟪hf.toLp f, hf.toLp f⟫_ℝ := (real_inner_self_eq_norm_sq _).symm
    _ = angularPairing f f := angularMean_inner_toLp hf hf
    _ = angularAverage (fun θ => f θ ^ 2) := by
      simp only [angularPairing, pow_two]

/-- Both entries of the angular pairing may be read directly in the normalized L² space. -/
theorem angularPairing_eq_inner_angularMean_toLp {f g : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))))
    (hg : MemLp g 2 (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))) :
    angularPairing f g =
      ⟪(memLp_angularMeanMeasure hf).toLp f, (memLp_angularMeanMeasure hg).toLp g⟫_ℝ :=
  (angularMean_inner_toLp (memLp_angularMeanMeasure hf) (memLp_angularMeanMeasure hg)).symm

end

end ContinuousFlexibility.Radial
