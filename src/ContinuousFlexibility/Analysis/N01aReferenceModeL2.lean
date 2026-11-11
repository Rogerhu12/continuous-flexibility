import ContinuousFlexibility.Analysis.N01aReferenceMeasurable
import ContinuousFlexibility.Analysis.N01aReferenceModes

/-!
# The actual angular-mode map on physical L²

All integrals use the reference convention of a normalized angular integral
over a full turn.  No alternate Fourier norm or finite-mode restriction is
introduced.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology

def referenceModeL2Constant : ℝ :=
  (2 * Real.pi)⁻¹ * Real.sqrt 2 * Real.sqrt (2 * Real.pi)

theorem referenceModeL2Constant_nonneg : 0 ≤ referenceModeL2Constant := by
  unfold referenceModeL2Constant
  positivity

theorem abs_cosineMode_le_sqrt_two (j : ℕ) (θ : ℝ) :
    |Radial.cosineMode j θ| ≤ Real.sqrt 2 := by
  rw [Radial.cosineMode, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (Real.abs_cos_le_one ((j : ℝ) * θ)) (Real.sqrt_nonneg 2)

theorem radialAngularMean_mul_cosine_sq_le {f : ℝ → ℝ}
    (hf : Integrable (fun θ => f θ ^ 2)
      (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))) (j : ℕ) :
    (radialAngularMean (fun θ => f θ * Radial.cosineMode j θ)) ^ 2 ≤
      referenceModeL2Constant ^ 2 *
        ∫ θ in Ioc (0 : ℝ) (2 * Real.pi), f θ ^ 2 := by
  let ν : Measure ℝ := volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))
  have ha : Integrable (fun θ => |f θ|) ν :=
    (n01a_memLp_abs_of_integrable_sq hf).integrable (by norm_num)
  have hmass : ν.real univ = 2 * Real.pi := by
    simp only [ν, measureReal_def, Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero,
      ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
  have hraw : |∫ θ, f θ * Radial.cosineMode j θ ∂ν| ≤
      Real.sqrt 2 * ∫ θ, |f θ| ∂ν := by
    have h := norm_integral_le_of_norm_le (ha.const_mul (Real.sqrt 2))
      (Eventually.of_forall fun θ => show ‖f θ * Radial.cosineMode j θ‖ ≤
        Real.sqrt 2 * |f θ| from by
          rw [Real.norm_eq_abs, abs_mul, mul_comm (Real.sqrt 2)]
          exact mul_le_mul_of_nonneg_left (abs_cosineMode_le_sqrt_two j θ) (abs_nonneg _))
    simpa only [Real.norm_eq_abs, integral_const_mul] using h
  have habs := n01a_integral_abs_le_sqrt_square hf
  rw [hmass] at habs
  have hb : |radialAngularMean (fun θ => f θ * Radial.cosineMode j θ)| ≤
      referenceModeL2Constant * Real.sqrt (∫ θ, f θ ^ 2 ∂ν) := by
    unfold radialAngularMean
    rw [intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi),
      abs_mul, abs_of_nonneg (inv_nonneg.mpr (by positivity : (0 : ℝ) ≤ 2 * Real.pi))]
    calc
      _ ≤ (2 * Real.pi)⁻¹ * (Real.sqrt 2 * ∫ θ, |f θ| ∂ν) :=
        mul_le_mul_of_nonneg_left hraw (by positivity)
      _ ≤ (2 * Real.pi)⁻¹ *
          (Real.sqrt 2 * (Real.sqrt (2 * Real.pi) * Real.sqrt (∫ θ, f θ ^ 2 ∂ν))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left habs (Real.sqrt_nonneg _)) (by positivity)
      _ = _ := by unfold referenceModeL2Constant; ring
  have h := pow_le_pow_left₀ (abs_nonneg _) hb 2
  simpa only [sq_abs, mul_pow, Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)] using h

theorem referenceMode_mul_radial (a : ℝ → ℝ) (u : PolarPoint → ℝ)
    (j : ℕ) (r : ℝ) :
    referenceMode (fun p => a p.1 * u p) j r = a r * referenceMode u j r := by
  unfold referenceMode
  simp only [mul_assoc]
  exact radialAngularMean_const_mul _ _

/-- The mode map is bounded for every radial measure, so the same estimate
can be used before or after inserting any actual radial weight. -/
theorem referenceMode_memLp_two_and_integral_bound {μ : Measure ℝ} [SFinite μ]
    {u : PolarPoint → ℝ}
    (hu : MemLp u 2 (μ.prod (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))))
    (j : ℕ) :
    MemLp (referenceMode u j) 2 μ ∧
      (∫ r, referenceMode u j r ^ 2 ∂μ) ≤ referenceModeL2Constant ^ 2 *
        ∫ p, u p ^ 2 ∂μ.prod (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))) := by
  have hc : Continuous (fun p : PolarPoint => Radial.cosineMode j p.2) := by
    unfold Radial.cosineMode
    fun_prop
  have hm : AEStronglyMeasurable (referenceMode u j) μ := by
    have h := (hu.aestronglyMeasurable.mul hc.aestronglyMeasurable).integral_prod_right'
    change AEStronglyMeasurable (fun r => (2 * Real.pi)⁻¹ *
      ∫ θ in 0..2 * Real.pi, u (r, θ) * Radial.cosineMode j θ) μ
    simpa only [
      intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)] using
      h.const_mul (2 * Real.pi)⁻¹
  have hi := hu.integrable_sq
  have hb : ∀ᵐ r ∂μ, referenceMode u j r ^ 2 ≤ referenceModeL2Constant ^ 2 *
      ∫ θ in Ioc (0 : ℝ) (2 * Real.pi), u (r, θ) ^ 2 := by
    filter_upwards [hi.prod_right_ae] with r hr
    exact radialAngularMean_mul_cosine_sq_le hr j
  have hmajor : Integrable
      (fun r => referenceModeL2Constant ^ 2 *
        ∫ θ in Ioc (0 : ℝ) (2 * Real.pi), u (r, θ) ^ 2) μ :=
    hi.integral_prod_left.const_mul _
  have hsq : Integrable (fun r => referenceMode u j r ^ 2) μ := by
    apply hmajor.mono'
      (hm.aemeasurable.pow_const 2).aestronglyMeasurable
    filter_upwards [hb] with r hr
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)] using hr
  refine ⟨(memLp_two_iff_integrable_sq hm).mpr hsq, ?_⟩
  calc
    _ ≤ ∫ r, referenceModeL2Constant ^ 2 *
        (∫ θ in Ioc (0 : ℝ) (2 * Real.pi), u (r, θ) ^ 2) ∂μ :=
      integral_mono_ae hsq hmajor hb
    _ = _ := by rw [integral_const_mul, MeasureTheory.integral_prod _ hi]

theorem referenceMode_memLp_two {D : ReferenceData} {u : PolarPoint → ℝ}
    (hu : MemLp u 2 (radialPhysicalMeasure D)) (j : ℕ) :
    MemLp (referenceMode u j) 2 (volume.restrict (radialCore D)) := by
  rw [radialPhysicalMeasure_eq_prod] at hu
  exact (referenceMode_memLp_two_and_integral_bound hu j).1

end ContinuousFlexibility.Statements
