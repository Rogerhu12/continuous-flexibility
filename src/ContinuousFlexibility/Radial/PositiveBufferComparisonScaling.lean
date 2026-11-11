import ContinuousFlexibility.Radial.PositiveBufferComparisonAffine
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Actual L² scaling in a buffer coordinate

The Jacobian is retained in the norm of the genuine `Lp` element.  These
lemmas apply to the Green profile and to its cutoff commutator.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real MeasureTheory
open scoped RealInnerProductSpace

theorem positiveBuffer_affine_integrable {f : ℝ → ℝ}
    (hf : Integrable f volume) (a : ℝ) {b : ℝ} (hb : b ≠ 0) :
    Integrable (fun x : ℝ => f (a + b * x)) volume :=
  (hf.comp_add_left a).comp_mul_left' hb

theorem positiveBuffer_affine_memLp_two {f : ℝ → ℝ}
    (hc : Continuous f) (hf : MemLp f 2 volume) (a : ℝ) {b : ℝ} (hb : b ≠ 0) :
    MemLp (fun x : ℝ => f (a + b * x)) 2 volume := by
  apply (memLp_two_iff_integrable_sq
    (hc.comp (continuous_const.add (continuous_const.mul continuous_id))).aestronglyMeasurable).2
  exact positiveBuffer_affine_integrable hf.integrable_sq a hb

theorem positiveBuffer_toLp_norm_sq {f : ℝ → ℝ} (hf : MemLp f 2 volume) :
    ‖hf.toLp f‖ ^ 2 = ∫ x : ℝ, f x ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp hf] with x hx
  simp only [RCLike.inner_apply, conj_trivial, hx]
  ring

theorem positiveBuffer_affine_toLp_norm_sq {f : ℝ → ℝ}
    (hc : Continuous f) (hf : MemLp f 2 volume) (a : ℝ) {b : ℝ} (hb : b ≠ 0) :
    ‖(positiveBuffer_affine_memLp_two hc hf a hb).toLp (fun x => f (a + b * x))‖ ^ 2 =
      |b|⁻¹ * ‖hf.toLp f‖ ^ 2 := by
  rw [positiveBuffer_toLp_norm_sq, positiveBuffer_toLp_norm_sq]
  simpa only [preimage_univ, Measure.restrict_univ] using
    positiveBuffer_affine_setIntegral (fun x => f x ^ 2) MeasurableSet.univ a b

theorem positiveBuffer_affine_toLp_norm {f : ℝ → ℝ}
    (hc : Continuous f) (hf : MemLp f 2 volume) (a : ℝ) {b : ℝ} (hb : b ≠ 0) :
    ‖(positiveBuffer_affine_memLp_two hc hf a hb).toLp (fun x => f (a + b * x))‖ =
      sqrt (|b|⁻¹) * ‖hf.toLp f‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _)
    (mul_nonneg (sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, sq_sqrt (inv_nonneg.mpr (abs_nonneg _))]
  exact positiveBuffer_affine_toLp_norm_sq hc hf a hb

theorem positiveBuffer_const_mul_toLp_norm {f : ℝ → ℝ}
    (hf : MemLp f 2 volume) (k : ℝ) :
    ‖(hf.const_mul k).toLp (fun x => k * f x)‖ = |k| * ‖hf.toLp f‖ := by
  change ‖(hf.const_smul k).toLp (k • f)‖ = _
  rw [MemLp.toLp_const_smul, norm_smul, Real.norm_eq_abs]

theorem positiveBuffer_affine_scaled_toLp_norm {f : ℝ → ℝ}
    (hc : Continuous f) (hf : MemLp f 2 volume) (a k : ℝ) {b : ℝ} (hb : b ≠ 0) :
    ‖((positiveBuffer_affine_memLp_two hc hf a hb).const_mul k).toLp
      (fun x => k * f (a + b * x))‖ =
      |k| * sqrt (|b|⁻¹) * ‖hf.toLp f‖ := by
  rw [positiveBuffer_const_mul_toLp_norm (positiveBuffer_affine_memLp_two hc hf a hb) k,
    positiveBuffer_affine_toLp_norm hc hf a hb, mul_assoc]

end ContinuousFlexibility.Radial
