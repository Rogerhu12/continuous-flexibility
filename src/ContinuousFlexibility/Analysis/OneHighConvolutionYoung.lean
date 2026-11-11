import Mathlib.Analysis.LConvolution
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Tactic.NormNum

/-!
# Young's `L¹ * L² → L²` inequality

The positive convolution is mathlib's Lebesgue-integral convolution. Weighted
Cauchy--Schwarz followed by Tonelli proves Young's inequality on any commutative
measurable group with an invariant measure. This includes both circle and
cylinder frequency measures.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory MeasureTheory.Measure
open scoped ENNReal MeasureTheory

variable {G : Type*} [MeasurableSpace G]

private theorem ennreal_mul_half_factor (a b : ℝ≥0∞) :
    a * b = a ^ (1 / (2 : ℝ)) * (a * b ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := by
  have hb : (b ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) = b := by
    rw [← ENNReal.rpow_mul]
    norm_num
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2),
    hb, ← mul_assoc, ← ENNReal.rpow_add_of_nonneg _ _
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  norm_num

/-- Cauchy--Schwarz with the first factor used as a density. -/
theorem lintegral_mul_rpow_two_le {μ : Measure G} {f g : G → ℝ≥0∞}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    (∫⁻ x, f x * g x ∂μ) ^ (2 : ℝ) ≤
      (∫⁻ x, f x ∂μ) * ∫⁻ x, f x * g x ^ (2 : ℝ) ∂μ := by
  have hhalf :
      (∫⁻ x, f x * g x ∂μ) ≤ (∫⁻ x, f x ∂μ) ^ (1 / (2 : ℝ)) *
        (∫⁻ x, f x * g x ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := by
    calc
      _ = ∫⁻ x, f x ^ (1 / (2 : ℝ)) *
          (f x * g x ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) ∂μ :=
        lintegral_congr fun x => ennreal_mul_half_factor (f x) (g x)
      _ ≤ _ := ENNReal.lintegral_mul_norm_pow_le hf (hf.mul (hg.pow_const (2 : ℝ)))
        (by norm_num) (by norm_num) (by norm_num)
  calc
    _ ≤ ((∫⁻ x, f x ∂μ) ^ (1 / (2 : ℝ)) *
        (∫⁻ x, f x * g x ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ))) ^ (2 : ℝ) :=
      ENNReal.rpow_le_rpow hhalf (by norm_num)
    _ = _ := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2),
        ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
      norm_num

variable [AddCommGroup G] [MeasurableAdd₂ G] [MeasurableNeg G]
  {μ : Measure G} [SFinite μ] [IsAddLeftInvariant μ] [IsNegInvariant μ]

/-- Tonelli and translation invariance give the exact `L¹` convolution identity. -/
theorem lconvolution_lintegral {f g : G → ℝ≥0∞}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    (∫⁻ x, (f ⋆ₗ[μ] g) x ∂μ) = (∫⁻ x, f x ∂μ) * ∫⁻ x, g x ∂μ := by
  simp_rw [lconvolution_def]
  rw [lintegral_lintegral_swap (by fun_prop)]
  calc
    (∫⁻ y, ∫⁻ x, f y * g (-y + x) ∂μ ∂μ) =
        ∫⁻ y, f y * ∫⁻ x, g (-y + x) ∂μ ∂μ := by
      apply lintegral_congr
      intro y
      exact lintegral_const_mul'' _ (by fun_prop)
    _ = (∫⁻ y, f y ∂μ) * ∫⁻ x, g x ∂μ := by
      simp_rw [lintegral_add_left_eq_self]
      exact lintegral_mul_const'' _ hf

theorem lconvolution_rpow_two_le {f g : G → ℝ≥0∞}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) (x : G) :
    (f ⋆ₗ[μ] g) x ^ (2 : ℝ) ≤
      (∫⁻ y, f y ∂μ) * (f ⋆ₗ[μ] (fun y => g y ^ (2 : ℝ))) x := by
  have hgx : AEMeasurable (fun y => g (-y + x)) μ := by
    simpa only [Function.comp_def, neg_add_eq_sub] using
      hg.comp_quasiMeasurePreserving (μ.measurePreserving_sub_left x).quasiMeasurePreserving
  simpa only [lconvolution_def] using lintegral_mul_rpow_two_le hf hgx

/-- The squared form of Young's inequality, valid also for infinite integrals. -/
theorem lconvolution_lintegral_rpow_two_le {f g : G → ℝ≥0∞}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    (∫⁻ x, (f ⋆ₗ[μ] g) x ^ (2 : ℝ) ∂μ) ≤
      (∫⁻ x, f x ∂μ) ^ (2 : ℝ) * ∫⁻ x, g x ^ (2 : ℝ) ∂μ := by
  calc
    _ ≤ ∫⁻ x, (∫⁻ y, f y ∂μ) *
        (f ⋆ₗ[μ] (fun y => g y ^ (2 : ℝ))) x ∂μ :=
      lintegral_mono fun x => lconvolution_rpow_two_le hf hg x
    _ = (∫⁻ y, f y ∂μ) * ∫⁻ x,
        (f ⋆ₗ[μ] (fun y => g y ^ (2 : ℝ))) x ∂μ :=
      lintegral_const_mul'' _ (aemeasurable_lconvolution hf (hg.pow_const (2 : ℝ)))
    _ = (∫⁻ x, f x ∂μ) ^ (2 : ℝ) * ∫⁻ x, g x ^ (2 : ℝ) ∂μ := by
      rw [lconvolution_lintegral hf (hg.pow_const (2 : ℝ)), ENNReal.rpow_two]
      simp only [pow_two, mul_assoc]

private theorem eLpNorm_one_nonneg {f : G → ℝ≥0∞} (hf : AEMeasurable f μ) :
    eLpNorm f 1 μ = ∫⁻ x, f x ∂μ := by
  simpa only [enorm_eq_self] using eLpNorm_one_eq_lintegral_enorm hf.aestronglyMeasurable

private theorem eLpNorm_two_nonneg {f : G → ℝ≥0∞} (hf : AEMeasurable f μ) :
    eLpNorm f 2 μ = (∫⁻ x, f x ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := by
  simpa only [ENNReal.toReal_ofNat, enorm_eq_self] using
    eLpNorm_eq_lintegral_rpow_enorm_toReal (p := (2 : ℝ≥0∞))
      (by norm_num) (by norm_num) hf.aestronglyMeasurable

/-- Young's inequality for one `L¹` and one `L²` positive frequency factor. -/
theorem lconvolution_eLpNorm_two_le {f g : G → ℝ≥0∞}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    eLpNorm (f ⋆ₗ[μ] g) 2 μ ≤ eLpNorm f 1 μ * eLpNorm g 2 μ := by
  rw [eLpNorm_two_nonneg (aemeasurable_lconvolution hf hg),
    eLpNorm_one_nonneg hf, eLpNorm_two_nonneg hg]
  calc
    _ ≤ ((∫⁻ x, f x ∂μ) ^ (2 : ℝ) * ∫⁻ x, g x ^ (2 : ℝ) ∂μ) ^
        (1 / (2 : ℝ)) :=
      ENNReal.rpow_le_rpow (lconvolution_lintegral_rpow_two_le hf hg) (by norm_num)
    _ = _ := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2),
        ← ENNReal.rpow_mul]
      norm_num

/-- The symmetric orientation of Young's inequality follows from commutativity. -/
theorem lconvolution_eLpNorm_two_le' {f g : G → ℝ≥0∞}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    eLpNorm (f ⋆ₗ[μ] g) 2 μ ≤ eLpNorm f 2 μ * eLpNorm g 1 μ := by
  rw [lconvolution_comm, mul_comm]
  exact lconvolution_eLpNorm_two_le hg hf

theorem lconvolution_memLp_two {f g : G → ℝ≥0∞}
    (hf : MemLp f 1 μ) (hg : MemLp g 2 μ) : MemLp (f ⋆ₗ[μ] g) 2 μ := by
  apply memLp_iff.mpr
  exact (lconvolution_eLpNorm_two_le hf.aemeasurable hg.aemeasurable).trans_lt
    (ENNReal.mul_lt_top hf hg)

end ContinuousFlexibility.Analysis
