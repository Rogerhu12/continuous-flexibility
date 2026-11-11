import ContinuousFlexibility.Radial.R11bPartitionMeasurable
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Global physical L2 membership from localized squares

Tonelli's theorem converts the summable family of actual square integrals
into an integrable square majorant. Bounded overlap then controls the
unlocalized field. The measure may be infinite and need not be sigma-finite.
-/

namespace ContinuousFlexibility.Radial

open Filter MeasureTheory
open scoped BigOperators Topology ENNReal

/-- Tonelli's identity for the nonnegative localized square majorant. -/
theorem r11b_lintegral_sum_squares
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (g : ℕ → α → ℝ) (hg : ∀ m, MemLp (g m) 2 μ)
    (hs : Summable (fun m => ∫ x, g m x ^ 2 ∂μ)) :
    (∫⁻ x, ∑' m, ENNReal.ofReal (g m x ^ 2) ∂μ) =
      ENNReal.ofReal (∑' m, ∫ x, g m x ^ 2 ∂μ) := by
  have hgm (m : ℕ) :
      AEMeasurable (fun x => ENNReal.ofReal (g m x ^ 2)) μ :=
    (hg m).integrable_sq.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  rw [lintegral_tsum hgm]
  calc
    (∑' m, ∫⁻ x, ENNReal.ofReal (g m x ^ 2) ∂μ) =
        ∑' m, ENNReal.ofReal (∫ x, g m x ^ 2 ∂μ) := by
      apply tsum_congr
      intro m
      exact (ofReal_integral_eq_lintegral_ofReal (hg m).integrable_sq
        (Eventually.of_forall (fun x => sq_nonneg (g m x)))).symm
    _ = ENNReal.ofReal (∑' m, ∫ x, g m x ^ 2 ∂μ) :=
      (ENNReal.ofReal_tsum_of_nonneg
        (fun m => integral_nonneg (fun x => sq_nonneg (g m x))) hs).symm

/-- Actual global L2 membership and its square estimate follow from the
localized L2 fields, pointwise finite overlap, and summable square integrals. -/
theorem r11b_memLp_of_localized_square_summable
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (χ : ℕ → α → ℝ) (f : α → ℝ) {B : ℕ}
    (hlocal : ∀ m, MemLp (fun x => χ m x * f x) 2 μ)
    (hfinite : ∀ᵐ x ∂μ, (Function.support (fun m => χ m x)).Finite)
    (hcard : ∀ᵐ x ∂μ, (Function.support (fun m => χ m x)).ncard ≤ B)
    (hsum : ∀ᵐ x ∂μ, (∑' m, χ m x) = 1)
    (hintegral : Summable (fun m => ∫ x, (χ m x * f x) ^ 2 ∂μ)) :
    MemLp f 2 μ ∧
      (∫ x, f x ^ 2 ∂μ) ≤ (B : ℝ) * ∑' m, ∫ x, (χ m x * f x) ^ 2 ∂μ := by
  have hf : AEStronglyMeasurable f μ :=
    r11b_aestronglyMeasurable_of_localized χ f
      (fun m => (hlocal m).aestronglyMeasurable) hfinite hsum
  have hnn : ∀ᵐ x ∂μ, 0 ≤ f x ^ 2 :=
    Eventually.of_forall (fun x => sq_nonneg (f x))
  have hpoint : ∀ᵐ x ∂μ, ENNReal.ofReal (f x ^ 2) ≤
      ENNReal.ofReal (B : ℝ) * ∑' m, ENNReal.ofReal ((χ m x * f x) ^ 2) := by
    filter_upwards [hfinite, hcard, hsum] with x hfin hcardx hsumx
    have hfin_sq : (Function.support (fun m => (χ m x * f x) ^ 2)).Finite := by
      apply hfin.subset
      intro m hm hz
      apply hm
      simp [hz]
    have hsq_sum : Summable (fun m => (χ m x * f x) ^ 2) :=
      summable_of_hasFiniteSupport hfin_sq
    have h := ENNReal.ofReal_le_ofReal
      (r11b_partition_square_bound (fun m => χ m x) (f x) hfin hcardx hsumx)
    rw [sq_abs, ENNReal.ofReal_mul (Nat.cast_nonneg B),
      ENNReal.ofReal_tsum_of_nonneg (fun m => sq_nonneg (χ m x * f x)) hsq_sum] at h
    exact h
  have hbound : (∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂μ) ≤
      ENNReal.ofReal ((B : ℝ) * ∑' m, ∫ x, (χ m x * f x) ^ 2 ∂μ) := by
    calc
      _ ≤ ∫⁻ x, ENNReal.ofReal (B : ℝ) *
          ∑' m, ENNReal.ofReal ((χ m x * f x) ^ 2) ∂μ :=
        lintegral_mono_ae hpoint
      _ = _ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          r11b_lintegral_sum_squares (fun m x => χ m x * f x) hlocal hintegral,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg B)]
  have hfi : Integrable (fun x => f x ^ 2) μ :=
    (lintegral_ofReal_ne_top_iff_integrable (hf.pow 2) hnn).mp
      (lt_of_le_of_lt hbound ENNReal.ofReal_lt_top).ne
  refine ⟨(memLp_two_iff_integrable_sq hf).mpr hfi, ?_⟩
  have hC : 0 ≤ (B : ℝ) * ∑' m, ∫ x, (χ m x * f x) ^ 2 ∂μ :=
    mul_nonneg (Nat.cast_nonneg B)
      (tsum_nonneg (fun m => integral_nonneg (fun x => sq_nonneg (χ m x * f x))))
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
  rw [← integral_eq_lintegral_of_nonneg_ae hnn (hf.pow 2),
    ENNReal.toReal_ofReal hC] at ht
  exact ht

end ContinuousFlexibility.Radial
