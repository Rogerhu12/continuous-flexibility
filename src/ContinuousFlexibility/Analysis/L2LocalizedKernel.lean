module

public import ContinuousFlexibility.Analysis.L2BoundedMultiplier
public import ContinuousFlexibility.Analysis.L2BoundedKernel

/-!
# The kernel of actual localized L² operators

Multiplication on the two sides of a Green operator multiplies the same
kernel on its output and source variables.  The resulting pointwise bound
therefore controls the norm of the actual localized operator.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory

variable (μ : Measure ℝ) {φ ψ : ℝ → ℝ} {M N : ℝ}
  (hφ : AEStronglyMeasurable φ μ) (hψ : AEStronglyMeasurable ψ μ)
  (hφb : ∀ᵐ x ∂μ, |φ x| ≤ M) (hψb : ∀ᵐ x ∂μ, |ψ x| ≤ N)

/-- The two actual multipliers give the localized kernel on every L² source. -/
theorem l2Multiplier_comp_kernel
    (R : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (K : ℝ → ℝ → ℝ)
    (hR : ∀ f : Lp ℝ 2 μ,
      (R f : ℝ → ℝ) =ᵐ[μ] fun x => ∫ y, K x y * f y ∂μ)
    (f : Lp ℝ 2 μ) :
    (((l2BoundedMultiplier μ hφ hφb).comp
      (R.comp (l2BoundedMultiplier μ hψ hψb))) f : ℝ → ℝ) =ᵐ[μ]
      fun x => ∫ y, (φ x * K x y * ψ y) * f y ∂μ := by
  simp only [ContinuousLinearMap.comp_apply]
  filter_upwards [l2BoundedMultiplier_ae μ hφ hφb
    (R (l2BoundedMultiplier μ hψ hψb f)),
    hR (l2BoundedMultiplier μ hψ hψb f)] with x hx hRx
  rw [hx, hRx]
  calc
    _ = φ x * ∫ y, K x y * (ψ y * f y) ∂μ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [l2BoundedMultiplier_ae μ hψ hψb f] with y hy
      rw [hy]
    _ = ∫ y, (φ x * K x y * ψ y) * f y ∂μ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun y => by ring)

/-- A bound on the actual localized kernel controls the same localized operator. -/
theorem l2Multiplier_comp_norm_le [IsFiniteMeasure μ]
    (R : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (K : ℝ → ℝ → ℝ)
    (hR : ∀ f : Lp ℝ 2 μ,
      (R f : ℝ → ℝ) =ᵐ[μ] fun x => ∫ y, K x y * f y ∂μ)
    (hrow : ∀ᵐ x ∂μ, AEStronglyMeasurable (K x) μ)
    {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, |φ x * K x y * ψ y| ≤ B) :
    ‖(l2BoundedMultiplier μ hφ hφb).comp
      (R.comp (l2BoundedMultiplier μ hψ hψb))‖ ≤
      (measureUnivNNReal μ : ℝ) * B := by
  apply l2Kernel_norm_le_mass_mul _ (fun x y => φ x * K x y * ψ y) ?_
    (l2Multiplier_comp_kernel μ hφ hψ hφb hψb R K hR) hB hbound
  filter_upwards [hrow, hbound] with x hx hxb
  apply MemLp.of_bound ((hx.const_mul (φ x)).mul hψ) B
  filter_upwards [hxb] with y hy
  change ‖φ x * K x y * ψ y‖ ≤ B
  simpa only [Real.norm_eq_abs] using hy

end ContinuousFlexibility.Analysis
