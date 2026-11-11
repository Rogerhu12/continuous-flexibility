import Mathlib.MeasureTheory.Function.L2Space

/-!
# Operator bounds from the actual bounded integral kernel

The source and target measures may differ.  A uniform almost-everywhere
bound on the actual kernel gives its finite-measure L² operator bound.
This applies to localized Green operators after their integral formula
has been established; no bounded integral operator is postulated here.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [IsFiniteMeasure ν]

private theorem l2Kernel_norm_le_constant {f : Lp ℝ 2 μ} {C : ℝ}
    (hC : 0 ≤ C) (hf : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) :
    ‖f‖ ≤ Real.sqrt (measureUnivNNReal μ : ℝ) * C := by
  simpa only [Real.sqrt_eq_rpow, ENNReal.toReal_ofNat, one_div] using
    Lp.norm_le_of_ae_bound hC hf

/-- A uniformly bounded measurable row has the expected L² norm. -/
theorem l2Kernel_row_norm_le {k : X → ℝ} (hk : MemLp k 2 μ) {B : ℝ}
    (hB : 0 ≤ B) (hbound : ∀ᵐ x ∂μ, |k x| ≤ B) :
    ‖hk.toLp k‖ ≤ Real.sqrt (measureUnivNNReal μ : ℝ) * B := by
  apply l2Kernel_norm_le_constant hB
  filter_upwards [hk.coeFn_toLp, hbound] with x hx hxb
  rw [hx, Real.norm_eq_abs]
  exact hxb

/-- Pairing with the row class is exactly the stated integral. -/
theorem l2Kernel_row_inner_eq_integral {k : X → ℝ} (hk : MemLp k 2 μ)
    (f : Lp ℝ 2 μ) :
    inner ℝ (hk.toLp k) f = ∫ x, k x * f x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hk.coeFn_toLp] with x hx
  rw [Real.inner_apply, hx]

/-- A bound on the same kernel representing an operator controls its norm.
The estimate holds for arbitrary L² sources, not just smooth sources. -/
theorem l2Kernel_norm_le_of_ae_bound
    (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 ν) (K : Y → X → ℝ)
    (hrow : ∀ᵐ y ∂ν, MemLp (K y) 2 μ)
    (hrep : ∀ f : Lp ℝ 2 μ,
      (T f : Y → ℝ) =ᵐ[ν] fun y => ∫ x, K y x * f x ∂μ)
    {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ᵐ y ∂ν, ∀ᵐ x ∂μ, |K y x| ≤ B) :
    ‖T‖ ≤ Real.sqrt (measureUnivNNReal μ : ℝ) *
      Real.sqrt (measureUnivNNReal ν : ℝ) * B := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro f
  have hpoint : ∀ᵐ y ∂ν, ‖T f y‖ ≤
      (Real.sqrt (measureUnivNNReal μ : ℝ) * B) * ‖f‖ := by
    filter_upwards [hrow, hrep f, hbound] with y hy hyr hyb
    rw [hyr, ← l2Kernel_row_inner_eq_integral hy f]
    exact (norm_inner_le_norm (hy.toLp (K y)) f).trans
      (mul_le_mul_of_nonneg_right (l2Kernel_row_norm_le hy hB hyb) (norm_nonneg f))
  have hnorm := l2Kernel_norm_le_constant (by positivity) hpoint
  exact hnorm.trans_eq (by ring)

/-- On one finite measure space the factor is its total mass. -/
theorem l2Kernel_norm_le_mass_mul
    (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (K : X → X → ℝ)
    (hrow : ∀ᵐ y ∂μ, MemLp (K y) 2 μ)
    (hrep : ∀ f : Lp ℝ 2 μ,
      (T f : X → ℝ) =ᵐ[μ] fun y => ∫ x, K y x * f x ∂μ)
    {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ᵐ y ∂μ, ∀ᵐ x ∂μ, |K y x| ≤ B) :
    ‖T‖ ≤ (measureUnivNNReal μ : ℝ) * B := by
  calc
    ‖T‖ ≤ Real.sqrt (measureUnivNNReal μ : ℝ) *
        Real.sqrt (measureUnivNNReal μ : ℝ) * B :=
      l2Kernel_norm_le_of_ae_bound T K hrow hrep hB hbound
    _ = _ := by
      rw [← pow_two, Real.sq_sqrt (measureUnivNNReal μ).coe_nonneg]

end ContinuousFlexibility.Analysis
