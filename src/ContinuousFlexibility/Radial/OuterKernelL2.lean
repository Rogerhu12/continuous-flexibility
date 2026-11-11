import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# A continuous core kernel as an actual `L²` operator

A continuous kernel on a compact finite-measure core defines a continuous
linear map on `L²`.  We first take the `L²` inner product with each kernel
row, obtaining a continuous representative, and then include that
representative in `L²`.  This proves integrability and the integral formula
for every `L²` source without assuming an integral operator exists.

The operator norm is at most the core mass times the uniform kernel bound.
This is the core/core estimate used in the outer Green construction.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open MeasureTheory ContinuousLinearMap

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  (μ : Measure X) [IsFiniteMeasure μ]

/-- The continuous function obtained by pairing the source with each kernel row. -/
def outerKernelRepresentative (K : C(X, C(X, ℝ))) (f : Lp ℝ 2 μ) : C(X, ℝ) :=
  ⟨fun x => inner ℝ (ContinuousMap.toLp 2 μ ℝ (K x)) f,
    ((ContinuousMap.toLp 2 μ ℝ).continuous.comp K.continuous).inner continuous_const⟩

theorem outerKernelRepresentative_apply (K : C(X, C(X, ℝ))) (f : Lp ℝ 2 μ) (x : X) :
    outerKernelRepresentative μ K f x = inner ℝ (ContinuousMap.toLp 2 μ ℝ (K x)) f := rfl

private def outerKernelLinearMap (K : C(X, C(X, ℝ))) : Lp ℝ 2 μ →ₗ[ℝ] C(X, ℝ) where
  toFun := outerKernelRepresentative μ K
  map_add' f g := by
    ext x
    simp only [outerKernelRepresentative_apply, ContinuousMap.add_apply, inner_add_right]
  map_smul' c f := by
    ext x
    simp only [outerKernelRepresentative_apply, ContinuousMap.smul_apply, inner_smul_right,
      RingHom.id_apply, smul_eq_mul]

theorem norm_outerKernelRepresentative_le (K : C(X, C(X, ℝ))) (f : Lp ℝ 2 μ) :
    ‖outerKernelRepresentative μ K f‖ ≤
      (‖(ContinuousMap.toLp 2 μ ℝ : C(X, ℝ) →L[ℝ] Lp ℝ 2 μ)‖ * ‖K‖) * ‖f‖ := by
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro x
  rw [outerKernelRepresentative_apply]
  calc
    ‖inner ℝ (ContinuousMap.toLp 2 μ ℝ (K x)) f‖
        ≤ ‖ContinuousMap.toLp 2 μ ℝ (K x)‖ * ‖f‖ := norm_inner_le_norm _ _
    _ ≤ (‖(ContinuousMap.toLp 2 μ ℝ : C(X, ℝ) →L[ℝ] Lp ℝ 2 μ)‖ * ‖K x‖) * ‖f‖ :=
      mul_le_mul_of_nonneg_right ((ContinuousMap.toLp 2 μ ℝ).le_opNorm (K x))
        (norm_nonneg f)
    _ ≤ (‖(ContinuousMap.toLp 2 μ ℝ : C(X, ℝ) →L[ℝ] Lp ℝ 2 μ)‖ * ‖K‖) * ‖f‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (K.norm_coe_le_norm x) (norm_nonneg _)) (norm_nonneg f)

/-- Taking inner products with the kernel rows is a bounded map to continuous functions. -/
def outerKernelToContinuous (K : C(X, C(X, ℝ))) : Lp ℝ 2 μ →L[ℝ] C(X, ℝ) :=
  (outerKernelLinearMap μ K).mkContinuous
    (‖(ContinuousMap.toLp 2 μ ℝ : C(X, ℝ) →L[ℝ] Lp ℝ 2 μ)‖ * ‖K‖)
    (norm_outerKernelRepresentative_le μ K)

theorem outerKernelToContinuous_apply (K : C(X, C(X, ℝ))) (f : Lp ℝ 2 μ) :
    outerKernelToContinuous μ K f = outerKernelRepresentative μ K f := by
  simp only [outerKernelToContinuous, LinearMap.mkContinuous_apply, outerKernelLinearMap,
    LinearMap.coe_mk, AddHom.coe_mk]

/-- The bounded `L²` integral operator built from the actual kernel. -/
def outerKernelL2 (K : C(X, C(X, ℝ))) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  (ContinuousMap.toLp 2 μ ℝ).comp (outerKernelToContinuous μ K)

theorem outerKernelL2_apply (K : C(X, C(X, ℝ))) (f : Lp ℝ 2 μ) :
    outerKernelL2 μ K f = ContinuousMap.toLp 2 μ ℝ (outerKernelRepresentative μ K f) := by
  rw [outerKernelL2, comp_apply, outerKernelToContinuous_apply]

/-- The source against each row is genuinely Bochner integrable. -/
theorem integrable_outerKernel_row (K : C(X, C(X, ℝ))) (f : Lp ℝ 2 μ) (x : X) :
    Integrable (fun y => K x y * f y) μ := by
  have h := L2.integrable_inner (𝕜 := ℝ) (ContinuousMap.toLp 2 μ ℝ (K x)) f
  refine h.congr ?_
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) μ (K x)] with y hy
  rw [Real.inner_apply, hy]

/-- The continuous representative is the stated integral, at every core point. -/
theorem outerKernelRepresentative_eq_integral (K : C(X, C(X, ℝ)))
    (f : Lp ℝ 2 μ) (x : X) :
    outerKernelRepresentative μ K f x = ∫ y, K x y * f y ∂μ := by
  rw [outerKernelRepresentative_apply, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) μ (K x)] with y hy
  rw [Real.inner_apply, hy]

/-- The `L²` class has the actual Green integral as representative. -/
theorem outerKernelL2_ae_eq_integral (K : C(X, C(X, ℝ))) (f : Lp ℝ 2 μ) :
    outerKernelL2 μ K f =ᵐ[μ] fun x => ∫ y, K x y * f y ∂μ := by
  rw [outerKernelL2_apply]
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) μ
    (outerKernelRepresentative μ K f)] with x hx
  exact hx.trans (outerKernelRepresentative_eq_integral μ K f x)

theorem norm_outerKernelToContinuous_le (K : C(X, C(X, ℝ))) :
    ‖outerKernelToContinuous μ K‖ ≤
      ‖(ContinuousMap.toLp 2 μ ℝ : C(X, ℝ) →L[ℝ] Lp ℝ 2 μ)‖ * ‖K‖ := by
  exact LinearMap.mkContinuous_norm_le _ (by positivity)
    (norm_outerKernelRepresentative_le μ K)

private theorem outer_toLp_norm_le_sqrt :
    ‖(ContinuousMap.toLp 2 μ ℝ : C(X, ℝ) →L[ℝ] Lp ℝ 2 μ)‖ ≤
      Real.sqrt (measureUnivNNReal μ : ℝ) := by
  have h := ContinuousMap.toLp_norm_le (p := 2) (𝕜 := ℝ) (E := ℝ) μ
  rw [NNReal.coe_rpow] at h
  convert h using 1 <;> simp [Real.sqrt_eq_rpow]

/-- Core mass times the uniform kernel bound controls the actual operator norm. -/
theorem norm_outerKernelL2_le (K : C(X, C(X, ℝ))) :
    ‖outerKernelL2 μ K‖ ≤ (measureUnivNNReal μ : ℝ) * ‖K‖ := by
  have hnorm := outer_toLp_norm_le_sqrt μ
  calc
    ‖outerKernelL2 μ K‖
        ≤ ‖(ContinuousMap.toLp 2 μ ℝ : C(X, ℝ) →L[ℝ] Lp ℝ 2 μ)‖ *
          ‖outerKernelToContinuous μ K‖ := (ContinuousMap.toLp 2 μ ℝ).opNorm_comp_le _
    _ ≤ ‖(ContinuousMap.toLp 2 μ ℝ : C(X, ℝ) →L[ℝ] Lp ℝ 2 μ)‖ *
          (‖(ContinuousMap.toLp 2 μ ℝ : C(X, ℝ) →L[ℝ] Lp ℝ 2 μ)‖ * ‖K‖) :=
      mul_le_mul_of_nonneg_left (norm_outerKernelToContinuous_le μ K) (norm_nonneg _)
    _ ≤ Real.sqrt (measureUnivNNReal μ : ℝ) *
          (Real.sqrt (measureUnivNNReal μ : ℝ) * ‖K‖) :=
      mul_le_mul hnorm (mul_le_mul_of_nonneg_right hnorm (norm_nonneg K))
        (mul_nonneg (norm_nonneg _) (norm_nonneg K)) (Real.sqrt_nonneg _)
    _ = (measureUnivNNReal μ : ℝ) * ‖K‖ := by
      rw [← mul_assoc, Real.mul_self_sqrt (measureUnivNNReal μ).coe_nonneg]

/-- A bound stated directly for the pointwise kernel. -/
theorem norm_outerKernelL2_le_of_bound (K : C(X, C(X, ℝ))) {B : ℝ}
    (hB : 0 ≤ B) (hK : ∀ x y, |K x y| ≤ B) :
    ‖outerKernelL2 μ K‖ ≤ (measureUnivNNReal μ : ℝ) * B := by
  refine (norm_outerKernelL2_le μ K).trans
    (mul_le_mul_of_nonneg_left ?_ (measureUnivNNReal μ).coe_nonneg)
  apply (ContinuousMap.norm_le K hB).mpr
  intro x
  apply (ContinuousMap.norm_le (K x) hB).mpr
  intro y
  simpa only [Real.norm_eq_abs] using hK x y

end ContinuousFlexibility.Radial
