import ContinuousFlexibility.Radial.ReferenceCosineParseval
import ContinuousFlexibility.Radial.ReferenceL2Tensor
import ContinuousFlexibility.Radial.FourierOrthogonality

/-!
# The actual cosine family in angular L²

The constant mode and the positive even physical cosine modes form an
orthonormal family on the circle of period π. Its product-space synthesis
converges in the actual L² norm and retains the exact physical normalization.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace

local instance : Fact (0 < Real.pi) := ⟨Real.pi_pos⟩

/-- Continuous real cosine vectors on the circle of period π. -/
def referenceCircleCosine : ℕ → C(AddCircle Real.pi, ℝ)
  | 0 => ⟨fun _ => 1, continuous_const⟩
  | n + 1 =>
    ⟨fun z => Real.sqrt 2 * (fourier ((n + 1 : ℕ) : ℤ) z).re,
      continuous_const.mul
        (Complex.continuous_re.comp (fourier ((n + 1 : ℕ) : ℤ)).continuous)⟩

@[simp]
theorem referenceCircleCosine_zero (z : AddCircle Real.pi) :
    referenceCircleCosine 0 z = 1 := rfl

theorem referenceCircleCosine_succ_coe (n : ℕ) (θ : ℝ) :
    referenceCircleCosine (n + 1) (θ : AddCircle Real.pi) =
      Radial.cosineMode (2 * (n + 1)) θ := by
  change Real.sqrt 2 * (fourier ((n + 1 : ℕ) : ℤ) (θ : AddCircle Real.pi)).re = _
  rw [referencePiFourier_re]
  unfold Radial.cosineMode
  push_cast
  ring

theorem referenceCircleCosine_even (n : ℕ) (z : AddCircle Real.pi) :
    referenceCircleCosine n (-z) = referenceCircleCosine n z := by
  cases n with
  | zero => rfl
  | succ n =>
    change Real.sqrt 2 * (fourier ((n + 1 : ℕ) : ℤ) (-z)).re =
      Real.sqrt 2 * (fourier ((n + 1 : ℕ) : ℤ) z).re
    rw [referenceFourier_neg_argument, fourier_neg, Complex.conj_re]

theorem referenceCircleCosine_periodic (n : ℕ) :
    Function.Periodic
      (fun θ : ℝ => referenceCircleCosine n (θ : AddCircle Real.pi)) Real.pi := by
  intro θ
  change referenceCircleCosine n ((θ + Real.pi : ℝ) : AddCircle Real.pi) =
    referenceCircleCosine n (θ : AddCircle Real.pi)
  rw [AddCircle.coe_add_period]

/-- Haar normalization on the period-π circle equals the frozen angular mean. -/
theorem referenceCircle_integral_eq_angularMean
    (f : C(AddCircle Real.pi, ℝ)) :
    (∫ z, f z ∂AddCircle.haarAddCircle) =
      radialAngularMean (fun θ : ℝ => f (θ : AddCircle Real.pi)) := by
  have hp : Function.Periodic
      (fun θ : ℝ => f (θ : AddCircle Real.pi)) Real.pi := by
    intro θ
    change f ((θ + Real.pi : ℝ) : AddCircle Real.pi) = f (θ : AddCircle Real.pi)
    rw [AddCircle.coe_add_period]
  have hi : IntervalIntegrable
      (fun θ : ℝ => f (θ : AddCircle Real.pi)) volume 0 Real.pi :=
    (f.continuous.comp (AddCircle.continuous_mk' Real.pi)).intervalIntegrable _ _
  rw [radialAngularMean_eq_pi_mean hp hi, AddCircle.integral_haarAddCircle]
  simpa only [smul_eq_mul, zero_add] using
    congrArg (fun x : ℝ => Real.pi⁻¹ * x)
      (AddCircle.intervalIntegral_preimage Real.pi 0 f).symm

/-- The genuine angular L² vector associated with a continuous cosine mode. -/
def referenceCircleCosineLp (n : ℕ) : Lp ℝ 2
    (AddCircle.haarAddCircle : Measure (AddCircle Real.pi)) :=
  ContinuousMap.toLp 2 AddCircle.haarAddCircle ℝ (referenceCircleCosine n)

theorem referenceCircleCosineLp_ae (n : ℕ) :
    referenceCircleCosineLp n =ᵐ[AddCircle.haarAddCircle] referenceCircleCosine n :=
  ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ)
    AddCircle.haarAddCircle (referenceCircleCosine n)

theorem referenceCircleCosineLp_inner (i j : ℕ) :
    ⟪referenceCircleCosineLp i, referenceCircleCosineLp j⟫_ℝ =
      radialAngularMean (fun θ : ℝ =>
        referenceCircleCosine i (θ : AddCircle Real.pi) *
          referenceCircleCosine j (θ : AddCircle Real.pi)) := by
  calc
    _ = ∫ z, referenceCircleCosine i z * referenceCircleCosine j z
        ∂AddCircle.haarAddCircle := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [referenceCircleCosineLp_ae i, referenceCircleCosineLp_ae j]
        with z hi hj
      simp only [Real.inner_apply, hi, hj]
    _ = _ := referenceCircle_integral_eq_angularMean
      (referenceCircleCosine i * referenceCircleCosine j)

/-- Orthogonality is obtained from the actual normalized cosine integrals. -/
theorem referenceCircleCosineLp_orthonormal :
    Orthonormal ℝ referenceCircleCosineLp := by
  rw [orthonormal_iff_ite]
  intro i j
  rw [referenceCircleCosineLp_inner]
  cases i with
  | zero =>
    cases j with
    | zero =>
      simp [radialAngularMean, Real.pi_ne_zero] <;>
        field_simp [Real.pi_ne_zero]
    | succ j =>
      simp only [referenceCircleCosine_zero, referenceCircleCosine_succ_coe, one_mul]
      change radialAngularMean (Radial.cosineMode (2 * (j + 1))) = 0
      simpa only [Radial.angularAverage, one_div, radialAngularMean] using
        Radial.angularAverage_cosineMode (2 * (j + 1)) (by omega)
  | succ i =>
    cases j with
    | zero =>
      simp only [referenceCircleCosine_zero, referenceCircleCosine_succ_coe, mul_one]
      change radialAngularMean (Radial.cosineMode (2 * (i + 1))) = 0
      simpa only [Radial.angularAverage, one_div, radialAngularMean] using
        Radial.angularAverage_cosineMode (2 * (i + 1)) (by omega)
    | succ j =>
      simp only [referenceCircleCosine_succ_coe]
      have hij : (2 * (i + 1) = 2 * (j + 1)) ↔ i + 1 = j + 1 := by omega
      simpa only [Radial.angularPairing, Radial.angularAverage, one_div,
        radialAngularMean, hij] using
        Radial.angularPairing_cosineMode (2 * (i + 1)) (2 * (j + 1))
          (by omega) (by omega)

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [SFinite μ]

/-- Actual L² synthesis of the constant and positive even cosine modes. -/
def referenceCosineL2Synthesis :
    lp (fun _ : ℕ => Lp ℝ 2 μ) 2 →ₗᵢ[ℝ]
      Lp ℝ 2 (μ.prod (AddCircle.haarAddCircle : Measure (AddCircle Real.pi))) :=
  referenceL2TensorSynthesis referenceCircleCosineLp referenceCircleCosineLp_orthonormal

theorem referenceCosineL2Synthesis_hasSum (f : lp (fun _ : ℕ => Lp ℝ 2 μ) 2) :
    HasSum (fun n => referenceL2Tensor (f n) (referenceCircleCosineLp n))
      (referenceCosineL2Synthesis f) :=
  referenceL2TensorSynthesis_hasSum
    referenceCircleCosineLp referenceCircleCosineLp_orthonormal f

theorem referenceCosineL2Synthesis_norm_sq (f : lp (fun _ : ℕ => Lp ℝ 2 μ) 2) :
    ‖referenceCosineL2Synthesis f‖ ^ 2 = ∑' n, ‖f n‖ ^ 2 :=
  referenceL2TensorSynthesis_norm_sq
    referenceCircleCosineLp referenceCircleCosineLp_orthonormal f

end ContinuousFlexibility.Statements
