import ContinuousFlexibility.Radial.PositiveBufferComparisonGreen

/-!
# The physical cutoff source and its exponential norm bound

The physical Schrödinger operator contributes a factor `mass²` to the
normalized commutator.  The Green normalization divides by the genuine
sum of conormal energies.  The length Jacobian then gives `sqrt mass`
in the error estimate.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter Real MeasureTheory
open ContinuousFlexibility.Statements
open scoped Topology

def positiveBufferGreenError (B : BufferData) (i : Fin 2) (A : ℝ)
    (pin dpin : ℝ → ℝ) (x : ℝ) : ℝ :=
  (B.mass i ^ 2 / A) * positiveBufferCutoffError (B.action i) pin dpin
    (positiveBufferCoordinate B i x)

theorem positiveBufferGreenError_support (B : BufferData) (i : Fin 2) (A : ℝ)
    (pin dpin : ℝ → ℝ) :
    Function.support (positiveBufferGreenError B i A pin dpin) ⊆
      (positiveBufferCoordinate B i) ⁻¹' Icc (B.action i + 2) (B.action i + 4) := by
  intro x hx
  apply positiveBufferCutoffError_support (B.action i) pin dpin
  intro hz
  apply hx
  simp only [positiveBufferGreenError, hz, mul_zero]

theorem positiveBufferGreenError_border_zero {B : BufferData}
    (hB : BufferHypotheses B) (i : Fin 2) (A : ℝ) (pin dpin : ℝ → ℝ)
    {x : ℝ} (hx : x ∈ Function.support (positiveBufferGreenError B i A pin dpin)) :
    B.borderFunction x = 0 := by
  have ht := positiveBufferGreenError_support B i A pin dpin hx
  have hz := positiveBufferPoint_border_eq_zero hB i
    (t := positiveBufferCoordinate B i x) (by linarith [ht.2])
  rwa [positiveBufferPoint_coordinate hB i x] at hz

theorem positiveBufferGreenError_memLp {B : BufferData}
    (hB : BufferHypotheses B) (i : Fin 2) (A : ℝ) {pin dpin q : ℝ → ℝ}
    (hu : ∀ t ∈ Ioo 0 (B.action i + 6), HasDerivAt pin (dpin t) t)
    (hdu : ∀ t ∈ Ioo 0 (B.action i + 6), HasDerivAt dpin (q t * pin t) t) :
    MemLp (positiveBufferGreenError B i A pin dpin) 2 volume := by
  have hσ := buffer_action_pos hB i
  simpa only [positiveBufferGreenError, ← positiveBufferCoordinate_affine] using
    (positiveBuffer_affine_memLp_two (positiveBufferCutoffError_continuous hσ hu hdu)
      (positiveBufferCutoffError_memLp hσ hu hdu)
      (bufferSign i * B.mass i * bufferCut B i)
      (positiveBufferCoordinate_slope_ne_zero hB i)).const_mul (B.mass i ^ 2 / A)

theorem positiveBufferGreenError_toLp_norm {B : BufferData}
    (hB : BufferHypotheses B) (i : Fin 2) (A : ℝ) {pin dpin q : ℝ → ℝ}
    (hu : ∀ t ∈ Ioo 0 (B.action i + 6), HasDerivAt pin (dpin t) t)
    (hdu : ∀ t ∈ Ioo 0 (B.action i + 6), HasDerivAt dpin (q t * pin t) t) :
    ‖(positiveBufferGreenError_memLp hB i A hu hdu).toLp
      (positiveBufferGreenError B i A pin dpin)‖ =
      |B.mass i ^ 2 / A| * sqrt ((B.mass i)⁻¹) *
        ‖(positiveBufferCutoffError_memLp (buffer_action_pos hB i) hu hdu).toLp
          (positiveBufferCutoffError (B.action i) pin dpin)‖ := by
  simpa only [positiveBufferGreenError, ← positiveBufferCoordinate_affine,
    positiveBufferCoordinate_abs_slope hB i] using
    positiveBuffer_affine_scaled_toLp_norm
      (positiveBufferCutoffError_continuous (buffer_action_pos hB i) hu hdu)
      (positiveBufferCutoffError_memLp (buffer_action_pos hB i) hu hdu)
      (bufferSign i * B.mass i * bufferCut B i) (B.mass i ^ 2 / A)
      (positiveBufferCoordinate_slope_ne_zero hB i)

/-- The actual physical `L²` source is exponentially small.  All
constants other than the mass and action belong to the single fixed
smooth cutoff. -/
theorem positiveBufferGreenError_toLp_norm_bound {B : BufferData}
    (hB : BufferHypotheses B) (i : Fin 2) {A C : ℝ}
    (hA : B.mass i ≤ A) (hC : 0 ≤ C)
    (hcut : ∀ t, |deriv (positiveBufferCutoff (B.action i)) t| ≤ C ∧
      |deriv (deriv (positiveBufferCutoff (B.action i))) t| ≤ C)
    {pin dpin q : ℝ → ℝ}
    (hc : ContinuousOn pin (Icc 0 (B.action i + 6)))
    (hu : ∀ t ∈ Ioo 0 (B.action i + 6), HasDerivAt pin (dpin t) t)
    (hdu : ∀ t ∈ Ioo 0 (B.action i + 6), HasDerivAt dpin (q t * pin t) t)
    (hq : ∀ t ∈ Ioo 0 (B.action i + 6), 1 ≤ q t)
    (h0 : pin 0 = 1) (hwall : pin (B.action i + 6) = 0) :
    ‖(positiveBufferGreenError_memLp hB i A hu hdu).toLp
      (positiveBufferGreenError B i A pin dpin)‖ ≤
      6 * C * sqrt (B.mass i) * exp (-B.action i) := by
  have hm := buffer_mass_pos hB i
  have hApos := hm.trans_le hA
  have hnorm := positiveBufferCutoffError_toLp_norm_bound (buffer_action_pos hB i)
    hC hcut hc hu hdu hq h0 hwall
  have hratio : B.mass i / A ≤ 1 :=
    (div_le_iff₀ hApos).2 (by simpa only [one_mul] using hA)
  have hcoef : (B.mass i ^ 2 / A) * sqrt ((B.mass i)⁻¹) ≤ sqrt (B.mass i) := by
    calc
      _ = (B.mass i / A) * (B.mass i / sqrt (B.mass i)) := by
        rw [sqrt_inv]
        ring
      _ = (B.mass i / A) * sqrt (B.mass i) := by rw [div_sqrt]
      _ ≤ 1 * sqrt (B.mass i) :=
        mul_le_mul_of_nonneg_right hratio (sqrt_nonneg _)
      _ = sqrt (B.mass i) := one_mul _
  rw [positiveBufferGreenError_toLp_norm hB i A hu hdu,
    abs_of_nonneg (div_nonneg (sq_nonneg _) hApos.le)]
  calc
    _ ≤ ((B.mass i ^ 2 / A) * sqrt ((B.mass i)⁻¹)) *
        (6 * C * exp (-B.action i)) :=
      mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ ≤ sqrt (B.mass i) * (6 * C * exp (-B.action i)) :=
      mul_le_mul_of_nonneg_right hcoef (by positivity)
    _ = 6 * C * sqrt (B.mass i) * exp (-B.action i) := by ring

end ContinuousFlexibility.Radial
