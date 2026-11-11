import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul

/-!
# The base-point term in smooth composition

The order-zero estimate follows from a bound on the actual derivative along a
convex region containing zero and the input range. The region cannot be
replaced by the range alone: `OneHighFactorCounterexample` supplies an explicit
obstruction. These estimates allow an arbitrary real normed input space, so
they include a smooth function of several real variables.

The constants below are the specified derivative bound itself. In particular,
they are uniform over the outer functions and inputs satisfying that bound.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory Set
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The mean value theorem with the indispensable segment to the base point. -/
theorem composition_sub_base_norm_le {Φ : E → ℝ} {S : Set E} {M : ℝ}
    (hS : Convex ℝ S) (h0 : (0 : E) ∈ S)
    (hΦ : ∀ z ∈ S, DifferentiableAt ℝ Φ z)
    (hbound : ∀ z ∈ S, ‖fderiv ℝ Φ z‖ ≤ M) {v : E} (hv : v ∈ S) :
    ‖Φ v - Φ 0‖ ≤ M * ‖v‖ := by
  simpa only [sub_zero] using
    hS.norm_image_sub_le_of_norm_fderiv_le hΦ hbound h0 hv

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]

private theorem continuous_composition_sub_base {Φ : E → ℝ} {S : Set E} {v : X → E}
    (hΦ : ∀ z ∈ S, DifferentiableAt ℝ Φ z)
    (hv : Continuous v) (hvin : ∀ x, v x ∈ S) :
    Continuous (fun x => Φ (v x) - Φ 0) := by
  have hΦc : ContinuousOn Φ S :=
    fun z hz => (hΦ z hz).continuousAt.continuousWithinAt
  exact (hΦc.comp_continuous hv hvin).sub continuous_const

/-- Composition after subtracting the base value preserves every finite or
infinite `Lp` class under a uniform first-derivative bound. -/
theorem composition_sub_base_memLp {μ : Measure X} {p : ℝ≥0∞}
    {Φ : E → ℝ} {S : Set E} {v : X → E} {M : ℝ}
    (hS : Convex ℝ S) (h0 : (0 : E) ∈ S) (hM : 0 ≤ M)
    (hΦ : ∀ z ∈ S, DifferentiableAt ℝ Φ z)
    (hbound : ∀ z ∈ S, ‖fderiv ℝ Φ z‖ ≤ M)
    (hv : Continuous v) (hvin : ∀ x, v x ∈ S) (hvLp : MemLp v p μ) :
    MemLp (fun x => Φ (v x) - Φ 0) p μ := by
  apply (hvLp.const_smul M).of_le
    (continuous_composition_sub_base hΦ hv hvin).aestronglyMeasurable
  filter_upwards [] with x
  simpa only [Pi.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg hM] using
    composition_sub_base_norm_le hS h0 hΦ hbound (hvin x)

/-- The corresponding extended-norm inequality, without a finiteness
assumption that could hide an infinite input norm. -/
theorem composition_sub_base_eLpNorm_le {μ : Measure X} {p : ℝ≥0∞}
    {Φ : E → ℝ} {S : Set E} {v : X → E} {M : ℝ}
    (hS : Convex ℝ S) (h0 : (0 : E) ∈ S) (hM : 0 ≤ M)
    (hΦ : ∀ z ∈ S, DifferentiableAt ℝ Φ z)
    (hbound : ∀ z ∈ S, ‖fderiv ℝ Φ z‖ ≤ M)
    (hv : Continuous v) (hvin : ∀ x, v x ∈ S) :
    eLpNorm (fun x => Φ (v x) - Φ 0) p μ ≤ ENNReal.ofReal M * eLpNorm v p μ := by
  have hle : eLpNorm (fun x => Φ (v x) - Φ 0) p μ ≤ eLpNorm (M • v) p μ := by
    apply eLpNorm_mono (continuous_composition_sub_base hΦ hv hvin).aestronglyMeasurable
    intro x
    simpa only [Pi.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg hM] using
      composition_sub_base_norm_le hS h0 hΦ hbound (hvin x)
  simpa only [eLpNorm_const_smul, Real.enorm_of_nonneg hM] using hle

/-- The real norm inequality, with genuine `Lp` membership before taking
`toReal`. At exponent two this is the corrected order-zero composition bound. -/
theorem composition_sub_base_LpNorm_le {μ : Measure X} {p : ℝ≥0∞}
    {Φ : E → ℝ} {S : Set E} {v : X → E} {M : ℝ}
    (hS : Convex ℝ S) (h0 : (0 : E) ∈ S) (hM : 0 ≤ M)
    (hΦ : ∀ z ∈ S, DifferentiableAt ℝ Φ z)
    (hbound : ∀ z ∈ S, ‖fderiv ℝ Φ z‖ ≤ M)
    (hv : Continuous v) (hvin : ∀ x, v x ∈ S) (hvLp : MemLp v p μ) :
    (eLpNorm (fun x => Φ (v x) - Φ 0) p μ).toReal ≤ M * (eLpNorm v p μ).toReal := by
  have htop : ENNReal.ofReal M * eLpNorm v p μ ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hvLp.ne
  have h := ENNReal.toReal_mono htop
    (composition_sub_base_eLpNorm_le hS h0 hM hΦ hbound hv hvin)
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hM] using h

end ContinuousFlexibility.Analysis
