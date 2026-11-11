import ContinuousFlexibility.Radial.PositiveBufferComparisonCutoff
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Actual L² cutoff errors

The cutoff commutator is a continuous, compactly supported function.
Its normalized support has length two.  This file records the resulting
ordinary L² element and its norm bound.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter Real MeasureTheory
open scoped Topology ContDiff

theorem positiveBufferCutoffError_hasCompactSupport (σ : ℝ) (u du : ℝ → ℝ) :
    HasCompactSupport (positiveBufferCutoffError σ u du) := by
  apply HasCompactSupport.intro (isCompact_Icc : IsCompact (Icc (σ + 2) (σ + 4)))
  intro x hx
  by_contra hne
  exact hx (positiveBufferCutoffError_support σ u du hne)

/-- Only local regularity where the cutoff varies is needed; the
commutator vanishes in a neighborhood of every other point. -/
theorem positiveBufferCutoffError_continuous {σ : ℝ} {u du q : ℝ → ℝ}
    (hσ : 0 < σ)
    (hu : ∀ x ∈ Ioo 0 (σ + 6), HasDerivAt u (du x) x)
    (hdu : ∀ x ∈ Ioo 0 (σ + 6), HasDerivAt du (q x * u x) x) :
    Continuous (positiveBufferCutoffError σ u du) := by
  have h1 : ContDiff ℝ ∞ (deriv (positiveBufferCutoff σ)) :=
    (contDiff_infty_iff_deriv.mp (positiveBufferCutoff_contDiff σ)).2
  have h2 : ContDiff ℝ ∞ (deriv (deriv (positiveBufferCutoff σ))) :=
    (contDiff_infty_iff_deriv.mp h1).2
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x ∈ Ioo 0 (σ + 6)
  · exact ((h2.continuous.continuousAt.neg.mul (hu x hx).continuousAt).sub
      ((continuousAt_const.mul h1.continuous.continuousAt).mul (hdu x hx).continuousAt))
  · have hout : x ∉ Icc (σ + 2) (σ + 4) := by
      intro h
      exact hx ⟨by linarith [h.1], by linarith [h.2]⟩
    have he : positiveBufferCutoffError σ u du =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      filter_upwards [isClosed_Icc.isOpen_compl.mem_nhds hout] with y hy
      have hd := positiveBufferCutoff_derivatives_zero hy
      simp only [positiveBufferCutoffError, hd.1, hd.2, neg_zero, zero_mul, mul_zero, sub_self]
    exact continuousAt_const.congr he.symm

theorem positiveBufferCutoffError_memLp {σ : ℝ} {u du q : ℝ → ℝ}
    (hσ : 0 < σ)
    (hu : ∀ x ∈ Ioo 0 (σ + 6), HasDerivAt u (du x) x)
    (hdu : ∀ x ∈ Ioo 0 (σ + 6), HasDerivAt du (q x * u x) x) :
    MemLp (positiveBufferCutoffError σ u du) 2 volume :=
  (positiveBufferCutoffError_continuous hσ hu hdu).memLp_of_hasCompactSupport
    (positiveBufferCutoffError_hasCompactSupport σ u du)

/-- The L² norm of a bounded function supported on a finite interval.
The proof compares its actual L² representative to the indicator of the
constant bound, so the measure factor is explicit. -/
theorem positiveBuffer_toLp_norm_le_of_support {a b K : ℝ} {f : ℝ → ℝ}
    (hab : a ≤ b) (hK : 0 ≤ K) (hf : MemLp f 2 volume)
    (hsupport : Function.support f ⊆ Icc a b)
    (hbound : ∀ x, |f x| ≤ K) :
    ‖hf.toLp f‖ ≤ K * sqrt (b - a) := by
  let g : Lp ℝ 2 (volume : Measure ℝ) :=
    indicatorConstLp (μ := volume) (s := Icc a b) 2 measurableSet_Icc
      (isCompact_Icc : IsCompact (Icc a b)).measure_lt_top.ne K
  have hle : ‖hf.toLp f‖ ≤ ‖g‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [MemLp.coeFn_toLp hf,
      (indicatorConstLp_coeFn (p := 2) (μ := volume) (s := Icc a b)
        (hs := measurableSet_Icc) (hμs := (isCompact_Icc : IsCompact (Icc a b)).measure_lt_top.ne) (c := K))]
      with x hfx hgx
    change ‖hf.toLp f x‖ ≤ ‖indicatorConstLp (μ := volume) (s := Icc a b) 2 measurableSet_Icc
      (isCompact_Icc : IsCompact (Icc a b)).measure_lt_top.ne K x‖
    rw [hfx, hgx]
    by_cases hx : x ∈ Icc a b
    · rw [indicator_of_mem hx, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hK]
      exact hbound x
    · have hzero : f x = 0 := by
        by_contra hn
        exact hx (hsupport hn)
      simp only [indicator_of_notMem hx, hzero, norm_zero]
      exact le_rfl
  have hgnorm : ‖g‖ = K * sqrt (b - a) := by
    dsimp [g]
    rw [norm_indicatorConstLp (by norm_num) (by norm_num), Real.norm_eq_abs,
      abs_of_nonneg hK, Real.volume_real_Icc_of_le hab]
    norm_num only [ENNReal.toReal_ofNat]
    rw [Real.sqrt_eq_rpow]
  exact hle.trans_eq hgnorm

/-- The ordinary L² source of the normalized cutoff error has an
exponentially small norm, with one universal numerical factor. -/
theorem positiveBufferCutoffError_toLp_norm_bound {σ C : ℝ} {u du q : ℝ → ℝ}
    (hσ : 0 < σ) (hC : 0 ≤ C)
    (hcut : ∀ x, |deriv (positiveBufferCutoff σ) x| ≤ C ∧
      |deriv (deriv (positiveBufferCutoff σ)) x| ≤ C)
    (hc : ContinuousOn u (Icc 0 (σ + 6)))
    (hu : ∀ x ∈ Ioo 0 (σ + 6), HasDerivAt u (du x) x)
    (hdu : ∀ x ∈ Ioo 0 (σ + 6), HasDerivAt du (q x * u x) x)
    (hq : ∀ x ∈ Ioo 0 (σ + 6), 1 ≤ q x)
    (h0 : u 0 = 1) (hwall : u (σ + 6) = 0) :
    ‖(positiveBufferCutoffError_memLp hσ hu hdu).toLp (positiveBufferCutoffError σ u du)‖ ≤
      6 * C * exp (-σ) := by
  have hK : 0 ≤ 3 * C * exp (-σ) := by positivity
  have h := positiveBuffer_toLp_norm_le_of_support
    (a := σ + 2) (b := σ + 4) (by linarith) hK
    (positiveBufferCutoffError_memLp hσ hu hdu)
    (positiveBufferCutoffError_support σ u du)
    (positiveBufferCutoffError_bound hσ hC hcut hc hu hdu hq h0 hwall)
  have hsqrt : sqrt (2 : ℝ) ≤ 2 := by
    nlinarith [sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), sqrt_nonneg (2 : ℝ)]
  rw [show σ + 4 - (σ + 2) = 2 by ring] at h
  calc
    _ ≤ (3 * C * exp (-σ)) * sqrt 2 := h
    _ ≤ (3 * C * exp (-σ)) * 2 := mul_le_mul_of_nonneg_left hsqrt hK
    _ = 6 * C * exp (-σ) := by ring

end ContinuousFlexibility.Radial
