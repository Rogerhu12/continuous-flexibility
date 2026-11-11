import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# The support-length factor in the buffer error

The pointwise cutoff commutator is supported on a layer of length
`1 / m`. Its `m²` pointwise factor therefore becomes `m^(3/2)` in
the actual Lebesgue `L²` norm. The first lemma applies to any source
measure and a measurable set of finite mass.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory

theorem innerL2_norm_le_of_support_bound {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {s : Set α} (hs : MeasurableSet s) (hμs : μ s ≠ ⊤)
    (f : Lp ℝ 2 μ) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ᵐ x ∂μ, x ∈ s → |f x| ≤ M)
    (hsupport : ∀ᵐ x ∂μ, x ∉ s → f x = 0) :
    ‖f‖ ≤ M * Real.sqrt (μ.real s) := by
  let g : Lp ℝ 2 μ := indicatorConstLp 2 hs hμs M
  have hnorm : ‖f‖ ≤ ‖g‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [hbound, hsupport,
      (indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hμs) (c := M))] with x hb hz hg
    change g x = s.indicator (fun _ => M) x at hg
    by_cases hx : x ∈ s
    · rw [hg, indicator_of_mem hx, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hM]
      exact hb hx
    · rw [hz hx, hg, indicator_of_notMem hx, norm_zero]
  have hg : ‖g‖ = M * Real.sqrt (μ.real s) := by
    dsimp only [g]
    rw [norm_indicatorConstLp (by norm_num : (2 : ENNReal) ≠ 0)
      (by norm_num : (2 : ENNReal) ≠ ⊤), Real.norm_eq_abs, abs_of_nonneg hM,
      show (2 : ENNReal).toReal = (2 : ℝ) by norm_num, ← Real.sqrt_eq_rpow]
  exact hnorm.trans_eq hg

theorem innerIntervalL2_norm_le_of_support_bound {a b M : ℝ} (hab : a ≤ b)
    (f : Lp ℝ 2 volume) (hM : 0 ≤ M)
    (hbound : ∀ᵐ x ∂volume, x ∈ Icc a b → |f x| ≤ M)
    (hsupport : ∀ᵐ x ∂volume, x ∉ Icc a b → f x = 0) :
    ‖f‖ ≤ M * Real.sqrt (b - a) := by
  have hμ : volume (Icc a b) ≠ ⊤ := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  simpa only [Real.volume_real_Icc_of_le hab] using
    innerL2_norm_le_of_support_bound measurableSet_Icc hμ f hM hbound hsupport

theorem inner_mass_sqrt_layer {m : ℝ} (hm : 0 < m) :
    m ^ 2 * Real.sqrt (1 / m) = m ^ (3 / 2 : ℝ) := by
  have hm0 : Real.sqrt m ≠ 0 := (Real.sqrt_pos.mpr hm).ne'
  have hs : Real.sqrt m * Real.sqrt m = m := Real.mul_self_sqrt hm.le
  rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one,
    show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hm,
    Real.rpow_one, ← Real.sqrt_eq_rpow]
  field_simp [hm0]
  have hsm := congrArg (fun t : ℝ => m * t) hs
  nlinarith only [hs, hsm]

/-- A mass-scale layer has the exact `m^(3/2)` source cost needed for
the exponentially small global Dirichlet correction. -/
theorem innerBuffer_layer_L2_bound {a m C M : ℝ} (hm : 0 < m)
    (hC : 0 ≤ C) (hM : 0 ≤ M) (f : Lp ℝ 2 volume)
    (hbound : ∀ᵐ x ∂volume, x ∈ Icc a (a + 1 / m) → |f x| ≤ C * m ^ 2 * M)
    (hsupport : ∀ᵐ x ∂volume, x ∉ Icc a (a + 1 / m) → f x = 0) :
    ‖f‖ ≤ C * m ^ (3 / 2 : ℝ) * M := by
  have h := innerIntervalL2_norm_le_of_support_bound
    (le_add_of_nonneg_right (one_div_nonneg.mpr hm.le)) f
    (mul_nonneg (mul_nonneg hC (sq_nonneg _)) hM) hbound hsupport
  calc
    ‖f‖ ≤ (C * m ^ 2 * M) * Real.sqrt (1 / m) := by
      simpa only [add_sub_cancel_left] using h
    _ = C * (m ^ 2 * Real.sqrt (1 / m)) * M := by ring
    _ = _ := by rw [inner_mass_sqrt_layer hm]

end ContinuousFlexibility.Radial
