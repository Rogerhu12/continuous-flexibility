import ContinuousFlexibility.Radial.ZeroModeWeightGeometry
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Weighted pointwise bounds for the actual zero-mode Green kernel

The input weight is `exp (M₀ q + γ S)` and the output weight is
`exp (-M₁ q + γ S)`. A single source loss works for every exponent in
`[0,1]`. Both estimates below use the actual profile and cell levels.
The resistance integral is the kernel obtained by exchanging the two
integrals in `zeroModeHeight`.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real MeasureTheory
open ContinuousFlexibility.Statements

theorem zeroMode_weighted_inverseProfile_bound
    {D : ReferenceData} {C : ℕ → ℝ}
    (hD : AccumulatingProfileBounds D C) :
    ∃ Mstar K : ℝ, 0 < Mstar ∧ 0 < K ∧
      ∀ M₀ M₁ γ : ℝ, Mstar ≤ M₀ → 0 ≤ M₁ → γ ∈ Icc (0 : ℝ) 1 →
      ∀ k m : ℕ, ∀ r t s : ℝ,
      r ∈ D.cells k → t ∈ D.cells m → s ∈ radialCore D →
      min (t - D.a) (D.b - t) ≤ min (r - D.a) (D.b - r) →
      min (t - D.a) (D.b - t) ≤ min (s - D.a) (D.b - s) →
      exp (-M₁ * radialQ (D.cellIndex k) + γ * radialS (D.cellIndex k)) *
        (D.w s)⁻¹ ≤
      K * exp (M₀ * radialQ (D.cellIndex m) + γ * radialS (D.cellIndex m)) := by
  obtain ⟨shift, hshift⟩ := zeroMode_cellIndex_le_add_of_endpointDistance_le hD
  obtain ⟨A, B, hA, hB, hS⟩ := zeroMode_radialS_shift_sub_le shift
  obtain ⟨U, V, hU, hV, hw⟩ := zeroMode_inverseProfile_bound_of_deeper hD
  refine ⟨V + A, U * exp B, by linarith, by positivity, ?_⟩
  intro M₀ M₁ γ hM₀ hM₁ hγ k m r t s hr ht hs htr hts
  have hqk := radialQ_nonneg (D.cellIndex k)
  have hqm := radialQ_nonneg (D.cellIndex m)
  have hlevel := hshift k m r t hr ht htr
  have hSk :
      radialS (D.cellIndex k) - radialS (D.cellIndex m) ≤
        A * radialQ (D.cellIndex m) + B := by
    exact (sub_le_sub_right (radialS_monotone hlevel) _).trans (hS _)
  have hγS :
      γ * (radialS (D.cellIndex k) - radialS (D.cellIndex m)) ≤
        A * radialQ (D.cellIndex m) + B := by
    calc
      _ ≤ γ * (A * radialQ (D.cellIndex m) + B) :=
        mul_le_mul_of_nonneg_left hSk hγ.1
      _ ≤ 1 * (A * radialQ (D.cellIndex m) + B) :=
        mul_le_mul_of_nonneg_right hγ.2 (add_nonneg (mul_nonneg hA hqm) hB)
      _ = _ := one_mul _
  have hcost := mul_le_mul_of_nonneg_right hM₀ hqm
  have hexp :
      (-M₁ * radialQ (D.cellIndex k) + γ * radialS (D.cellIndex k)) +
        V * radialQ (D.cellIndex m) ≤
      B + (M₀ * radialQ (D.cellIndex m) + γ * radialS (D.cellIndex m)) := by
    nlinarith only [hγS, hcost, mul_nonneg hM₁ hqk]
  calc
    exp (-M₁ * radialQ (D.cellIndex k) + γ * radialS (D.cellIndex k)) *
        (D.w s)⁻¹ ≤
      exp (-M₁ * radialQ (D.cellIndex k) + γ * radialS (D.cellIndex k)) *
        (U * exp (V * radialQ (D.cellIndex m))) :=
      mul_le_mul_of_nonneg_left (hw m t s ht hs hts) (exp_pos _).le
    _ = U * exp ((-M₁ * radialQ (D.cellIndex k) + γ * radialS (D.cellIndex k)) +
        V * radialQ (D.cellIndex m)) := by rw [exp_add]; ring
    _ ≤ U * exp (B + (M₀ * radialQ (D.cellIndex m) + γ * radialS (D.cellIndex m))) :=
      mul_le_mul_of_nonneg_left (exp_le_exp.mpr hexp) hU.le
    _ = (U * exp B) *
        exp (M₀ * radialQ (D.cellIndex m) + γ * radialS (D.cellIndex m)) := by
      rw [exp_add]
      ring

/-- Every point between two interior points is at least as far from the
endpoints as the deeper of the two points. -/
theorem zeroMode_endpointDistance_le_between
    {a b r t s : ℝ}
    (htr : min (t - a) (b - t) ≤ min (r - a) (b - r))
    (hs : s ∈ Icc (min r t) (max r t)) :
    min (t - a) (b - t) ≤ min (s - a) (b - s) := by
  have hra := htr.trans (min_le_left (r - a) (b - r))
  have hrb := htr.trans (min_le_right (r - a) (b - r))
  have hta := min_le_left (t - a) (b - t)
  have htb := min_le_right (t - a) (b - t)
  rcases le_total r t with hrt | hrt
  · rw [min_eq_left hrt, max_eq_right hrt] at hs
    exact le_min (by linarith only [hra, hs.1]) (by linarith only [htb, hs.2])
  · rw [min_eq_right hrt, max_eq_left hrt] at hs
    exact le_min (by linarith only [hta, hs.1]) (by linarith only [hrb, hs.2])

/-- The actual resistance kernel has a common weighted bound on both
endpoint triangles. The integral interval stays strictly inside the core. -/
theorem zeroMode_weighted_resistance_bound
    {D : ReferenceData} {C : ℕ → ℝ}
    (hD : AccumulatingProfileBounds D C) :
    ∃ Mstar K : ℝ, 0 < Mstar ∧ 0 < K ∧
      ∀ M₀ M₁ γ : ℝ, Mstar ≤ M₀ → 0 ≤ M₁ → γ ∈ Icc (0 : ℝ) 1 →
      ∀ k m : ℕ, ∀ r t : ℝ,
      r ∈ D.cells k → t ∈ D.cells m →
      min (t - D.a) (D.b - t) ≤ min (r - D.a) (D.b - r) →
      exp (-M₁ * radialQ (D.cellIndex k) + γ * radialS (D.cellIndex k)) *
        (∫ s in min r t..max r t, (D.w s)⁻¹) ≤
      K * exp (M₀ * radialQ (D.cellIndex m) + γ * radialS (D.cellIndex m)) := by
  obtain ⟨Mstar, K, hMstar, hK, hpoint⟩ := zeroMode_weighted_inverseProfile_bound hD
  have hab : D.a < D.b := hD.1.2.1
  refine ⟨Mstar, (D.b - D.a) * K, hMstar, mul_pos (sub_pos.mpr hab) hK, ?_⟩
  intro M₀ M₁ γ hM₀ hM₁ hγ k m r t hr ht htr
  have hrCore : r ∈ radialCore D := hD.2.1.2.2.2.1 k hr
  have htCore : t ∈ radialCore D := hD.2.1.2.2.2.1 m ht
  have hmin : D.a < min r t := lt_min hrCore.1 htCore.1
  have hmax : max r t < D.b := max_lt hrCore.2 htCore.2
  have hcore (s : ℝ) (hs : s ∈ Icc (min r t) (max r t)) : s ∈ radialCore D :=
    ⟨hmin.trans_le hs.1, hs.2.trans_lt hmax⟩
  have hc : ContinuousOn (fun s => (D.w s)⁻¹) (Icc (min r t) (max r t)) :=
    hD.1.2.2.1.1.continuous.continuousOn.inv₀
      (fun s hs => (hD.1.2.2.2.2.1 s (hcore s hs)).ne')
  have hi : IntervalIntegrable (fun s => (D.w s)⁻¹) volume (min r t) (max r t) :=
    hc.intervalIntegrable_of_Icc (min_le_max r t)
  have hint := intervalIntegral.integral_mono_on (min_le_max r t)
    (hi.const_mul
      (exp (-M₁ * radialQ (D.cellIndex k) + γ * radialS (D.cellIndex k))))
    (intervalIntegrable_const (a := min r t) (b := max r t)
      (c := K * exp (M₀ * radialQ (D.cellIndex m) + γ * radialS (D.cellIndex m))))
    (fun s hs => hpoint M₀ M₁ γ hM₀ hM₁ hγ k m r t s hr ht (hcore s hs) htr
      (zeroMode_endpointDistance_le_between htr hs))
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const,
    smul_eq_mul] at hint
  have hwidth : max r t - min r t ≤ D.b - D.a := by
    linarith only [hmin, hmax]
  calc
    exp (-M₁ * radialQ (D.cellIndex k) + γ * radialS (D.cellIndex k)) *
        (∫ s in min r t..max r t, (D.w s)⁻¹) ≤
      (max r t - min r t) *
        (K * exp (M₀ * radialQ (D.cellIndex m) + γ * radialS (D.cellIndex m))) := hint
    _ ≤ (D.b - D.a) *
        (K * exp (M₀ * radialQ (D.cellIndex m) + γ * radialS (D.cellIndex m))) :=
      mul_le_mul_of_nonneg_right hwidth (mul_pos hK (exp_pos _)).le
    _ = ((D.b - D.a) * K) *
        exp (M₀ * radialQ (D.cellIndex m) + γ * radialS (D.cellIndex m)) := by ring

end ContinuousFlexibility.Radial
