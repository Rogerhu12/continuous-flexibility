import ContinuousFlexibility.Radial.TerminalCapEnergy

/-!
# Two attenuation factors in the actual lift energy

The error term is estimated directly from w, the cutoff derivative and
the actual stand-in value on the cutoff layer. The resulting exponential
is exp(-2 action), because the energy contains the square of that value.
Disjoint closed cutoff supports also give exact off-diagonal orthogonality.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory Real
open scoped ContDiff

theorem terminalCapCutoffEnergy_le {r W C A σ : ℝ} {w χ u : ℝ → ℝ}
    (hW : 0 ≤ W) (hw : 0 ≤ w r) (hwW : w r ≤ W)
    (hχ : |deriv χ r| ≤ C)
    (hu : deriv χ r ≠ 0 → |u r| ≤ A * exp (-σ)) :
    terminalCapCutoffEnergy w χ u r ≤ W * C ^ 2 * A ^ 2 * exp (-2 * σ) := by
  by_cases hz : deriv χ r = 0
  · simp only [terminalCapCutoffEnergy, hz, zero_pow (by decide : 2 ≠ 0),
      mul_zero, zero_mul]
    positivity
  · have hχsq : deriv χ r ^ 2 ≤ C ^ 2 := by
      have hs := pow_le_pow_left₀ (abs_nonneg (deriv χ r)) hχ 2
      simpa only [sq_abs] using hs
    have husq : u r ^ 2 ≤ (A * exp (-σ)) ^ 2 := by
      have hs := pow_le_pow_left₀ (abs_nonneg (u r)) (hu hz) 2
      simpa only [sq_abs] using hs
    have he : exp (-σ) ^ 2 = exp (-2 * σ) := by
      rw [pow_two, ← exp_add]
      congr 1
      ring
    calc
      terminalCapCutoffEnergy w χ u r ≤ W * C ^ 2 * (A * exp (-σ)) ^ 2 := by
        apply mul_le_mul _ husq (sq_nonneg _) (mul_nonneg hW (sq_nonneg _))
        exact mul_le_mul hwW hχsq (sq_nonneg _) hW
      _ = _ := by rw [mul_pow, he]; ring

/-- The actual integrated cutoff error, with decay used only where the
cutoff changes. No pointwise bound on a precomputed residual is an input. -/
theorem terminalCapCutoffEnergy_integral_bound {a b W C A σ : ℝ}
    (hab : a ≤ b) (hW : 0 ≤ W) {w χ u : ℝ → ℝ}
    (hw : ContDiff ℝ ∞ w) (hχ : ContDiff ℝ ∞ χ) (hu : ContDiff ℝ ∞ u)
    (hwBounds : ∀ r ∈ Icc a b, 0 ≤ w r ∧ w r ≤ W)
    (hχBound : ∀ r ∈ Icc a b, |deriv χ r| ≤ C)
    (huBound : ∀ r ∈ Icc a b, deriv χ r ≠ 0 → |u r| ≤ A * exp (-σ)) :
    0 ≤ (∫ r in a..b, terminalCapCutoffEnergy w χ u r) ∧
      (∫ r in a..b, terminalCapCutoffEnergy w χ u r) ≤
        (b - a) * W * C ^ 2 * A ^ 2 * exp (-2 * σ) := by
  constructor
  · apply intervalIntegral.integral_nonneg hab
    intro r hr
    exact mul_nonneg (mul_nonneg (hwBounds r hr).1 (sq_nonneg _)) (sq_nonneg _)
  · have hi : IntervalIntegrable (terminalCapCutoffEnergy w χ u) volume a b :=
      (terminalCapCutoffEnergy_continuous hw hχ hu).intervalIntegrable a b
    have hc : IntervalIntegrable (fun _ : ℝ => W * C ^ 2 * A ^ 2 * exp (-2 * σ))
        volume a b := intervalIntegrable_const
    have hbound := intervalIntegral.integral_mono_on hab hi hc
      (fun r hr => terminalCapCutoffEnergy_le hW (hwBounds r hr).1
        (hwBounds r hr).2 (hχBound r hr) (huBound r hr))
    simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_assoc] using hbound

theorem terminalCapLift_energy_error_bound {J lam a b W C A σ : ℝ}
    (hab : a ≤ b) (hlam : 0 < lam) (hW : 0 ≤ W) {w χ u : ℝ → ℝ}
    (hw : ContDiff ℝ ∞ w) (hχ : ContDiff ℝ ∞ χ) (hu : ContDiff ℝ ∞ u)
    (hode : ∀ r ∈ uIcc a b, radialJacobi J w u r = 0)
    (hwBounds : ∀ r ∈ Icc a b, 0 ≤ w r ∧ w r ≤ W)
    (hχBound : ∀ r ∈ Icc a b, |deriv χ r| ≤ C)
    (huBound : ∀ r ∈ Icc a b, deriv χ r ≠ 0 → |u r| ≤ A * exp (-σ)) :
    |(∫ r in a..b, terminalCapEnergyDensity J w (terminalCapLift lam χ u) r) -
      (terminalCapBoundaryFlux w χ u b - terminalCapBoundaryFlux w χ u a) / lam| ≤
        ((b - a) * W * C ^ 2 * A ^ 2 / lam) * exp (-2 * σ) := by
  obtain ⟨hpos, hbound⟩ :=
    terminalCapCutoffEnergy_integral_bound hab hW hw hχ hu hwBounds hχBound huBound
  rw [terminalCapLift_energy_identity hlam hw hχ hu hode, add_sub_cancel_left,
    abs_of_nonneg (div_nonneg hpos hlam.le)]
  calc
    _ ≤ ((b - a) * W * C ^ 2 * A ^ 2 * exp (-2 * σ)) / lam :=
      div_le_div_of_nonneg_right hbound hlam.le
    _ = _ := by ring

/-- Derivative products vanish as well as value products when the closed
cutoff supports are disjoint. This gives the actual zero mixed energy. -/
theorem terminalCapLift_mixed_energy_zero {lam μ J r : ℝ}
    {w χ η u v : ℝ → ℝ} (hsep : Disjoint (tsupport χ) (tsupport η)) :
    w r * deriv (terminalCapLift lam χ u) r * deriv (terminalCapLift μ η v) r +
      J * deriv w r / r * terminalCapLift lam χ u r * terminalCapLift μ η v r = 0 := by
  by_cases hχ : r ∈ tsupport χ
  · have hη : r ∉ tsupport η := fun hη => Set.disjoint_left.mp hsep hχ hη
    have hout : r ∉ tsupport (terminalCapLift μ η v) :=
      fun h => hη (terminalCapLift_tsupport μ η v h)
    rw [deriv_of_notMem_tsupport hout, image_eq_zero_of_notMem_tsupport hout]
    ring
  · have hout : r ∉ tsupport (terminalCapLift lam χ u) :=
      fun h => hχ (terminalCapLift_tsupport lam χ u h)
    rw [deriv_of_notMem_tsupport hout, image_eq_zero_of_notMem_tsupport hout]
    ring

theorem terminalCapLift_mixed_energy_integral_zero {lam μ J a b : ℝ}
    {w χ η u v : ℝ → ℝ} (hsep : Disjoint (tsupport χ) (tsupport η)) :
    (∫ r in a..b,
      w r * deriv (terminalCapLift lam χ u) r * deriv (terminalCapLift μ η v) r +
        J * deriv w r / r * terminalCapLift lam χ u r * terminalCapLift μ η v r) = 0 := by
  simp_rw [terminalCapLift_mixed_energy_zero hsep]
  exact intervalIntegral.integral_zero

end ContinuousFlexibility.Radial
