import ContinuousFlexibility.Radial.TerminalCapEnergyError

/-!
# The actual lift-source pairing

The commutator source of the same cutoff lift has pairing equal to the
positive cutoff-energy integral. The only boundary assumption is that
the cutoff derivative vanishes at the two integration endpoints.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real MeasureTheory
open scoped ContDiff

def terminalCapCutoffCrossFlux (w χ u : ℝ → ℝ) (x : ℝ) : ℝ :=
  w x * χ x * deriv χ x * u x ^ 2

theorem terminalCapCutoffCrossFlux_smooth {w χ u : ℝ → ℝ}
    (hw : ContDiff ℝ ∞ w) (hχ : ContDiff ℝ ∞ χ) (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (terminalCapCutoffCrossFlux w χ u) :=
  ((hw.mul hχ).mul (contDiff_infty_iff_deriv.mp hχ).2).mul (hu.pow 2)

theorem terminalCapCutoffCrossFlux_hasDerivAt {w χ u : ℝ → ℝ} (x : ℝ)
    (hw : ContDiff ℝ ∞ w) (hχ : ContDiff ℝ ∞ χ) (hu : ContDiff ℝ ∞ u) :
    HasDerivAt (terminalCapCutoffCrossFlux w χ u)
      (terminalCapCutoffEnergy w χ u x +
        χ x * u x * (2 * w x * deriv χ x * deriv u x +
          (deriv w x * deriv χ x + w x * deriv (deriv χ) x) * u x)) x := by
  have hχ' : ContDiff ℝ ∞ (deriv χ) := (contDiff_infty_iff_deriv.mp hχ).2
  have hf := ((((hw.differentiable (by simp) x).hasDerivAt.mul
    (hχ.differentiable (by simp) x).hasDerivAt).mul
      (hχ'.differentiable (by simp) x).hasDerivAt).mul
        ((hu.differentiable (by simp) x).hasDerivAt.pow 2))
  convert hf using 1
  dsimp only [terminalCapCutoffCrossFlux, terminalCapCutoffEnergy]
  norm_num
  ring

theorem terminalCapLift_mul_residual {lam x : ℝ} {w χ u : ℝ → ℝ}
    (hlam : 0 < lam)
    (hw : ContDiff ℝ ∞ w) (hχ : ContDiff ℝ ∞ χ) (hu : ContDiff ℝ ∞ u) :
    terminalCapLift lam χ u x * terminalCapResidual lam w χ u x =
      (terminalCapCutoffEnergy w χ u x - deriv (terminalCapCutoffCrossFlux w χ u) x) / lam := by
  rw [(terminalCapCutoffCrossFlux_hasDerivAt x hw hχ hu).deriv]
  dsimp only [terminalCapLift, terminalCapResidual]
  rw [div_mul_div_comm, mul_self_sqrt hlam.le]
  ring

/-- This is the actual commutator pairing, not a separately postulated
bilinear form identity. -/
theorem terminalCapLift_residual_pairing {lam a b : ℝ} {w χ u : ℝ → ℝ}
    (hlam : 0 < lam)
    (hw : ContDiff ℝ ∞ w) (hχ : ContDiff ℝ ∞ χ) (hu : ContDiff ℝ ∞ u)
    (ha : deriv χ a = 0) (hb : deriv χ b = 0) :
    (∫ x in a..b, terminalCapLift lam χ u x * terminalCapResidual lam w χ u x) =
      (∫ x in a..b, terminalCapCutoffEnergy w χ u x) / lam := by
  have hF := terminalCapCutoffCrossFlux_smooth hw hχ hu
  have hFI : IntervalIntegrable (deriv (terminalCapCutoffCrossFlux w χ u)) volume a b :=
    (contDiff_infty_iff_deriv.mp hF).2.continuous.intervalIntegrable a b
  have hEI := (terminalCapCutoffEnergy_continuous hw hχ hu).intervalIntegrable a b
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x (_ : x ∈ uIcc a b) => (hF.differentiable (by simp) x).hasDerivAt) hFI
  simp_rw [terminalCapLift_mul_residual hlam hw hχ hu]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_sub hEI hFI, hFTC]
  simp only [terminalCapCutoffCrossFlux, ha, hb, mul_zero, zero_mul, sub_zero]

/-- In the original radial coordinate the true Hilbert density cancels
against the true source conversion, giving the same cutoff integral. -/
theorem terminalCapLift_source_density_pairing {lam a b : ℝ} {w χ u : ℝ → ℝ}
    (hlam : 0 < lam)
    (hw : ContDiff ℝ ∞ w) (hχ : ContDiff ℝ ∞ χ) (hu : ContDiff ℝ ∞ u)
    (ha : deriv χ a = 0) (hb : deriv χ b = 0)
    (hr : ∀ x ∈ uIcc a b, x ≠ 0) (hw₀ : ∀ x ∈ uIcc a b, w x ≠ 0) :
    (∫ x in a..b, (12 * w x / x ^ 2) *
      terminalCapLift lam χ u x * terminalCapHilbertSource lam w χ u x) =
      (∫ x in a..b, terminalCapCutoffEnergy w χ u x) / lam := by
  calc
    _ = ∫ x in a..b, terminalCapLift lam χ u x * terminalCapResidual lam w χ u x := by
      apply intervalIntegral.integral_congr
      intro x hx
      change (12 * w x / x ^ 2) * terminalCapLift lam χ u x *
        terminalCapHilbertSource lam w χ u x =
        terminalCapLift lam χ u x * terminalCapResidual lam w χ u x
      rw [show (12 * w x / x ^ 2) * terminalCapLift lam χ u x *
          terminalCapHilbertSource lam w χ u x =
        terminalCapLift lam χ u x * ((12 * w x / x ^ 2) *
          terminalCapHilbertSource lam w χ u x) by ring]
      rw [terminalCapHilbertSource_density (hr x hx) (hw₀ x hx)]
    _ = _ := terminalCapLift_residual_pairing hlam hw hχ hu ha hb

end ContinuousFlexibility.Radial

