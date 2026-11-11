import ContinuousFlexibility.Radial.TerminalCapLift
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The actual energy of a terminal cutoff lift

For a homogeneous stand-in, integration by parts gives its cutoff energy
as its boundary flux plus the integral of w (χ')² u². This is the
geometric source of the two attenuation factors in the lift-energy error.
The normalized identity uses the same χu/√lam as TerminalCapLift.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory Real
open scoped ContDiff

def terminalCapEnergyDensity (J : ℝ) (w u : ℝ → ℝ) (r : ℝ) : ℝ :=
  w r * deriv u r ^ 2 + J * deriv w r / r * u r ^ 2

def terminalCapBoundaryFlux (w χ u : ℝ → ℝ) (r : ℝ) : ℝ :=
  χ r ^ 2 * u r * (w r * deriv u r)

def terminalCapCutoffEnergy (w χ u : ℝ → ℝ) (r : ℝ) : ℝ :=
  w r * deriv χ r ^ 2 * u r ^ 2

theorem terminalCapBoundaryFlux_smooth {w χ u : ℝ → ℝ}
    (hw : ContDiff ℝ ∞ w) (hχ : ContDiff ℝ ∞ χ) (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (terminalCapBoundaryFlux w χ u) :=
  ((hχ.pow 2).mul hu).mul (hw.mul (contDiff_infty_iff_deriv.mp hu).2)

theorem terminalCapCutoffEnergy_continuous {w χ u : ℝ → ℝ}
    (hw : ContDiff ℝ ∞ w) (hχ : ContDiff ℝ ∞ χ) (hu : ContDiff ℝ ∞ u) :
    Continuous (terminalCapCutoffEnergy w χ u) :=
  (hw.continuous.mul ((contDiff_infty_iff_deriv.mp hχ).2.continuous.pow 2)).mul
    (hu.continuous.pow 2)

/-- The exact differentiated boundary term; the homogeneous equation is
used for the actual flux derivative, before any integration. -/
theorem terminalCapBoundaryFlux_hasDerivAt {J r : ℝ} {w χ u : ℝ → ℝ}
    (hw : ContDiff ℝ ∞ w) (hχ : ContDiff ℝ ∞ χ) (hu : ContDiff ℝ ∞ u)
    (hode : radialJacobi J w u r = 0) :
    HasDerivAt (terminalCapBoundaryFlux w χ u)
      (terminalCapEnergyDensity J w (fun t => χ t * u t) r -
        terminalCapCutoffEnergy w χ u r) r := by
  have hwD := hw.differentiable (by simp)
  have hχD := hχ.differentiable (by simp)
  have huD := hu.differentiable (by simp)
  have hu₂ := (contDiff_infty_iff_deriv.mp hu).2.differentiable (by simp)
  have hb := (hwD r).hasDerivAt.fun_mul (hu₂ r).hasDerivAt
  have heq : deriv w r * deriv u r + w r * deriv (deriv u) r =
      J * deriv w r / r * u r := by
    unfold radialJacobi at hode
    rw [hb.deriv] at hode
    exact sub_eq_zero.mp hode
  rw [heq] at hb
  have hf := ((((hχD r).hasDerivAt.pow 2).mul (huD r).hasDerivAt).mul hb)
  change HasDerivAt (fun t => χ t ^ 2 * u t * (w t * deriv u t)) _ r
  convert hf using 1
  simp only [terminalCapEnergyDensity, terminalCapCutoffEnergy,
    Nat.cast_ofNat, Nat.reduceSub, pow_one, Pi.mul_apply, Pi.pow_apply]
  rw [deriv_fun_mul (hχD r) (huD r)]
  ring

theorem terminalCapEnergyDensity_eq_deriv_add {J r : ℝ} {w χ u : ℝ → ℝ}
    (hw : ContDiff ℝ ∞ w) (hχ : ContDiff ℝ ∞ χ) (hu : ContDiff ℝ ∞ u)
    (hode : radialJacobi J w u r = 0) :
    terminalCapEnergyDensity J w (fun t => χ t * u t) r =
      deriv (terminalCapBoundaryFlux w χ u) r + terminalCapCutoffEnergy w χ u r := by
  have h := (terminalCapBoundaryFlux_hasDerivAt hw hχ hu hode).deriv
  linarith only [h]

/-- The energy identity on either oriented interval. No boundary values
or normalization have been assumed at this stage. -/
theorem terminalCap_cutoff_energy_identity {J a b : ℝ} {w χ u : ℝ → ℝ}
    (hw : ContDiff ℝ ∞ w) (hχ : ContDiff ℝ ∞ χ) (hu : ContDiff ℝ ∞ u)
    (hode : ∀ r ∈ uIcc a b, radialJacobi J w u r = 0) :
    (∫ r in a..b, terminalCapEnergyDensity J w (fun t => χ t * u t) r) =
      terminalCapBoundaryFlux w χ u b - terminalCapBoundaryFlux w χ u a +
        ∫ r in a..b, terminalCapCutoffEnergy w χ u r := by
  have hF := terminalCapBoundaryFlux_smooth hw hχ hu
  have hFd := hF.differentiable (by simp)
  have hFI : IntervalIntegrable (deriv (terminalCapBoundaryFlux w χ u)) volume a b :=
    (contDiff_infty_iff_deriv.mp hF).2.continuous.intervalIntegrable a b
  have hCI : IntervalIntegrable (terminalCapCutoffEnergy w χ u) volume a b :=
    (terminalCapCutoffEnergy_continuous hw hχ hu).intervalIntegrable a b
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun r (_ : r ∈ uIcc a b) => (hFd r).hasDerivAt) hFI
  calc
    _ = ∫ r in a..b, deriv (terminalCapBoundaryFlux w χ u) r +
        terminalCapCutoffEnergy w χ u r :=
      intervalIntegral.integral_congr (fun r hr => terminalCapEnergyDensity_eq_deriv_add
        hw hχ hu (hode r hr))
    _ = _ := by rw [intervalIntegral.integral_add hFI hCI, hFTC]

/-- The original radial energy scales by the square of the solution
amplitude, using the total derivative convention. -/
theorem terminalCapEnergyDensity_const_mul (J c : ℝ) (w u : ℝ → ℝ) (r : ℝ) :
    terminalCapEnergyDensity J w (fun t => c * u t) r =
      c ^ 2 * terminalCapEnergyDensity J w u r := by
  unfold terminalCapEnergyDensity
  rw [deriv_const_mul_field]
  ring

theorem terminalCapLift_energy_density {J lam r : ℝ} (hlam : 0 < lam)
    (w χ u : ℝ → ℝ) :
    terminalCapEnergyDensity J w (terminalCapLift lam χ u) r =
      terminalCapEnergyDensity J w (fun t => χ t * u t) r / lam := by
  rw [terminalCapLift_eq, terminalCapEnergyDensity_const_mul,
    inv_pow, sq_sqrt hlam.le]
  ring

/-- The energy of the actual normalized lift differs from the normalized
boundary flux by exactly the positive cutoff integral. -/
theorem terminalCapLift_energy_identity {J lam a b : ℝ} (hlam : 0 < lam)
    {w χ u : ℝ → ℝ}
    (hw : ContDiff ℝ ∞ w) (hχ : ContDiff ℝ ∞ χ) (hu : ContDiff ℝ ∞ u)
    (hode : ∀ r ∈ uIcc a b, radialJacobi J w u r = 0) :
    (∫ r in a..b, terminalCapEnergyDensity J w (terminalCapLift lam χ u) r) =
      (terminalCapBoundaryFlux w χ u b - terminalCapBoundaryFlux w χ u a) / lam +
        (∫ r in a..b, terminalCapCutoffEnergy w χ u r) / lam := by
  simp_rw [terminalCapLift_energy_density hlam]
  rw [intervalIntegral.integral_div, terminalCap_cutoff_energy_identity hw hχ hu hode]
  ring

end ContinuousFlexibility.Radial
