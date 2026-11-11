import ContinuousFlexibility.Radial.Gauge
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Actual homogeneous solutions on a cone

The radial second-mode equation on w(r)=c*r is the constant-coefficient
equation v''=4v in y=log r. The two exponential coefficients are conserved.
A single signed-frequency formula treats both independent modes.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter
open scoped Topology ContDiff

def coneLogPullback (u : ℝ → ℝ) (y : ℝ) : ℝ := u (exp y)

theorem hasDerivAt_coneLogPullback {u : ℝ → ℝ} {y : ℝ}
    (hu : DifferentiableAt ℝ u (exp y)) :
    HasDerivAt (coneLogPullback u) (exp y * deriv u (exp y)) y := by
  exact (hu.hasDerivAt.comp y (hasDerivAt_exp y)).congr_deriv (by ring)

theorem hasDerivAt_deriv_coneLogPullback {u : ℝ → ℝ} {J : Set ℝ}
    (hJ : IsOpen J) (hu : ∀ y ∈ J, DifferentiableAt ℝ u (exp y))
    {y : ℝ} (hy : y ∈ J) (hu' : DifferentiableAt ℝ (deriv u) (exp y)) :
    HasDerivAt (deriv (coneLogPullback u))
      (exp y * deriv u (exp y) + exp y ^ 2 * deriv (deriv u) (exp y)) y := by
  have hEq : deriv (coneLogPullback u) =ᶠ[𝓝 y]
      fun t => exp t * deriv u (exp t) := by
    filter_upwards [hJ.mem_nhds hy] with t ht
    exact (hasDerivAt_coneLogPullback (hu t ht)).deriv
  have h := (hasDerivAt_exp y).mul (hu'.hasDerivAt.comp y (hasDerivAt_exp y))
  have hd : HasDerivAt (fun t => exp t * deriv u (exp t))
      (exp y * deriv u (exp y) + exp y ^ 2 * deriv (deriv u) (exp y)) y := by
    apply h.congr_deriv
    simp only [Function.comp_apply]
    ring
  exact hd.congr_of_eventuallyEq hEq

theorem radialJacobi_cone_eq {u : ℝ → ℝ} {c r : ℝ}
    (hu' : DifferentiableAt ℝ (deriv u) r) :
    radialJacobi 4 (fun t => c * t) u r =
      c * (r * deriv (deriv u) r + deriv u r - 4 * u r / r) := by
  have hw : HasDerivAt (fun t : ℝ => c * t) c r := by
    simpa only [mul_one] using (hasDerivAt_id' r).const_mul c
  have hf := hw.mul hu'.hasDerivAt
  unfold radialJacobi
  rw [hf.deriv, hw.deriv]
  ring

theorem coneLogPullback_second_derivative {u : ℝ → ℝ} {J : Set ℝ} {c : ℝ}
    (hc : c ≠ 0) (hJ : IsOpen J)
    (hu : ∀ y ∈ J, DifferentiableAt ℝ u (exp y))
    (hu' : ∀ y ∈ J, DifferentiableAt ℝ (deriv u) (exp y))
    (hode : ∀ y ∈ J, radialJacobi 4 (fun r => c * r) u (exp y) = 0) :
    ∀ y ∈ J, deriv (deriv (coneLogPullback u)) y = 4 * coneLogPullback u y := by
  intro y hy
  have he := hode y hy
  rw [radialJacobi_cone_eq (hu' y hy)] at he
  have he' : exp y * deriv (deriv u) (exp y) + deriv u (exp y) -
      4 * u (exp y) / exp y = 0 := (mul_eq_zero.mp he).resolve_left hc
  field_simp [(exp_pos y).ne'] at he'
  rw [(hasDerivAt_deriv_coneLogPullback hJ hu hy (hu' y hy)).deriv]
  dsimp only [coneLogPullback]
  nlinarith only [he']

/-- Coefficient of exp(s*y) in a solution of v''=s²*v. -/
def coneExponentialCoefficient (v : ℝ → ℝ) (s y : ℝ) : ℝ :=
  (deriv v y + s * v y) / (2 * s) * exp (-s * y)

theorem hasDerivAt_coneExponentialCoefficient {v : ℝ → ℝ} {s y : ℝ}
    (hv : DifferentiableAt ℝ v y) (hv' : DifferentiableAt ℝ (deriv v) y) :
    HasDerivAt (coneExponentialCoefficient v s)
      ((deriv (deriv v) y - s ^ 2 * v y) / (2 * s) * exp (-s * y)) y := by
  have h := ((hv'.hasDerivAt.add (hv.hasDerivAt.const_mul s)).div_const (2 * s)).mul
    (((hasDerivAt_id' y).const_mul (-s)).exp)
  apply h.congr_deriv
  simp only [Function.comp_apply, div_eq_mul_inv]
  ring

theorem coneExponentialCoefficient_const {v : ℝ → ℝ} {J : Set ℝ} {s y₀ : ℝ}
    (hJ : IsOpen J) (hconn : IsPreconnected J) (hy₀ : y₀ ∈ J)
    (hv : ∀ y ∈ J, DifferentiableAt ℝ v y)
    (hv' : ∀ y ∈ J, DifferentiableAt ℝ (deriv v) y)
    (hode : ∀ y ∈ J, deriv (deriv v) y = s ^ 2 * v y) :
    ∀ y ∈ J, coneExponentialCoefficient v s y = coneExponentialCoefficient v s y₀ := by
  have hd (y : ℝ) (hy : y ∈ J) :
      HasDerivAt (coneExponentialCoefficient v s) 0 y := by
    simpa only [hode y hy, sub_self, zero_div, zero_mul] using
      hasDerivAt_coneExponentialCoefficient (hv y hy) (hv' y hy) (s := s)
  intro y hy
  exact hJ.is_const_of_deriv_eq_zero hconn
    (fun t ht => (hd t ht).differentiableAt.differentiableWithinAt)
    (fun t ht => (hd t ht).deriv) hy hy₀

theorem coneExponentialCoefficient_reconstruct (v : ℝ → ℝ) {s : ℝ}
    (hs : s ≠ 0) (y : ℝ) :
    v y = coneExponentialCoefficient v s y * exp (s * y) +
      coneExponentialCoefficient v (-s) y * exp (-s * y) := by
  have he : exp (-s * y) * exp (s * y) = 1 := by
    rw [← exp_add, show -s * y + s * y = 0 by ring, exp_zero]
  have he' : exp (s * y) * exp (-s * y) = 1 := by rw [mul_comm]; exact he
  symm
  calc
    coneExponentialCoefficient v s y * exp (s * y) +
        coneExponentialCoefficient v (-s) y * exp (-s * y) =
        (deriv v y + s * v y) / (2 * s) * (exp (-s * y) * exp (s * y)) +
        (deriv v y + (-s) * v y) / (2 * (-s)) *
          (exp (s * y) * exp (-s * y)) := by
      simp only [coneExponentialCoefficient, neg_neg]
      ring
    _ = (deriv v y + s * v y) / (2 * s) +
        (deriv v y + (-s) * v y) / (2 * (-s)) := by
      rw [he, he', mul_one, mul_one]
    _ = v y := by field_simp [hs]; ring

/-- Exact decomposition with coefficients computed at the chosen base point. -/
theorem eq_coneExponential_modes {v : ℝ → ℝ} {J : Set ℝ} {s y₀ : ℝ}
    (hs : s ≠ 0) (hJ : IsOpen J) (hconn : IsPreconnected J) (hy₀ : y₀ ∈ J)
    (hv : ∀ y ∈ J, DifferentiableAt ℝ v y)
    (hv' : ∀ y ∈ J, DifferentiableAt ℝ (deriv v) y)
    (hode : ∀ y ∈ J, deriv (deriv v) y = s ^ 2 * v y) :
    ∀ y ∈ J, v y = coneExponentialCoefficient v s y₀ * exp (s * y) +
      coneExponentialCoefficient v (-s) y₀ * exp (-s * y) := by
  have hode' : ∀ y ∈ J, deriv (deriv v) y = (-s) ^ 2 * v y := by
    simpa only [neg_sq] using hode
  intro y hy
  rw [coneExponentialCoefficient_reconstruct v hs y,
    coneExponentialCoefficient_const hJ hconn hy₀ hv hv' hode y hy,
    coneExponentialCoefficient_const hJ hconn hy₀ hv hv' hode' y hy]

/-- In ordinary radius the two modes are exactly r² and r⁻². -/
theorem radialCone_eq_modes {u : ℝ → ℝ} {J : Set ℝ} {c y₀ : ℝ}
    (hc : c ≠ 0) (hJ : IsOpen J) (hconn : IsPreconnected J) (hy₀ : y₀ ∈ J)
    (hu : ∀ y ∈ J, DifferentiableAt ℝ u (exp y))
    (hu' : ∀ y ∈ J, DifferentiableAt ℝ (deriv u) (exp y))
    (hode : ∀ y ∈ J, radialJacobi 4 (fun r => c * r) u (exp y) = 0) :
    ∃ A B : ℝ, ∀ r : ℝ, 0 < r → log r ∈ J → u r = A * r ^ 2 + B / r ^ 2 := by
  have hv (y : ℝ) (hy : y ∈ J) :
      DifferentiableAt ℝ (coneLogPullback u) y :=
    (hasDerivAt_coneLogPullback (hu y hy)).differentiableAt
  have hv' (y : ℝ) (hy : y ∈ J) :
      DifferentiableAt ℝ (deriv (coneLogPullback u)) y :=
    (hasDerivAt_deriv_coneLogPullback hJ hu hy (hu' y hy)).differentiableAt
  have hode' : ∀ y ∈ J, deriv (deriv (coneLogPullback u)) y =
      (2 : ℝ) ^ 2 * coneLogPullback u y := by
    simpa only [show (2 : ℝ) ^ 2 = 4 by norm_num] using
      coneLogPullback_second_derivative hc hJ hu hu' hode
  have hrep := eq_coneExponential_modes (by norm_num : (2 : ℝ) ≠ 0)
    hJ hconn hy₀ hv hv' hode'
  refine ⟨coneExponentialCoefficient (coneLogPullback u) 2 y₀,
    coneExponentialCoefficient (coneLogPullback u) (-2) y₀, ?_⟩
  intro r hr hrJ
  have hpow : exp (2 * log r) = r ^ 2 := by
    rw [show 2 * log r = log r + log r by ring, exp_add, exp_log hr]
    ring
  have hneg : exp (-2 * log r) = (r ^ 2)⁻¹ := by
    rw [show -2 * log r = -(2 * log r) by ring, exp_neg, hpow]
  simpa only [coneLogPullback, exp_log hr, hpow, hneg, div_eq_mul_inv] using
    hrep (log r) hrJ

end ContinuousFlexibility.Radial
