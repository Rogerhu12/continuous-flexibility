import ContinuousFlexibility.Radial.Liouville
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Exact finite-cell Liouville coefficient identities

The physical signed potential becomes -j²*rho after the normalized
value weights. The density drift contributes s''/s through first-order
integration by parts. Both identities use derivatives of the actual
radius and profile on a neighborhood.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Filter
open scoped Topology ContDiff

theorem innerLiouville_weight_deriv {R s w : ℝ → ℝ} {lam x : ℝ}
    (hR : DifferentiableAt ℝ R x) (hs : DifferentiableAt ℝ s x)
    (hR₂ : DifferentiableAt ℝ (deriv R) x) (hw : DifferentiableAt ℝ w (R x))
    (hweight : (fun y => w (R y)) =ᶠ[𝓝 x]
      (fun y => lam * s y ^ 2 * deriv R y)) :
    deriv w (R x) * deriv R x =
      lam * (2 * s x * deriv s x * deriv R x + s x ^ 2 * deriv (deriv R) x) := by
  have hmodel : HasDerivAt (fun y => lam * s y ^ 2 * deriv R y)
      (lam * (2 * s x * deriv s x * deriv R x + s x ^ 2 * deriv (deriv R) x)) x := by
    convert ((hs.hasDerivAt.pow 2).mul hR₂.hasDerivAt).const_mul lam using 1
    · funext y
      simp only [Pi.mul_apply, Pi.pow_apply]
      ring
    · simp only [Pi.pow_apply]
      ring
  exact (hw.hasDerivAt.comp x hR.hasDerivAt).unique
    (hmodel.congr_of_eventuallyEq hweight)

theorem innerLiouville_radialPotential_pullback {R s w : ℝ → ℝ} {lam x : ℝ}
    (hlam : lam ≠ 0) (hR : DifferentiableAt ℝ R x) (hs : DifferentiableAt ℝ s x)
    (hR₂ : DifferentiableAt ℝ (deriv R) x) (hw : DifferentiableAt ℝ w (R x))
    (hRp : R x ≠ 0) (hvp : deriv R x ≠ 0) (hsp : s x ≠ 0)
    (hweight : (fun y => w (R y)) =ᶠ[𝓝 x]
      (fun y => lam * s y ^ 2 * deriv R y)) (j : ℝ) :
    12 * (deriv R x / R x) ^ 2 *
        ((j ^ 2 / 12) * (R x * deriv w (R x) / w (R x))) =
      -j ^ 2 * liouvilleRho R s x := by
  have hd := innerLiouville_weight_deriv hR hs hR₂ hw hweight
  have hw' : deriv w (R x) =
      lam * (2 * s x * deriv s x * deriv R x + s x ^ 2 * deriv (deriv R) x) /
        deriv R x := (eq_div_iff hvp).mpr hd
  rw [hw', hweight.eq_of_nhds]
  unfold liouvilleRho
  field_simp [hlam, hRp, hvp, hsp]
  <;> ring

theorem innerLiouville_densityDrift_deriv {s : ℝ → ℝ} {x : ℝ}
    (hs : DifferentiableAt ℝ s x) (hs₂ : DifferentiableAt ℝ (deriv s) x)
    (hs₀ : s x ≠ 0) :
    deriv (fun y => deriv s y / s y) x =
      liouvilleV0 s x - (deriv s x / s x) ^ 2 := by
  rw [(hs₂.hasDerivAt.div hs.hasDerivAt hs₀).deriv]
  unfold liouvilleV0
  field_simp [hs₀]
  <;> ring

theorem innerLiouville_densityDrift_prod_deriv {s p : ℝ → ℝ} {x : ℝ}
    (hs : DifferentiableAt ℝ s x) (hs₂ : DifferentiableAt ℝ (deriv s) x)
    (hs₀ : s x ≠ 0) (hp : DifferentiableAt ℝ p x) :
    deriv (fun y => (deriv s y / s y) * p y) x =
      (liouvilleV0 s x - (deriv s x / s x) ^ 2) * p x +
        (deriv s x / s x) * deriv p x := by
  rw [deriv_mul (hs₂.div hs hs₀) hp,
    innerLiouville_densityDrift_deriv hs hs₂ hs₀]

theorem innerLiouville_densityDrift_contDiffAt {s : ℝ → ℝ} {x : ℝ}
    (hs : ContDiff ℝ ∞ s) (hs₀ : s x ≠ 0) :
    ContDiffAt ℝ ∞ (fun y => deriv s y / s y) x :=
  (contDiff_infty_iff_deriv.mp hs).2.contDiffAt.div hs.contDiffAt hs₀

end ContinuousFlexibility.Radial
