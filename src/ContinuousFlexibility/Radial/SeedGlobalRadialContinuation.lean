import ContinuousFlexibility.Radial.SeedGlobalLogContinuation
import ContinuousFlexibility.Radial.SeedRadialContinuation

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter
open scoped Topology ContDiff

theorem seedConeLogHeight_at_log (A B : ℝ) {r : ℝ} (hr : 0 < r) :
    seedConeLogHeight A B (log r) = A * r ^ 2 + B / r ^ 2 := by
  have hp : exp (2 * log r) = r ^ 2 := by
    rw [show 2 * log r = log r + log r by ring, exp_add, exp_log hr]
    ring
  have hn : exp (-2 * log r) = (r ^ 2)⁻¹ := by
    rw [show -2 * log r = -(2 * log r) by ring, exp_neg, hp]
  simp only [seedConeLogHeight, hp, hn, div_eq_mul_inv]

namespace SeedGlobalLogContinuation

variable {H : ℝ → ℝ} {left right y₀ A B : ℝ}
variable (S : SeedGlobalLogContinuation H left right y₀ A B)

theorem radial_equation (hH : ContDiff ℝ ∞ H) {r : ℝ} (hr : 0 < r) :
    radialJacobi 4 (seedRadialProfile H) (seedRadialHeight S.height) r = 0 := by
  apply radialJacobi_seedRadialHeight hH isOpen_univ (J := univ) (z := deriv S.height) _ hr
    (mem_univ _)
  intro y hy
  exact ⟨(S.smooth.differentiable (by simp) y).hasDerivAt,
    ((contDiff_infty_iff_deriv.mp S.smooth).2.differentiable (by simp) y).hasDerivAt.congr_deriv
      (S.equation y)⟩

theorem radial_value : seedRadialHeight S.height (exp y₀) = A := by
  simpa only [seedRadialHeight, Real.log_exp] using S.value

theorem radial_deriv_value : deriv (seedRadialHeight S.height) (exp y₀) = B / exp y₀ := by
  have hd := hasDerivAt_seedRadialHeight
    (S.smooth.differentiable (by simp) (log (exp y₀))).hasDerivAt (Real.exp_pos y₀)
  rw [hd.deriv, Real.log_exp, S.deriv_value]

theorem radial_left_modes {r : ℝ} (hr : 0 < r) (hy : log r ≤ left) :
    seedRadialHeight S.height r = S.leftA * r ^ 2 + S.leftB / r ^ 2 := by
  rw [seedRadialHeight, S.left_modes _ hy, seedConeLogHeight_at_log _ _ hr]

theorem radial_right_modes {r : ℝ} (hr : 0 < r) (hy : right ≤ log r) :
    seedRadialHeight S.height r = S.rightA * r ^ 2 + S.rightB / r ^ 2 := by
  rw [seedRadialHeight, S.right_modes _ hy, seedConeLogHeight_at_log _ _ hr]

end SeedGlobalLogContinuation
end ContinuousFlexibility.Radial
