import ContinuousFlexibility.Radial.LogSlopeConnector
import ContinuousFlexibility.Radial.SeedPairGluing
import ContinuousFlexibility.Radial.SeedCentralPair

/-!
# Quantitative lower bounds for the actual radial profile

The inequality is kept without division.  It is invariant under the
positive profile rescalings used in the common reference construction.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter
open scoped Topology ContDiff

theorem connectorProfile_logSlope_lower {k : ℝ → ℝ}
    (hk : ContDiff ℝ ∞ k) (hk4 : ∀ y, k y < 4)
    (y₀ f₀ : ℝ) {r ν : ℝ} (hr : 0 < r)
    (hν : ν ≤ (k (log r) ^ 2 - k (log r) + deriv k (log r)) /
      (4 - k (log r))) :
    ν * connectorProfile k y₀ f₀ r ≤ r * deriv (connectorProfile k y₀ f₀) r := by
  rw [(hasDerivAt_connectorProfile hk hk4 y₀ f₀ hr).deriv]
  change ν * (r * exp (connectorLogProfile k y₀ f₀ (log r))) ≤ _
  convert mul_le_mul_of_nonneg_left hν
    (mul_pos hr (exp_pos (connectorLogProfile k y₀ f₀ (log r)))).le using 1 <;> ring

theorem seedRescale_logSlope_lower {R A ν r : ℝ} {w : ℝ → ℝ}
    (hA : 0 ≤ A)
    (hw : ν * w (R⁻¹ * r) ≤ (R⁻¹ * r) * deriv w (R⁻¹ * r)) :
    ν * seedRescale R A w r ≤ r * deriv (seedRescale R A w) r := by
  rw [deriv_seedRescale]
  change ν * (A * w (R⁻¹ * r)) ≤ r * (A * R⁻¹ * deriv w (R⁻¹ * r))
  convert mul_le_mul_of_nonneg_left hw hA using 1 <;> ring

theorem logSlope_lower_of_germ {w v : ℝ → ℝ} {ν r : ℝ}
    (hg : w =ᶠ[𝓝 r] v) (hv : ν * v r ≤ r * deriv v r) :
    ν * w r ≤ r * deriv w r := by
  rw [hg.eq_of_nhds, hg.deriv_eq]
  exact hv

theorem SeedCentralCutoff.profile_logSlope_lower (K : SeedCentralCutoff)
    {r : ℝ} (hr : 0 < r) (hout : log r ≤ K.left ∨ K.right ≤ log r) :
    (3 / 4 : ℝ) * K.profile r ≤ r * deriv K.profile r := by
  apply connectorProfile_logSlope_lower K.smooth K.below_four
    0 (log (centralRadialProfile 1 1)) hr
  exact hout.elim (K.positive_left (log r)) (K.positive_right (log r))

end ContinuousFlexibility.Radial
