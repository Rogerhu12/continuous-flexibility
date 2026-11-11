import ContinuousFlexibility.Radial.InnerPositiveGap
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Topology.Order.Compact

/-!
# Closed geometric bounds for actual positive gaps

The profile identity on a closed model interval determines its derivative
at both endpoints by uniqueness of the one-sided derivative. Open join
slope bounds extend to the closed join by continuity. A fixed compact
positive connector has a positive slope constant without any inverse or
coercivity hypothesis.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set
open scoped ContDiff

/-- The logarithmic slope of the physical profile is determined by the
actual radius equation, including the two closed model endpoints. -/
theorem innerProfile_logSlope_identity {R w rho : ℝ → ℝ} {a b lam x : ℝ}
    (hab : a < b) (hR : ContDiff ℝ ∞ R) (hw : ContDiff ℝ ∞ w)
    (hlam : lam ≠ 0) (hRp : R x ≠ 0) (hvp : deriv R x ≠ 0)
    (hprofile : ∀ y ∈ Icc a b, w (R y) = lam * deriv R y)
    (heq : deriv (deriv R) x = -rho x * R x) (hx : x ∈ Icc a b) :
    (R x * deriv w (R x) / w (R x)) * (deriv R x / R x) ^ 2 = -rho x := by
  have hR₂ := (contDiff_infty_iff_deriv.mp hR).2
  have hleft : HasDerivWithinAt (fun y => w (R y))
      (deriv w (R x) * deriv R x) (Icc a b) x :=
    ((hw.differentiable (by simp) (R x)).hasDerivAt.comp x
      (hR.differentiable (by simp) x).hasDerivAt).hasDerivWithinAt
  have hright : HasDerivWithinAt (fun y => w (R y))
      (lam * deriv (deriv R) x) (Icc a b) x := by
    have hmodel : HasDerivWithinAt (fun y => lam * deriv R y)
        (lam * deriv (deriv R) x) (Icc a b) x :=
      ((hR₂.differentiable (by simp) x).hasDerivAt.const_mul lam).hasDerivWithinAt
    exact hmodel.congr_of_mem hprofile hx
  have hd : deriv w (R x) * deriv R x = lam * deriv (deriv R) x :=
    (hleft.derivWithin (uniqueDiffOn_Icc hab x hx)).symm.trans
      (hright.derivWithin (uniqueDiffOn_Icc hab x hx))
  have hd' : deriv w (R x) = (lam * (-rho x * R x)) / deriv R x := by
    apply (eq_div_iff hvp).mpr
    simpa only [heq] using hd
  rw [hd', hprofile x hx]
  field_simp [hlam, hRp, hvp]
  <;> ring

/-- A raw open-connector slope inequality also holds at its matched
endpoints. Positivity of the actual weight excludes a division singularity. -/
theorem innerPositiveGap_closed_slope {w : ℝ → ℝ} {a b c : ℝ}
    (hab : a < b) (hw : ContDiff ℝ ∞ w)
    (hpos : ∀ r ∈ Icc a b, 0 < w r)
    (hslope : ∀ r ∈ Ioo a b, c ≤ r * deriv w r / w r) :
    ∀ r ∈ Icc a b, c ≤ r * deriv w r / w r := by
  have hc : ContinuousOn (fun r => r * deriv w r / w r) (Icc a b) :=
    ((continuous_id.mul (contDiff_infty_iff_deriv.mp hw).2.continuous).continuousOn).div
      hw.continuous.continuousOn (fun r hr => (hpos r hr).ne')
  have hc' : ContinuousOn (fun r => r * deriv w r / w r) (closure (Ioo a b)) := by
    simpa only [closure_Ioo hab.ne] using hc
  intro r hr
  exact le_on_closure hslope continuousOn_const hc'
    (by simpa only [closure_Ioo hab.ne] using hr)

/-- The constant for a fixed central connector is obtained from the raw
strict positivity of its derivative on the compact connector. It has no
dependence on the frequency or on a later tail truncation. -/
theorem innerPositiveGap_exists_slope {w : ℝ → ℝ} {a b : ℝ}
    (ha : 0 < a) (hw : ContDiff ℝ ∞ w)
    (hpos : ∀ r ∈ Icc a b, 0 < w r)
    (hderiv : ∀ r ∈ Icc a b, 0 < deriv w r) :
    ∃ c : ℝ, 0 < c ∧ ∀ r ∈ Icc a b, c ≤ r * deriv w r / w r := by
  have hc : ContinuousOn (fun r => r * deriv w r / w r) (Icc a b) :=
    ((continuous_id.mul (contDiff_infty_iff_deriv.mp hw).2.continuous).continuousOn).div
      hw.continuous.continuousOn (fun r hr => (hpos r hr).ne')
  exact isCompact_Icc.exists_forall_le' hc (fun r hr =>
    div_pos (mul_pos (ha.trans_le hr.1) (hderiv r hr)) (hpos r hr))

end ContinuousFlexibility.Radial
