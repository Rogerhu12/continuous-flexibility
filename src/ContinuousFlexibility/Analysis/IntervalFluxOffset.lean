import ContinuousFlexibility.Analysis.IntervalWeakPotentialRegularity

/-!
# Subtracting a smooth offset from an actual primitive flux

The offset is subtracted from the C¹ representative, and its exact Jacobi
forcing is subtracted from the source. The primitive constant changes by the
offset flux at the base point. This will retain the original left-tail datum.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

theorem intervalLocalPrimitive_deriv_of_contDiff {p : ℝ → ℝ}
    (hp : ContDiff ℝ ∞ p) (x₀ x : ℝ) :
    intervalLocalPrimitive (deriv p) x₀ x = p x - p x₀ := by
  exact intervalIntegral.integral_deriv_eq_sub
    (fun r _ => hp.differentiable (by simp) r)
    ((contDiff_infty_iff_deriv.mp hp).2.continuous.intervalIntegrable _ _)

theorem interval_flux_sub_smooth {a b : ℝ} {u f w V z : ℝ → ℝ}
    (hu : ContDiffOn ℝ 1 u (Ioo a b))
    (huLp : MemLp u 2 (volume.restrict (Ioo a b)))
    (hfLp : MemLp f 2 (volume.restrict (Ioo a b)))
    (hw : ContDiff ℝ ∞ w) (hV : Continuous V) (hz : ContDiff ℝ ∞ z)
    (x₀ q : ℝ) (hx₀ : x₀ ∈ Ioo a b)
    (hflux : ∀ x ∈ Ioo a b, w x * deriv u x =
      intervalLocalPrimitive (fun t => f t + u t * V t) x₀ x + q) :
    ∀ x ∈ Ioo a b, w x * deriv (fun t => u t - z t) x =
      intervalLocalPrimitive
        (fun t => (f t - (deriv (fun s => w s * deriv z s) t - V t * z t)) +
          (u t - z t) * V t) x₀ x + (q - w x₀ * deriv z x₀) := by
  have hzd : ContDiff ℝ ∞ (deriv z) := (contDiff_infty_iff_deriv.mp hz).2
  have hZ : ContDiff ℝ ∞ (fun s => w s * deriv z s) := hw.mul hzd
  have hH : IntegrableOn (fun t => f t + u t * V t) (Ioo a b) volume :=
    (interval_memLp_integrable hfLp).add
      (interval_integrable_mul_continuous huLp hV)
  intro x hx
  have hHi : IntervalIntegrable (fun t => f t + u t * V t) volume x₀ x :=
    intervalIntegrable_of_locallyIntegrableOn_Ioo
      (IntegrableOn.locallyIntegrableOn hH) hx₀ hx
  have hZi : IntervalIntegrable (deriv (fun s => w s * deriv z s)) volume x₀ x :=
    (contDiff_infty_iff_deriv.mp hZ).2.continuous.intervalIntegrable _ _
  have hsplit :
      intervalLocalPrimitive
        (fun t => (f t - (deriv (fun s => w s * deriv z s) t - V t * z t)) +
          (u t - z t) * V t) x₀ x =
        intervalLocalPrimitive (fun t => f t + u t * V t) x₀ x -
          (w x * deriv z x - w x₀ * deriv z x₀) := by
    have heq :
        (fun t => (f t - (deriv (fun s => w s * deriv z s) t - V t * z t)) +
          (u t - z t) * V t) =
        (fun t => (f t + u t * V t) - deriv (fun s => w s * deriv z s) t) := by
      funext t
      ring
    rw [heq]
    change (∫ t in x₀..x, (f t + u t * V t) -
      deriv (fun s => w s * deriv z s) t) = _
    rw [intervalIntegral.integral_sub hHi hZi]
    change intervalLocalPrimitive (fun t => f t + u t * V t) x₀ x -
      intervalLocalPrimitive (deriv (fun s => w s * deriv z s)) x₀ x = _
    rw [intervalLocalPrimitive_deriv_of_contDiff hZ]
  have hud : HasDerivAt u (deriv u x) x :=
    ((hu.differentiableOn (by simp) x hx).differentiableAt
      (isOpen_Ioo.mem_nhds hx)).hasDerivAt
  have hzdAt : HasDerivAt z (deriv z x) x :=
    (hz.differentiable (by simp) x).hasDerivAt
  have hsub : HasDerivAt (fun t => u t - z t) (deriv u x - deriv z x) x :=
    hud.sub hzdAt
  rw [hsub.deriv, mul_sub, hflux x hx, hsplit]
  ring

end ContinuousFlexibility.Analysis
