import ContinuousFlexibility.Radial.Liouville
import ContinuousFlexibility.Statements.RadialTargets

/-!
# General physical conormals of the actual unit Poisson columns

Both signs use one formula. The density-root drift is retained on the
diagonal; removing that same diagonal leaves exactly the two-sided
height/density scaling of the model flux error.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Filter
open ContinuousFlexibility.Statements
open scoped Topology

def innerLiouvilleBoundaryDrift (s : ℝ → ℝ) (cut : Fin 2 → ℝ) (i : Fin 2) : ℝ :=
  -bufferSign i * deriv s (cut i) / s (cut i)

def innerLiouvilleBoundaryKappa (lam : ℝ) (s : ℝ → ℝ)
    (cut : Fin 2 → ℝ) (inward : Fin 2 → ℝ) (i : Fin 2) : ℝ :=
  lam * s (cut i) ^ 2 * (inward i + innerLiouvilleBoundaryDrift s cut i)

theorem innerLiouvilleUnitPoisson_flux {R s w p u : ℝ → ℝ} {lam x t : ℝ}
    (hR : DifferentiableAt ℝ R x) (hs : DifferentiableAt ℝ s x)
    (hp : DifferentiableAt ℝ p x) (hu : DifferentiableAt ℝ u (R x))
    (hs₀ : s x ≠ 0) (hw : w (R x) = lam * s x ^ 2 * deriv R x)
    (hheight : (fun y => u (R y)) =ᶠ[𝓝 x] (fun y => s t * p y / s y)) :
    w (R x) * deriv u (R x) =
      lam * s x * s t * deriv p x - lam * deriv s x * s t * p x := by
  have hflux := liouville_flux_at hR hs (hp.const_mul (s t)) hu hs₀ hw hheight
  rw [(hp.hasDerivAt.const_mul (s t)).deriv] at hflux
  exact hflux.trans (by ring)

theorem innerLiouvilleUnitPoisson_conormal {R s w : ℝ → ℝ}
    {p u : Fin 2 → ℝ → ℝ} {lam : ℝ} (cut : Fin 2 → ℝ)
    (hR : ∀ i, DifferentiableAt ℝ R (cut i))
    (hs : ∀ i, DifferentiableAt ℝ s (cut i))
    (hp : ∀ i k, DifferentiableAt ℝ (p k) (cut i))
    (hu : ∀ i k, DifferentiableAt ℝ (u k) (R (cut i)))
    (hs₀ : ∀ i, s (cut i) ≠ 0)
    (hw : ∀ i, w (R (cut i)) = lam * s (cut i) ^ 2 * deriv R (cut i))
    (hheight : ∀ i k, (fun y => u k (R y)) =ᶠ[𝓝 (cut i)]
      (fun y => s (cut k) * p k y / s y))
    (htrace : ∀ i k, p k (cut i) = if i = k then 1 else 0) (i k : Fin 2) :
    bufferSign i * w (R (cut i)) * deriv (u k) (R (cut i)) =
      lam * s (cut i) * s (cut k) * (bufferSign i * deriv (p k) (cut i)) +
        if i = k then lam * s (cut i) ^ 2 * innerLiouvilleBoundaryDrift s cut i else 0 := by
  have hflux := innerLiouvilleUnitPoisson_flux (hR i) (hs i) (hp i k) (hu i k)
    (hs₀ i) (hw i) (hheight i k)
  rw [mul_assoc (bufferSign i), hflux, htrace i k]
  by_cases hik : i = k
  · subst k
    simp only [eq_self_iff_true, ite_true, mul_one, innerLiouvilleBoundaryDrift]
    field_simp [hs₀ i]
    <;> ring
  · simp only [hik, ite_false, mul_zero, sub_zero, add_zero]
    ring

/-- The diagonal drift cancels exactly against the same kappa in the
physical reference interface. -/
theorem innerLiouvilleUnitPoisson_flux_error {R s w : ℝ → ℝ}
    {p u : Fin 2 → ℝ → ℝ} {lam : ℝ} (cut : Fin 2 → ℝ) (inward : Fin 2 → ℝ)
    (hR : ∀ i, DifferentiableAt ℝ R (cut i))
    (hs : ∀ i, DifferentiableAt ℝ s (cut i))
    (hp : ∀ i k, DifferentiableAt ℝ (p k) (cut i))
    (hu : ∀ i k, DifferentiableAt ℝ (u k) (R (cut i)))
    (hs₀ : ∀ i, s (cut i) ≠ 0)
    (hw : ∀ i, w (R (cut i)) = lam * s (cut i) ^ 2 * deriv R (cut i))
    (hheight : ∀ i k, (fun y => u k (R y)) =ᶠ[𝓝 (cut i)]
      (fun y => s (cut k) * p k y / s y))
    (htrace : ∀ i k, p k (cut i) = if i = k then 1 else 0) (i k : Fin 2) :
    bufferSign i * w (R (cut i)) * deriv (u k) (R (cut i)) -
        (if i = k then innerLiouvilleBoundaryKappa lam s cut inward i else 0) =
      lam * s (cut i) * s (cut k) *
        (bufferSign i * deriv (p k) (cut i) - if i = k then inward i else 0) := by
  rw [innerLiouvilleUnitPoisson_conormal cut hR hs hp hu hs₀ hw hheight htrace]
  by_cases hik : i = k
  · subst k
    simp only [eq_self_iff_true, ite_true, innerLiouvilleBoundaryKappa]
    ring
  · simp only [hik, ite_false, sub_zero, add_zero]

end ContinuousFlexibility.Radial
