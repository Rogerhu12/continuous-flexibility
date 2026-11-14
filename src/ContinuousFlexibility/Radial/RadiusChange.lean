module

public import ContinuousFlexibility.Radial.Liouville
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Source and Hilbert pairings under a radius change

These are genuine finite-interval change-of-variables theorems for the
two measures in the manuscript. Endpoint limits, full-line Hilbert-space
isomorphisms, and closed-operator realizations remain separate tasks.
-/

@[expose] public section

namespace ContinuousFlexibility.Radial

noncomputable section

open Set

/-- Exact finite-interval pullback of the ordinary radial source pairing.
The substitution factor is `v/s`; no spectral measure is substituted for `dr`.
-/
theorem liouville_source_pairing_integral {A B : ℝ} {R v s ψ u f : ℝ → ℝ}
    (hR : ∀ x ∈ uIcc A B, HasDerivAt R (v x) x)
    (hv : ContinuousOn v (uIcc A B))
    (hu : ∀ x ∈ uIcc A B, u (R x) = ψ x / s x)
    (hg : ContinuousOn (fun r => u r * f r) (R '' uIcc A B)) :
    (∫ r in R A..R B, u r * f r) =
      ∫ x in A..B, ψ x * (v x / s x * f (R x)) := by
  calc
    _ = ∫ x in A..B, (u (R x) * f (R x)) * v x :=
      (intervalIntegral.integral_comp_mul_deriv' hR hv hg).symm
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro x hx
      exact liouville_source_pairing_density R s ψ u f x (v x) (hu x hx)

/-- Exact finite-interval pullback of the natural spectral Hilbert norm.
The factor is `12 c (v/R)²`, as in `eq:rad-eq-ha2`. -/
theorem liouville_hilbert_integral {A B c : ℝ} {R v s ψ w u : ℝ → ℝ}
    (hR : ∀ x ∈ uIcc A B, HasDerivAt R (v x) x)
    (hv : ContinuousOn v (uIcc A B))
    (hs₀ : ∀ x ∈ uIcc A B, s x ≠ 0)
    (hw : ∀ x ∈ uIcc A B, w (R x) = c * s x ^ 2 * v x)
    (hu : ∀ x ∈ uIcc A B, u (R x) = ψ x / s x)
    (hg : ContinuousOn (fun r => (12 * w r / r ^ 2) * u r ^ 2) (R '' uIcc A B)) :
    (∫ r in R A..R B, (12 * w r / r ^ 2) * u r ^ 2) =
      ∫ x in A..B, 12 * c * (v x / R x) ^ 2 * ψ x ^ 2 := by
  calc
    _ = ∫ x in A..B, ((12 * w (R x) / R x ^ 2) * u (R x) ^ 2) * v x :=
      (intervalIntegral.integral_comp_mul_deriv' hR hv hg).symm
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro x hx
      exact liouville_hilbert_density (hs₀ x hx) (hw x hx) (hu x hx)

end

end ContinuousFlexibility.Radial
