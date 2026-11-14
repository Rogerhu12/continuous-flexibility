module

public import ContinuousFlexibility.Analysis.N04bRootCutHeight
public import ContinuousFlexibility.Statements.Nonlinear

/-!
# The root-cut identity for the actual canonical-height definition

The hypotheses identify the two inverse-chart and height germs with a
common physical travel inverse and the explicit root height. They contain
no transmission equation. One side parameter handles both endpoints.

The result does not identify the moving physical cut X(T/2, θ) with a
state-independent radial circle.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Filter
open ContinuousFlexibility.Statements
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

/-- Genuine root inverse-chart and height germs imply the frozen
transmission formula for every smooth physical unknown. -/
theorem n04b_canonicalHeight_root_cut
    {S : PhysicalSpacesData} (K : CanonicalData S)
    (z : AnnularState S × ℝ) (piece : Bool → ℕ)
    {T : ℝ} (hT : 0 < T) (θ : ℝ)
    (X : PolarPoint → PolarPoint) (A : PolarPoint → ℝ)
    (hX : DifferentiableAt ℝ X (T / 2, θ))
    (hA : DifferentiableAt ℝ A (T / 2, θ))
    (hA0 : 0 < A (T / 2, θ))
    (hInverse : ∀ side : Bool,
      ∀ᶠ p in 𝓝 (n04bRootCutRadius T, θ),
        K.inverseChart z (piece side) p =
          X (n04bSignedTravel T (if side then -1 else 1) n04bRootTravel p))
    (hHeight : ∀ side : Bool,
      ∀ᶠ p in 𝓝 (n04bRootCutRadius T, θ),
        K.height z (piece side) (K.inverseChart z (piece side) p) =
          n04bRootHeightInTravel T (if side then -1 else 1) A p)
    (u : PolarPoint → ℝ) (hu : ContDiff ℝ ∞ u) :
    canonicalHeight S K z (piece true) u (n04bRootCutRadius T, θ) =
        canonicalHeight S K z (piece false) u (n04bRootCutRadius T, θ) ∧
      radialPartial (canonicalHeight S K z (piece true) u) (n04bRootCutRadius T, θ) =
        -radialPartial (canonicalHeight S K z (piece false) u) (n04bRootCutRadius T, θ) -
          canonicalHeight S K z (piece false) u (n04bRootCutRadius T, θ) /
            (2 * n04bRootCutRadius T) := by
  have he (side : Bool) :
      canonicalHeight S K z (piece side) u =ᶠ[𝓝 (n04bRootCutRadius T, θ)]
        n04bRootUnknown T (if side then -1 else 1) X A u := by
    filter_upwards [hInverse side, hHeight side] with p hi hh
    unfold canonicalHeight
    rw [hh, hi]
    rfl
  have hv (side : Bool) := (he side).self_of_nhds
  have hd (side : Bool) :
      radialPartial (canonicalHeight S K z (piece side) u) (n04bRootCutRadius T, θ) =
        radialPartial (n04bRootUnknown T (if side then -1 else 1) X A u)
          (n04bRootCutRadius T, θ) := by
    unfold radialPartial
    rw [(he side).fderiv_eq]
  simpa [hv true, hv false, hd true, hd false] using
    (n04b_root_unknown_transmission hT θ X A u hX hA hA0
      (hu.differentiable (by simp) (X (T / 2, θ))))

end ContinuousFlexibility.Analysis
