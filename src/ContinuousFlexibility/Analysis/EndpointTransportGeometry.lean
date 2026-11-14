module

public import ContinuousFlexibility.Analysis.PositiveFiberClosedGeometry

/-!
# Actual whole-component transport geometry

The two scalar interpolations have positive true derivatives. Their
displayed triangular chart and its displayed inverse therefore supply
all open and closed geometry, symmetries, and genuine middle germs.
This is a new reconstruction after the workspace reset.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

structure WholeComponentTransportGeometry
    (τ σ : PolarPoint → PolarPoint) (l r c d J : ℝ) : Prop where
  smooth : ContDiff ℝ ∞ τ
  inverse_smooth : ContDiff ℝ ∞ σ
  left_inverse : Function.LeftInverse σ τ
  right_inverse : Function.RightInverse σ τ
  jacobian_lower : ∀ p, J ≤ planeJacobian τ p
  jacobian_positive : ∀ p, 0 < planeJacobian τ p
  bijOn : BijOn τ (Ioo l r ×ˢ (univ : Set ℝ)) (Ioo l r ×ˢ (univ : Set ℝ))
  maps_open : MapsTo τ (Ioo l r ×ˢ (univ : Set ℝ)) (Ioo l r ×ˢ (univ : Set ℝ))
  inverse_maps_open : MapsTo σ
    (Ioo l r ×ˢ (univ : Set ℝ)) (Ioo l r ×ˢ (univ : Set ℝ))
  maps_closed : MapsTo τ (Icc l r ×ˢ (univ : Set ℝ)) (Icc l r ×ˢ (univ : Set ℝ))
  inverse_maps_closed : MapsTo σ
    (Icc l r ×ˢ (univ : Set ℝ)) (Icc l r ×ˢ (univ : Set ℝ))
  period_add : ∀ p, τ (p + (0, Real.pi)) = τ p + (0, Real.pi)
  inverse_period_add : ∀ p, σ (p + (0, Real.pi)) = σ p + (0, Real.pi)
  reflect : ∀ p, τ (p.1, -p.2) = ((τ p).1, -(τ p).2)
  inverse_reflect : ∀ p, σ (p.1, -p.2) = ((σ p).1, -(σ p).2)
  middle_germ : ∀ x ∈ Icc c d, ∀ θ, τ =ᶠ[𝓝 (x, θ)] (id : PolarPoint → PolarPoint)
  inverse_middle_germ : ∀ x ∈ Icc c d, ∀ θ,
    σ =ᶠ[𝓝 (x, θ)] (id : PolarPoint → PolarPoint)
  boundary_inverse : ∀ p, CanonicalBoundaryInverseGerm τ σ p

theorem wholeComponentTransportGeometry_of_scalars
    {φ Y : PolarPoint → ℝ} {κ B l r c d : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hY : ContDiff ℝ ∞ Y) (hκ : 0 < κ) (hB : 0 < B)
    (hφLower : ∀ x θ, κ ≤ deriv (fun η => φ (x, η)) θ)
    (hYLower : ∀ x θ, B ≤ deriv (fun t => Y (t, θ)) x)
    (hφPeriod : ∀ x θ, φ (x, θ + Real.pi) = φ (x, θ) + Real.pi)
    (hφOdd : ∀ x θ, φ (x, -θ) = -φ (x, θ))
    (hYPeriod : ∀ x θ, Y (x, θ + Real.pi) = Y (x, θ))
    (hYEven : ∀ x θ, Y (x, -θ) = Y (x, θ))
    (hleft : ∀ θ, Y (l, θ) = l) (hright : ∀ θ, Y (r, θ) = r)
    (hφMiddle : ∀ x ∈ Icc c d, ∀ θ,
      φ =ᶠ[𝓝 (x, θ)] (Prod.snd : PolarPoint → ℝ))
    (hYMiddle : ∀ x ∈ Icc c d, ∀ θ,
      Y =ᶠ[𝓝 (x, θ)] (Prod.fst : PolarPoint → ℝ)) :
    WholeComponentTransportGeometry
      (positiveFiberChart φ Y) (positiveFiberChartInverse φ Y) l r c d (B * κ) := by
  let τ := positiveFiberChart φ Y
  let σ := positiveFiberChartInverse φ Y
  obtain ⟨hτ, hσ, hστ, hτσ, hJ⟩ :=
    positiveFiberChart_geometry hφ hY hκ hB Real.pi_ne_zero hφLower hYLower hφPeriod
  have hJpos (p : PolarPoint) : 0 < planeJacobian τ p :=
    (mul_pos hB hκ).trans_le (hJ p)
  have hbij := positiveFiberChart_bijOn_openStrip
    hφ hY hκ hB Real.pi_ne_zero hφLower hYLower hφPeriod hleft hright
  have hclosed := positiveFiberChart_maps_closedStrip (φ := φ) hY hB hYLower hleft hright
  have hperiod (p : PolarPoint) : τ (p + (0, Real.pi)) = τ p + (0, Real.pi) :=
    positiveFiberChart_period_add hφPeriod hYPeriod p
  have hreflect (p : PolarPoint) : τ (p.1, -p.2) = ((τ p).1, -(τ p).2) :=
    positiveFiberChart_reflect hφOdd hYEven p
  have hmiddle (x : ℝ) (hx : x ∈ Icc c d) (θ : ℝ) :
      τ =ᶠ[𝓝 (x, θ)] (id : PolarPoint → PolarPoint) := by
    filter_upwards [hφMiddle x hx θ, hYMiddle x hx θ] with p hpφ hpY
    change (Y (p.1, φ p), φ p) = p
    rw [hpφ]
    exact Prod.ext (by simpa only [Prod.eta] using hpY) rfl
  refine {
    smooth := hτ
    inverse_smooth := hσ
    left_inverse := hστ
    right_inverse := hτσ
    jacobian_lower := hJ
    jacobian_positive := hJpos
    bijOn := hbij
    maps_open := hbij.mapsTo
    inverse_maps_open := ?_
    maps_closed := hclosed.1
    inverse_maps_closed := hclosed.2
    period_add := hperiod
    inverse_period_add := ?_
    reflect := hreflect
    inverse_reflect := inverse_reflect_of_forward_reflect hστ hτσ hreflect
    middle_germ := hmiddle
    inverse_middle_germ := ?_
    boundary_inverse := fun p => canonicalBoundaryInverseGerm_of_global_leftInverse
      hτ.contDiffAt (hJpos p).ne' hστ }
  · intro p hp
    obtain ⟨q, hq, heq⟩ := hbij.surjOn hp
    rw [← heq, hστ]
    exact hq
  · intro p
    apply hστ.injective
    dsimp only [τ] at hperiod
    rw [hτσ, hperiod, hτσ]
  · intro x hx θ
    filter_upwards [hmiddle x hx θ] with p hp
    exact (congrArg σ hp.symm).trans (hστ p)

end ContinuousFlexibility.Analysis
