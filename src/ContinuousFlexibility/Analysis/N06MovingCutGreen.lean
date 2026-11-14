module

public import ContinuousFlexibility.Analysis.N04bRootCutHeight
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Green cancellation on the actual moving travel cut

The physical cut is the inverse-chart curve `X (T / 2, θ)`.  The two
canonical pullbacks use the genuine signed travel maps and the root
height.  Their Green densities are computed from these functions, rather
than supplied as a matching condition.  The reference field and the
current test may use different inverse charts and different positive
travel densities.

This module has no canonical-atlas record among its inputs.  In particular
it does not identify the moving cut with a radial line or a radial graph.
The last two statements retain an arbitrary angular parametrization and
its signed derivative.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped ContDiff Topology BigOperators

set_option backward.isDefEq.respectTransparency false

/-- The actual value and normal derivative of the height quotient at the
common travel cut, for either sign of the travel coordinate. -/
theorem n06_rootUnknown_cut_firstJets
    {T : ℝ} (hT : 0 < T) (s θ : ℝ)
    (X : PolarPoint → PolarPoint) (A u : PolarPoint → ℝ)
    (hX : DifferentiableAt ℝ X (T / 2, θ))
    (hA : DifferentiableAt ℝ A (T / 2, θ))
    (hApos : 0 < A (T / 2, θ))
    (hu : DifferentiableAt ℝ u (X (T / 2, θ))) :
    n04bRootUnknown T s X A u (n04bRootCutRadius T, θ) =
        n04bRootGauge (n04bRootCutRadius T) *
          n04bTravelUnknown X A u (T / 2, θ) ∧
      radialPartial (n04bRootUnknown T s X A u) (n04bRootCutRadius T, θ) =
        (-n04bRootGauge (n04bRootCutRadius T) / (4 * n04bRootCutRadius T)) *
            n04bTravelUnknown X A u (T / 2, θ) +
          n04bRootGauge (n04bRootCutRadius T) * s *
            Real.sqrt (n04bRootCutRadius T) *
              radialPartial (n04bTravelUnknown X A u) (T / 2, θ) := by
  have hr := n04bRootCutRadius_pos hT
  have hp : ∀ᶠ p : PolarPoint in 𝓝 (n04bRootCutRadius T, θ), 0 < p.1 :=
    (isOpen_lt continuous_const continuous_fst).mem_nhds hr
  have he : n04bRootUnknown T s X A u =ᶠ[𝓝 (n04bRootCutRadius T, θ)]
      n04bGaugedTravel T s n04bRootTravel n04bRootGauge
        (n04bTravelUnknown X A u) := by
    filter_upwards [hp] with p hp
    exact n04bRootUnknown_eq_gauged T s X A u hp
  constructor
  · rw [he.self_of_nhds]
    simp only [n04bGaugedTravel, n04bSignedTravel, n04b_rootTravel_cut hT,
      sub_self, mul_zero, add_zero]
  · have hd :
        radialPartial (n04bRootUnknown T s X A u) (n04bRootCutRadius T, θ) =
          radialPartial (n04bGaugedTravel T s n04bRootTravel n04bRootGauge
            (n04bTravelUnknown X A u)) (n04bRootCutRadius T, θ) := by
      unfold radialPartial
      rw [he.fderiv_eq]
    exact hd.trans (n04b_radialPartial_gaugedTravel T s (n04bRootCutRadius T) θ
      (Real.sqrt (n04bRootCutRadius T))
      (-n04bRootGauge (n04bRootCutRadius T) / (4 * n04bRootCutRadius T))
      n04bRootTravel n04bRootGauge (n04bTravelUnknown X A u)
      (n04b_hasDerivAt_rootTravel hr) (n04b_hasDerivAt_rootGauge hr)
      (n04b_rootTravel_cut hT)
      (n04bTravelUnknown_differentiableAt hX hA hApos hu))

private theorem n06_rootGauge_sq_mul_sqrt {r : ℝ} (hr : 0 < r) :
    n04bRootGauge r ^ 2 * Real.sqrt r = 1 := by
  rw [n04b_rootGauge_eq_inv_sqrt_sqrt hr, inv_pow,
    Real.sq_sqrt (Real.sqrt_nonneg r)]
  exact inv_mul_cancel₀ (Real.sqrt_pos.2 hr).ne'

/-- The canonical boundary density of the reference field and current
physical test, using their actual inverse-chart height quotients. -/
def n06MovingCutGreenDensity (T s : ℝ)
    (X₀ X : PolarPoint → PolarPoint) (A₀ A u φ : PolarPoint → ℝ)
    (θ : ℝ) : ℝ :=
  n04bRootUnknown T s X A φ (n04bRootCutRadius T, θ) *
      radialPartial (n04bRootUnknown T s X₀ A₀ u) (n04bRootCutRadius T, θ) -
    n04bRootUnknown T s X₀ A₀ u (n04bRootCutRadius T, θ) *
      radialPartial (n04bRootUnknown T s X A φ) (n04bRootCutRadius T, θ)

/-- The root gauge cancels from the Green density.  The only orientation
factor is the sign of the genuine travel coordinate. -/
theorem n06_movingCut_green_density
    {T : ℝ} (hT : 0 < T) (s θ : ℝ)
    (X₀ X : PolarPoint → PolarPoint) (A₀ A u φ : PolarPoint → ℝ)
    (hX₀ : DifferentiableAt ℝ X₀ (T / 2, θ))
    (hA₀ : DifferentiableAt ℝ A₀ (T / 2, θ))
    (hA₀pos : 0 < A₀ (T / 2, θ))
    (hu : DifferentiableAt ℝ u (X₀ (T / 2, θ)))
    (hX : DifferentiableAt ℝ X (T / 2, θ))
    (hA : DifferentiableAt ℝ A (T / 2, θ))
    (hApos : 0 < A (T / 2, θ))
    (hφ : DifferentiableAt ℝ φ (X (T / 2, θ))) :
    n06MovingCutGreenDensity T s X₀ X A₀ A u φ θ =
      s * (n04bTravelUnknown X A φ (T / 2, θ) *
          radialPartial (n04bTravelUnknown X₀ A₀ u) (T / 2, θ) -
        n04bTravelUnknown X₀ A₀ u (T / 2, θ) *
          radialPartial (n04bTravelUnknown X A φ) (T / 2, θ)) := by
  obtain ⟨hU, hUr⟩ := n06_rootUnknown_cut_firstJets hT s θ X₀ A₀ u
    hX₀ hA₀ hA₀pos hu
  obtain ⟨hQ, hQr⟩ := n06_rootUnknown_cut_firstJets hT s θ X A φ
    hX hA hApos hφ
  unfold n06MovingCutGreenDensity
  rw [hU, hUr, hQ, hQr]
  calc
    _ = (n04bRootGauge (n04bRootCutRadius T) ^ 2 *
        Real.sqrt (n04bRootCutRadius T)) *
      (s * (n04bTravelUnknown X A φ (T / 2, θ) *
          radialPartial (n04bTravelUnknown X₀ A₀ u) (T / 2, θ) -
        n04bTravelUnknown X₀ A₀ u (T / 2, θ) *
          radialPartial (n04bTravelUnknown X A φ) (T / 2, θ))) := by ring
    _ = _ := by rw [n06_rootGauge_sq_mul_sqrt (n04bRootCutRadius_pos hT), one_mul]

/-- Both upper-endpoint boundary terms cancel on the moving physical cut.
No equality of physical radii or extra trace matching is assumed. -/
theorem n06_movingCut_green_cancel
    {T : ℝ} (hT : 0 < T) (θ : ℝ)
    (X₀ X : PolarPoint → PolarPoint) (A₀ A u φ : PolarPoint → ℝ)
    (hX₀ : DifferentiableAt ℝ X₀ (T / 2, θ))
    (hA₀ : DifferentiableAt ℝ A₀ (T / 2, θ))
    (hA₀pos : 0 < A₀ (T / 2, θ))
    (hu : DifferentiableAt ℝ u (X₀ (T / 2, θ)))
    (hX : DifferentiableAt ℝ X (T / 2, θ))
    (hA : DifferentiableAt ℝ A (T / 2, θ))
    (hApos : 0 < A (T / 2, θ))
    (hφ : DifferentiableAt ℝ φ (X (T / 2, θ))) :
    n06MovingCutGreenDensity T 1 X₀ X A₀ A u φ θ +
      n06MovingCutGreenDensity T (-1) X₀ X A₀ A u φ θ = 0 := by
  rw [n06_movingCut_green_density hT 1 θ X₀ X A₀ A u φ
      hX₀ hA₀ hA₀pos hu hX hA hApos hφ,
    n06_movingCut_green_density hT (-1) θ X₀ X A₀ A u φ
      hX₀ hA₀ hA₀pos hu hX hA hApos hφ]
  ring

/-- Reparametrizing the actual inverse-chart curve retains the signed
angular derivative; it does not require the curve to be a radial graph. -/
theorem n06_movingCut_reparametrized_green_cancel
    {T : ℝ} (hT : 0 < T) (β : ℝ → ℝ) (θ : ℝ)
    (X₀ X : PolarPoint → PolarPoint) (A₀ A u φ : PolarPoint → ℝ)
    (hX₀ : DifferentiableAt ℝ X₀ (T / 2, β θ))
    (hA₀ : DifferentiableAt ℝ A₀ (T / 2, β θ))
    (hA₀pos : 0 < A₀ (T / 2, β θ))
    (hu : DifferentiableAt ℝ u (X₀ (T / 2, β θ)))
    (hX : DifferentiableAt ℝ X (T / 2, β θ))
    (hA : DifferentiableAt ℝ A (T / 2, β θ))
    (hApos : 0 < A (T / 2, β θ))
    (hφ : DifferentiableAt ℝ φ (X (T / 2, β θ))) :
    deriv β θ * n06MovingCutGreenDensity T 1 X₀ X A₀ A u φ (β θ) +
      deriv β θ * n06MovingCutGreenDensity T (-1) X₀ X A₀ A u φ (β θ) = 0 := by
  rw [← mul_add, n06_movingCut_green_cancel hT (β θ) X₀ X A₀ A u φ
    hX₀ hA₀ hA₀pos hu hX hA hApos hφ, mul_zero]

/-- The actual boundary integrals cancel with the same angular
parametrization on both sides.  Taking `a = 0`, `b = π` gives the
half-period formula, and `b = 2 * π` gives the full-period formula. -/
theorem n06_movingCut_green_integrals_cancel
    {T : ℝ} (hT : 0 < T) (β : ℝ → ℝ) (a b : ℝ)
    (X₀ X : PolarPoint → PolarPoint) (A₀ A u φ : PolarPoint → ℝ)
    (hX₀ : ∀ θ, DifferentiableAt ℝ X₀ (T / 2, β θ))
    (hA₀ : ∀ θ, DifferentiableAt ℝ A₀ (T / 2, β θ))
    (hA₀pos : ∀ θ, 0 < A₀ (T / 2, β θ))
    (hu : ∀ θ, DifferentiableAt ℝ u (X₀ (T / 2, β θ)))
    (hX : ∀ θ, DifferentiableAt ℝ X (T / 2, β θ))
    (hA : ∀ θ, DifferentiableAt ℝ A (T / 2, β θ))
    (hApos : ∀ θ, 0 < A (T / 2, β θ))
    (hφ : ∀ θ, DifferentiableAt ℝ φ (X (T / 2, β θ))) :
    (∫ θ in a..b, deriv β θ *
      n06MovingCutGreenDensity T 1 X₀ X A₀ A u φ (β θ)) +
    (∫ θ in a..b, deriv β θ *
      n06MovingCutGreenDensity T (-1) X₀ X A₀ A u φ (β θ)) = 0 := by
  have he : (fun θ => deriv β θ *
      n06MovingCutGreenDensity T (-1) X₀ X A₀ A u φ (β θ)) =
      fun θ => -(deriv β θ * n06MovingCutGreenDensity T 1 X₀ X A₀ A u φ (β θ)) := by
    funext θ
    have h := n06_movingCut_reparametrized_green_cancel hT β θ X₀ X A₀ A u φ
      (hX₀ θ) (hA₀ θ) (hA₀pos θ) (hu θ) (hX θ) (hA θ) (hApos θ) (hφ θ)
    linarith
  rw [he, intervalIntegral.integral_neg]
  ring

end ContinuousFlexibility.Analysis
