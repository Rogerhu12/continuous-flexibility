import ContinuousFlexibility.Analysis.N04bRootFlowContinuity
import ContinuousFlexibility.Analysis.RootChartSymmetry

/-!
# One actual smooth root function for both physical characteristic families

The actual stored flow is identified with the regularized Picard family.
Reflection uniqueness identifies the opposite characteristic family with
the opposite independent-root parameter of that same family. Its genuine
normalized inverse therefore supplies a single smooth G for both physical
footpoints, with the exact boundary value and divided odd coefficient.

The structure below packages conclusions of this construction. It is not
an additional hypothesis in N01, N03 or the raw field realization.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-- Proven output of the actual root-flow construction. -/
structure N04bRootCoordinateProperties
    (d c₀ : PolarPoint → ℝ) (hL : ℝ → ℝ) (Φ : ℝ → ℝ → ℝ)
    (R σ : ℝ) (G : ℝ × ℝ × ℝ → ℝ) : Prop where
  label_smooth : ContDiff ℝ ∞ hL
  label_positive : ∀ θ, 0 < deriv hL θ
  label_period : ∀ θ, hL (θ + Real.pi) = hL θ + Real.pi
  label_odd : ∀ θ, hL (-θ) = -hL θ
  smooth : ContDiff ℝ ∞ G
  zero_section : ∀ θ, G (0, 0, θ) = hL θ
  period : ∀ x ζ θ, G (x, ζ, θ + Real.pi) = G (x, ζ, θ) + Real.pi
  reflection : ∀ x ζ θ, G (x, -ζ, -θ) = -G (x, ζ, θ)
  odd_zero : ∀ θ, rootOddCoefficient G (0, θ) =
    ((2 : ℝ) / 3) * c₀ (0, θ) * deriv hL θ
  odd_positive : ∀ θ, 0 < rootOddCoefficient G (0, θ)
  stored_footpoint : ∀ x ∈ Icc (0 : ℝ) R, ∀ θ,
    hL (Function.invFun (fun η => Φ η x) θ) =
      rootCharacteristicCoordinate G σ (x, θ)
  reflected_footpoint : ∀ x ∈ Icc (0 : ℝ) R, ∀ θ,
    hL (Function.invFun (fun η => -Φ (-η) x) θ) =
      rootCharacteristicCoordinate G (-σ) (x, θ)
  angular_positive : ∀ s x θ : ℝ, 0 < x →
    0 < angularPartial (rootCharacteristicCoordinate G s) (x, θ)
  transport : ∀ s x θ : ℝ, 0 < x →
    radialPartial (rootCharacteristicCoordinate G s) (x, θ) =
      -rootPhysicalSpeed d c₀ s (x, θ) *
        angularPartial (rootCharacteristicCoordinate G s) (x, θ)

/-- Construct the common smooth root function from the actual stored
root equation. Angular positivity and both inverse-footpoint identities
are conclusions of the true flow and its chosen inverse. -/
theorem n04b_exists_actual_root_coordinate
    {d c₀ : PolarPoint → ℝ} {R σ : ℝ} {Φ : ℝ → ℝ → ℝ} {hL : ℝ → ℝ}
    (hR : 0 < R)
    (hd : ContDiff ℝ ∞ d) (hc₀ : ContDiff ℝ ∞ c₀)
    (hdperiod : ∀ r, Function.Periodic (fun θ => d (r, θ)) Real.pi)
    (hc₀period : ∀ r, Function.Periodic (fun θ => c₀ (r, θ)) Real.pi)
    (hdodd : ∀ r θ, d (r, -θ) = -d (r, θ))
    (hc₀even : ∀ r θ, c₀ (r, -θ) = c₀ (r, θ))
    (hc₀pos : ∀ θ, 0 < c₀ (0, θ))
    (hΦinit : ∀ θ, Φ θ 0 = θ)
    (hΦcont : ∀ θ, ContinuousOn (Φ θ) (Icc (0 : ℝ) R))
    (hΦflow : ∀ θ r, r ∈ Ioo (0 : ℝ) R →
      HasDerivAt (Φ θ) (rootPhysicalSpeed d c₀ σ (r, Φ θ r)) r)
    (hhL : ContDiff ℝ ∞ hL) (hLpos : ∀ θ, 0 < deriv hL θ)
    (hLperiod : ∀ θ, hL (θ + Real.pi) = hL θ + Real.pi)
    (hLodd : ∀ θ, hL (-θ) = -hL θ) :
    ∃ G : ℝ × ℝ × ℝ → ℝ, N04bRootCoordinateProperties d c₀ hL Φ R σ G := by
  obtain ⟨Θ, hi, hf, hΘ, hEndpoint, hpositive, hperiod, heq⟩ :=
    n04b_exists_complete_rootFlow_identification hR Real.pi_ne_zero
      hd hc₀ hdperiod hc₀period hΦinit hΦcont hΦflow
  let G : ℝ × ℝ × ℝ → ℝ := rootInverseCoordinate Θ hL
  have hG : ContDiff ℝ ∞ G :=
    contDiff_rootInverseCoordinate Real.pi_ne_zero hEndpoint hpositive hperiod hhL
  have hodd (θ : ℝ) : rootOddCoefficient G (0, θ) =
      ((2 : ℝ) / 3) * c₀ (0, θ) * deriv hL θ :=
    rootOddCoefficient_rootInverseCoordinate_zero Real.pi_ne_zero hc₀
      hi hf hΘ hEndpoint hpositive hperiod hhL θ
  have hreflected (x : ℝ) (hx : x ∈ Icc (0 : ℝ) R) (θ : ℝ) :
      -Φ (-θ) x = Θ (x, (-σ) * x ^ (3 / 2 : ℝ)) 1 θ := by
    rw [heq x hx (-θ)]
    simpa only [neg_neg, neg_mul] using
      (rootRegularizedFlow_reflect Real.pi_ne_zero hd hc₀ hdperiod hc₀period
        hdodd hc₀even hi hf x (σ * x ^ (3 / 2 : ℝ)) (-θ)
        (show (1 : ℝ) ∈ Icc 0 1 from ⟨zero_le_one, le_rfl⟩)).symm
  refine ⟨G, {
    label_smooth := hhL
    label_positive := hLpos
    label_period := hLperiod
    label_odd := hLodd
    smooth := hG
    zero_section := rootInverseCoordinate_zero Real.pi_ne_zero hi hf hEndpoint hperiod
    period := rootInverseCoordinate_period_add Real.pi_ne_zero
      hEndpoint hpositive hperiod hLperiod
    reflection := rootInverseCoordinate_reflect_of_rootFlow Real.pi_ne_zero hd hc₀
      hdperiod hc₀period hdodd hc₀even hi hf hEndpoint hpositive hperiod hLodd
    odd_zero := hodd
    odd_positive := ?_
    stored_footpoint := ?_
    reflected_footpoint := ?_
    angular_positive := ?_
    transport := ?_ }⟩
  · intro θ
    rw [hodd θ]
    exact mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2 / 3) (hc₀pos θ)) (hLpos θ)
  · intro x hx θ
    change hL (Function.invFun (fun η => Φ η x) θ) =
      hL (Function.invFun (fun η => Θ (x, σ * x ^ (3 / 2 : ℝ)) 1 η) θ)
    rw [show (fun η => Φ η x) =
      (fun η => Θ (x, σ * x ^ (3 / 2 : ℝ)) 1 η) from funext (heq x hx)]
  · intro x hx θ
    change hL (Function.invFun (fun η => -Φ (-η) x) θ) =
      hL (Function.invFun (fun η => Θ (x, (-σ) * x ^ (3 / 2 : ℝ)) 1 η) θ)
    rw [show (fun η => -Φ (-η) x) =
      (fun η => Θ (x, (-σ) * x ^ (3 / 2 : ℝ)) 1 η) from funext (hreflected x hx)]
  · intro s x θ hx
    exact rootInverseCoordinate_characteristic_angularPartial_pos
      Real.pi_ne_zero hEndpoint hpositive hperiod hhL hLpos s hx θ
  · intro s x θ hx
    exact rootInverseCoordinate_characteristic_transport Real.pi_ne_zero hd hc₀
      hdperiod hc₀period hi hf hEndpoint hpositive hperiod hhL s hx θ

end ContinuousFlexibility.Analysis
