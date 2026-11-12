import ContinuousFlexibility.Analysis.RootScaledInverseCoordinate
import ContinuousFlexibility.Analysis.RootChartSymmetry

/-!
# Reflection of the same controlled inverse after root scaling

The parameter rescaling commutes with the actual ODE reflection. The
chosen family is unchanged, and the true endpoint inverse supplies the
simultaneous reflection of its root parameter and angular coordinate.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

theorem rootScaledInverseCoordinate_reflect
    {d c : PolarPoint → ℝ} {δ : ℝ}
    {Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ} {h : ℝ → ℝ}
    (hd : ContDiff ℝ ∞ d) (hc : ContDiff ℝ ∞ c)
    (hdperiod : ∀ r, Function.Periodic (fun θ => d (r, θ)) Real.pi)
    (hcperiod : ∀ r, Function.Periodic (fun θ => c (r, θ)) Real.pi)
    (hdodd : ∀ r θ, d (r, -θ) = -d (r, θ))
    (hceven : ∀ r θ, c (r, -θ) = c (r, θ))
    (hΘ : N04FlowEquations (rootRescaledField d c δ) Θ)
    (hhodd : ∀ θ, h (-θ) = -h θ) (τ x ζ θ : ℝ) :
    rootScaledInverseCoordinate Θ h τ (x, -ζ, -θ) =
      -rootScaledInverseCoordinate Θ h τ (x, ζ, θ) := by
  let Φ := rootFlowParameterScale Θ τ
  let d' := rootParameterScaledDrift d δ
  let c' := rootParameterScaledSpeed c δ τ
  have hregular := contDiff_rootParameterScaledFields hd hc δ τ
  have hperiod := periodic_rootParameterScaledFields hdperiod hcperiod δ τ
  have hd' (r η : ℝ) : d' (r, -η) = -d' (r, η) := by
    change δ * d (δ * r, -η) = -(δ * d (δ * r, η))
    rw [hdodd, mul_neg]
  have hc' (r η : ℝ) : c' (r, -η) = c' (r, η) := by
    change (δ * τ) * c (δ * r, -η) = (δ * τ) * c (δ * r, η)
    rw [hceven]
  have hΦ : N04FlowEquations (rootRegularizedField d' c') Φ :=
    rootFlowParameterScale_equations hΘ τ
  have hF : ContDiff ℝ ∞ (rootRegularizedField d' c') :=
    contDiff_rootRegularizedField hregular.1 hregular.2
  have hFp := rootRegularizedField_periodic hperiod.1 hperiod.2
  have ht : (1 : ℝ) ∈ Icc 0 1 := ⟨zero_le_one, le_rfl⟩
  change rootInverseCoordinate Φ h (x, -ζ, -θ) = -rootInverseCoordinate Φ h (x, ζ, θ)
  exact rootInverseCoordinate_reflect_of_rootFlow Real.pi_ne_zero
    hregular.1 hregular.2 hperiod.1 hperiod.2 hd' hc' hΦ.1 hΦ.2
    (n04Flow_contDiff_slice hF hFp hΦ ht)
    (n04Flow_angular_deriv_pos hF hFp hΦ ht)
    (fun p η => n04Flow_period_add hF hFp hΦ p η ht) hhodd x ζ θ

end ContinuousFlexibility.Analysis
