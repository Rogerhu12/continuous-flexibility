import ContinuousFlexibility.Analysis.RootScaledInverseCoordinate
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# The actual inverse sampled on a signed root curve

The parameter curve is only used continuously at x = 0. The inverse
itself is the genuine jointly smooth inverse of the controlled flow.
Both its right-inverse identity and its exact zero value follow from
that same supplied ODE family.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

def rootRescaledInverseSample
    (Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ) (κ : ℝ) (p : PolarPoint) : ℝ :=
  parameterizedCircleInverse (fun q : N04FlowPoint => Θ q.1 1 q.2)
    ((p.1, κ * p.1 ^ (3 / 2 : ℝ)), p.2)

theorem rootRescaledInverseSample_regular
    {d c : PolarPoint → ℝ} {δ : ℝ}
    {Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ}
    (hd : ContDiff ℝ ∞ d) (hc : ContDiff ℝ ∞ c)
    (hdperiod : ∀ r, Function.Periodic (fun θ => d (r, θ)) Real.pi)
    (hcperiod : ∀ r, Function.Periodic (fun θ => c (r, θ)) Real.pi)
    (hΘ : N04FlowEquations (rootRescaledField d c δ) Θ) (κ : ℝ) :
    Continuous (rootRescaledInverseSample Θ κ) ∧
      (∀ p : PolarPoint, Θ (p.1, κ * p.1 ^ (3 / 2 : ℝ)) 1
        (rootRescaledInverseSample Θ κ p) = p.2) ∧
      ∀ θ, rootRescaledInverseSample Θ κ (0, θ) = θ := by
  have hF := contDiff_rootRescaledField hd hc δ
  have hp := rootRescaledField_periodic hdperiod hcperiod δ
  have ht : (1 : ℝ) ∈ Icc 0 1 := ⟨zero_le_one, le_rfl⟩
  have hI := contDiff_n04FlowInverse hF hp hΘ ht
  have harg : Continuous (fun p : PolarPoint =>
      ((p.1, κ * p.1 ^ (3 / 2 : ℝ)), p.2)) :=
    (continuous_fst.prodMk (continuous_const.mul
      ((Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 3 / 2)).comp
        continuous_fst))).prodMk continuous_snd
  have hright (p : PolarPoint) : Θ (p.1, κ * p.1 ^ (3 / 2 : ℝ)) 1
      (rootRescaledInverseSample Θ κ p) = p.2 :=
    parameterizedCircleInverse_right_inverse Real.pi_ne_zero
      (n04Flow_contDiff_slice hF hp hΘ ht)
      (fun v θ => n04Flow_period_add hF hp hΘ v θ ht)
      ((p.1, κ * p.1 ^ (3 / 2 : ℝ)), p.2)
  refine ⟨hI.continuous.comp harg, hright, ?_⟩
  intro θ
  have hscaled := rootFlowParameterScale_equations hΘ (1 : ℝ)
  have hzero : Θ (0, 0) 1 (rootRescaledInverseSample Θ κ (0, θ)) =
      rootRescaledInverseSample Θ κ (0, θ) := by
    simpa only [rootFlowParameterScale, mul_zero] using
      rootRegularizedFlow_zero_parameters hscaled.1 hscaled.2
        (rootRescaledInverseSample Θ κ (0, θ)) ht
  have hr := hright (0, θ)
  change Θ (0, κ * (0 : ℝ) ^ (3 / 2 : ℝ)) 1
    (rootRescaledInverseSample Θ κ (0, θ)) = θ at hr
  rw [Real.zero_rpow (by norm_num : (3 / 2 : ℝ) ≠ 0), mul_zero] at hr
  exact hzero.symm.trans hr

theorem rootScaledInverseCoordinate_eq_signed_sample
    (Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ) (h : ℝ → ℝ)
    (τ σ : ℝ) (p : PolarPoint) :
    rootScaledInverseCoordinate Θ h τ (p.1, σ * p.1 ^ (3 / 2 : ℝ), p.2) =
      h (rootRescaledInverseSample Θ (σ * τ) p) := by
  rw [rootScaledInverseCoordinate_eq_normalizedArgument]
  simp only [Function.comp_apply, rootFlowNormalizedArgument_apply,
    rootRescaledInverseSample]
  rw [show τ * (σ * p.1 ^ (3 / 2 : ℝ)) =
    (σ * τ) * p.1 ^ (3 / 2 : ℝ) by ring]

end ContinuousFlexibility.Analysis
