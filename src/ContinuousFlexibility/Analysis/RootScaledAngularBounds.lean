import ContinuousFlexibility.Analysis.RootScaledInverseCoordinate
import ContinuousFlexibility.Analysis.RootAngularProduct
import ContinuousFlexibility.Analysis.RootChartSymmetry
import ContinuousFlexibility.Scalar.Conservation

/-!
# Uniform angular bounds for the same normalized root inverse

Only the actual angular Gronwall bound enters these constants. The
chosen flow and its parameter scale are unchanged. In particular the
two physical samples have uniformly positive angular derivatives, and
their product stays in a fixed positive interval throughout the root
strip. No higher inverse jet or new collar is assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

theorem rootScaledInverseCoordinate_angular_deriv_bounds
    {d c : PolarPoint → ℝ} {δ τ Λ : ℝ}
    {Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ} {h : ℝ → ℝ}
    (hd : ContDiff ℝ ∞ d) (hc : ContDiff ℝ ∞ c)
    (hdperiod : ∀ r, Function.Periodic (fun θ => d (r, θ)) Real.pi)
    (hcperiod : ∀ r, Function.Periodic (fun θ => c (r, θ)) Real.pi)
    (hΘ : N04FlowEquations (rootRescaledField d c δ) Θ)
    (hcontrol : N04FlowAngularControl (rootRescaledField d c δ) Λ)
    (hh : ContDiff ℝ ∞ h) (hhbounds : ∀ θ, deriv h θ ∈ Icc (1 / 4 : ℝ) 4)
    (hτ : |τ| ≤ 1) {x ζ : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1)
    (hζ : ζ ∈ Icc (-1 : ℝ) 1) (θ : ℝ) :
    deriv (fun η => rootScaledInverseCoordinate Θ h τ (x, ζ, η)) θ ∈
      Icc (Real.exp (-Λ) / 4) (4 * Real.exp Λ) := by
  let F : N04FlowPoint → ℝ := fun q => Θ q.1 1 q.2
  let v : ℝ × ℝ := (x, τ * ζ)
  let η := parameterizedCircleInverse F (v, θ)
  have hF := contDiff_rootRescaledField hd hc δ
  have hperiod := rootRescaledField_periodic hdperiod hcperiod δ
  have ht : (1 : ℝ) ∈ Icc 0 1 := ⟨zero_le_one, le_rfl⟩
  have hEndpoint := n04Flow_contDiff_slice hF hperiod hΘ ht
  have hpositive := n04Flow_angular_deriv_pos hF hperiod hΘ ht
  have hflowperiod := fun p φ => n04Flow_period_add hF hperiod hΘ p φ ht
  have hτζ : |τ * ζ| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_mul hτ (abs_le.mpr ⟨hζ.1, hζ.2⟩)
      (abs_nonneg ζ) zero_le_one).trans_eq (mul_one 1)
  have hv : v ∈ n04FlowParameterBox := ⟨hx, abs_le.mp hτζ⟩
  have hforward := n04Flow_angular_bounds hF hperiod hΘ hcontrol hv ht η
  have hdpos := hpositive v η
  have hinv : (deriv (fun φ => Θ v 1 φ) η)⁻¹ ∈
      Icc (Real.exp (-Λ)) (Real.exp Λ) := by
    constructor
    · simpa only [one_div, Real.exp_neg] using
        one_div_le_one_div_of_le hdpos hforward.2
    · simpa only [one_div, Real.exp_neg, inv_inv] using
        one_div_le_one_div_of_le (Real.exp_pos (-Λ)) hforward.1
  have hi := hasDerivAt_parameterizedCircleInverse Real.pi_ne_zero hEndpoint
    (fun q => hpositive q.1 q.2) hflowperiod v θ
  have hl := (hh.differentiable (by simp) η).hasDerivAt
  have hcomp := hl.comp θ hi
  have he : h ∘ (fun φ => parameterizedCircleInverse F (v, φ)) =
      (fun φ => rootScaledInverseCoordinate Θ h τ (x, ζ, φ)) := by
    funext φ
    rw [rootScaledInverseCoordinate_eq_normalizedArgument]
    rfl
  rw [he] at hcomp
  rw [hcomp.deriv]
  have hk := hhbounds η
  constructor
  · have hm := mul_le_mul hk.1 hinv.1 (Real.exp_pos (-Λ)).le
      ((by norm_num : (0 : ℝ) ≤ 1 / 4).trans hk.1)
    exact (by ring : Real.exp (-Λ) / 4 = (1 / 4 : ℝ) * Real.exp (-Λ)).trans_le hm
  · exact mul_le_mul hk.2 hinv.2 (inv_pos.mpr hdpos).le (by norm_num)

theorem rootScaledCharacteristic_angularPartial_bounds
    {d c : PolarPoint → ℝ} {δ τ Λ : ℝ}
    {Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ} {h : ℝ → ℝ}
    (hd : ContDiff ℝ ∞ d) (hc : ContDiff ℝ ∞ c)
    (hdperiod : ∀ r, Function.Periodic (fun θ => d (r, θ)) Real.pi)
    (hcperiod : ∀ r, Function.Periodic (fun θ => c (r, θ)) Real.pi)
    (hΘ : N04FlowEquations (rootRescaledField d c δ) Θ)
    (hcontrol : N04FlowAngularControl (rootRescaledField d c δ) Λ)
    (hh : ContDiff ℝ ∞ h) (hhperiod : ∀ θ, h (θ + Real.pi) = h θ + Real.pi)
    (hhbounds : ∀ θ, deriv h θ ∈ Icc (1 / 4 : ℝ) 4)
    (hτ : |τ| ≤ 1) {σ x : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hx : x ∈ Ioc (0 : ℝ) 1) (θ : ℝ) :
    angularPartial (rootCharacteristicCoordinate
        (rootScaledInverseCoordinate Θ h τ) σ) (x, θ) ∈
      Icc (Real.exp (-Λ) / 4) (4 * Real.exp Λ) := by
  have hp : 0 ≤ x ^ (3 / 2 : ℝ) := Real.rpow_nonneg hx.1.le _
  have hpone : x ^ (3 / 2 : ℝ) ≤ 1 :=
    (Real.rpow_le_self_of_le_one hx.1.le hx.2 (by norm_num)).trans hx.2
  have hζ : σ * x ^ (3 / 2 : ℝ) ∈ Icc (-1 : ℝ) 1 := by
    rcases hσ with rfl | rfl <;> simp only [one_mul, neg_one_mul]
    · exact ⟨(by linarith), hpone⟩
    · constructor <;> linarith
  have hG := (rootScaledInverseCoordinate_regular hd hc hdperiod hcperiod hΘ hh hhperiod τ).1
  have hs := hasDerivAt_angular_slice
    ((contDiffAt_rootCharacteristicCoordinate (σ := σ) (θ := θ) hG hx.1).differentiableAt
      (by simp))
  have hb := rootScaledInverseCoordinate_angular_deriv_bounds hd hc hdperiod hcperiod
    hΘ hcontrol hh hhbounds hτ ⟨by linarith [hx.1], hx.2⟩ hζ θ
  have he : (fun φ => rootCharacteristicCoordinate
      (rootScaledInverseCoordinate Θ h τ) σ (x, φ)) =
      (fun φ => rootScaledInverseCoordinate Θ h τ (x, σ * x ^ (3 / 2 : ℝ), φ)) := rfl
  rw [he] at hs
  rw [← hs.deriv]
  exact hb

theorem rootScaledAngularProduct_bounds
    {d c : PolarPoint → ℝ} {δ τ Λ : ℝ}
    {Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ} {h : ℝ → ℝ}
    (hd : ContDiff ℝ ∞ d) (hc : ContDiff ℝ ∞ c)
    (hdperiod : ∀ r, Function.Periodic (fun θ => d (r, θ)) Real.pi)
    (hcperiod : ∀ r, Function.Periodic (fun θ => c (r, θ)) Real.pi)
    (hΘ : N04FlowEquations (rootRescaledField d c δ) Θ)
    (hcontrol : N04FlowAngularControl (rootRescaledField d c δ) Λ)
    (hh : ContDiff ℝ ∞ h) (hhperiod : ∀ θ, h (θ + Real.pi) = h θ + Real.pi)
    (hhbounds : ∀ θ, deriv h θ ∈ Icc (1 / 4 : ℝ) 4)
    (hτ : |τ| ≤ 1) {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1) (θ : ℝ) :
    rootAngularProduct (rootScaledInverseCoordinate Θ h τ) (x, θ) ∈
      Icc ((Real.exp (-Λ) / 4) ^ 2) ((4 * Real.exp Λ) ^ 2) := by
  have hG := rootScaledInverseCoordinate_regular hd hc hdperiod hcperiod hΘ hh hhperiod τ
  have hχperiod := fun (r : ℝ) (_ : 0 ≤ r) => rootOddCoefficient_periodic hG.2 r
  have hφperiod := fun (r : ℝ) (_ : 0 ≤ r) η => rootEven_period_add hG.2 r η
  have hu := rootScaledCharacteristic_angularPartial_bounds hd hc hdperiod hcperiod
    hΘ hcontrol hh hhperiod hhbounds hτ (Or.inl rfl : (1 : ℝ) = 1 ∨ (1 : ℝ) = -1) hx θ
  have hv := rootScaledCharacteristic_angularPartial_bounds hd hc hdperiod hcperiod
    hΘ hcontrol hh hhperiod hhbounds hτ (Or.inr rfl : (-1 : ℝ) = 1 ∨ (-1 : ℝ) = -1) hx θ
  have hl : 0 ≤ Real.exp (-Λ) / 4 := div_nonneg (Real.exp_pos _).le (by norm_num)
  have hu0 : 0 ≤ 4 * Real.exp Λ := mul_nonneg (by norm_num) (Real.exp_pos _).le
  rw [rootAngularProduct_eq_characteristicProduct hG.1 Real.pi_ne_zero hχperiod hφperiod
    (p := (x, θ)) hx.1]
  simpa only [Set.mem_Icc, pow_two] using
    And.intro (mul_le_mul hu.1 hv.1 hl (hl.trans hu.1))
      (mul_le_mul hu.2 hv.2 (hl.trans hv.1) hu0)

end ContinuousFlexibility.Analysis
