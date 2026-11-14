module

public import ContinuousFlexibility.Analysis.RootChartExtensionGeometry
public import ContinuousFlexibility.Analysis.N04FlowInverseGeometry

/-!
# The reciprocal determinant of the same unit root chart

The existing root determinant identity converts the reciprocal odd
coefficient bound and the actual angular label lower bound into a
reciprocal Jacobian bound. This part uses only already available root
flow and chart APIs; the actual atlas material producer supplies its
component data separately.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

private theorem rootJacobian_inverse_le_of_odd_inverse
    {χ a M : ℝ} (hχ : 0 < χ) (ha : (1 / 4 : ℝ) ≤ a)
    (hM : 1 ≤ M) (hinverse : χ⁻¹ ≤ M) :
    (((3 / 2 : ℝ) * χ) ^ (2 / 3 : ℝ) * a)⁻¹ ≤ 4 * M := by
  have hc : 0 < (3 / 2 : ℝ) * χ := mul_pos (by norm_num) hχ
  have hcinv : ((3 / 2 : ℝ) * χ)⁻¹ ≤ M :=
    (inv_anti₀ hχ (by nlinarith only [hχ])).trans hinverse
  have hr : (((3 / 2 : ℝ) * χ) ^ (2 / 3 : ℝ))⁻¹ ≤ M := by
    rw [← Real.inv_rpow hc.le]
    exact (Real.rpow_le_rpow (inv_nonneg.mpr hc.le) hcinv
      (by norm_num : (0 : ℝ) ≤ 2 / 3)).trans
      (Real.rpow_le_self_of_one_le hM (by norm_num : (2 / 3 : ℝ) ≤ 1))
  have hai : a⁻¹ ≤ 4 := by
    have hh := inv_anti₀ (by norm_num : (0 : ℝ) < 1 / 4) ha
    norm_num at hh
    exact hh
  rw [mul_inv_rev]
  exact mul_le_mul hai hr
    (inv_nonneg.mpr (Real.rpow_nonneg hc.le _)) (by norm_num)

/-- The same unit root coordinate has reciprocal determinant at most four
 times the supplied reciprocal odd-coefficient envelope. -/
theorem n04Realization_rootUnit_jacobian_cost
    {d c : PolarPoint → ℝ} {Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ}
    {l : ℝ → ℝ} {θ M : ℝ}
    (hd : ContDiff ℝ ∞ d) (hc : ContDiff ℝ ∞ c)
    (hdperiod : ∀ x, Function.Periodic (fun η => d (x, η)) Real.pi)
    (hcperiod : ∀ x, Function.Periodic (fun η => c (x, η)) Real.pi)
    (hΘ : N04FlowEquations (rootRegularizedField d c) Θ)
    (hl : ContDiff ℝ ∞ l) (hlperiod : ∀ η, l (η + Real.pi) = l η + Real.pi)
    (hlower : (1 / 4 : ℝ) ≤ deriv l θ) (hM : 1 ≤ M)
    (hχ : 0 < extendedRootOddCoefficient (rootInverseCoordinate Θ l) (0, θ))
    (hinverse : (extendedRootOddCoefficient (rootInverseCoordinate Θ l) (0, θ))⁻¹ ≤ M) :
    let G : ℝ × ℝ × ℝ → ℝ := rootInverseCoordinate Θ l
    ContDiffAt ℝ ∞ (extendedRootEvenOddChart G) (0, θ) ∧
      0 < planeJacobian (extendedRootEvenOddChart G) (0, θ) ∧
      (planeJacobian (extendedRootEvenOddChart G) (0, θ))⁻¹ ≤ 4 * M := by
  let G : ℝ × ℝ × ℝ → ℝ := rootInverseCoordinate Θ l
  have hfield := contDiff_rootRegularizedField hd hc
  have hperiod := rootRegularizedField_periodic hdperiod hcperiod
  have ht : (1 : ℝ) ∈ Icc 0 1 := ⟨zero_le_one, le_rfl⟩
  have hEndpoint : ContDiff ℝ ∞ (fun q : (ℝ × ℝ) × ℝ => Θ q.1 1 q.2) :=
    n04Flow_contDiff_slice hfield hperiod hΘ ht
  have hpositive : ∀ p η, 0 < deriv (fun ζ => Θ p 1 ζ) η :=
    fun p η => n04Flow_angular_deriv_pos hfield hperiod hΘ ht p η
  have hEndpointPeriod : ∀ p η, Θ p 1 (η + Real.pi) = Θ p 1 η + Real.pi :=
    fun p η => n04Flow_period_add hfield hperiod hΘ p η ht
  have hG : ContDiff ℝ ∞ G :=
    contDiff_rootInverseCoordinate Real.pi_ne_zero hEndpoint hpositive hEndpointPeriod hl
  have hGperiod : ∀ x ζ η, G (x, ζ, η + Real.pi) = G (x, ζ, η) + Real.pi :=
    rootInverseCoordinate_period_add Real.pi_ne_zero hEndpoint hpositive hEndpointPeriod hlperiod
  have hχperiod : ∀ r, 0 ≤ r →
      Function.Periodic (fun η => rootOddCoefficient G (r, η)) Real.pi :=
    fun r _ => rootOddCoefficient_periodic hGperiod r
  have hφperiod : ∀ r, 0 ≤ r → ∀ η,
      rootEven G (r, η + Real.pi) = rootEven G (r, η) + Real.pi :=
    fun r _ => rootEven_period_add hGperiod r
  have hzero : ∀ η, G (0, 0, η) = l η :=
    rootInverseCoordinate_zero Real.pi_ne_zero hΘ.1 hΘ.2 hEndpoint hEndpointPeriod
  have hχraw : 0 < rootOddCoefficient G (0, θ) :=
    lt_of_lt_of_eq hχ (extendedRootOddCoefficient_of_nonneg _ (p := (0, θ)) le_rfl)
  have hJ : planeJacobian (extendedRootEvenOddChart G) (0, θ) =
      ((3 / 2 : ℝ) * extendedRootOddCoefficient G (0, θ)) ^ (2 / 3 : ℝ) *
        deriv l θ := by
    rw [planeJacobian_extendedRootEvenOddChart_zero hG Real.pi_ne_zero
      hχperiod hφperiod hzero (hl.differentiable (by simp) θ).hasDerivAt hχraw.ne']
    simp only [rootRadialFactor, extendedRootOddCoefficient_of_nonneg G (p := (0, θ)) (le_refl (0 : ℝ))]
  refine ⟨contDiffAt_extendedRootEvenOddChart_of_ne_zero hG Real.pi_ne_zero
    hχperiod hφperiod hχ.ne', ?_, ?_⟩
  · rw [hJ]
    exact mul_pos (Real.rpow_pos_of_pos (mul_pos (by norm_num) hχ) _)
      (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 4) hlower)
  · rw [hJ]
    exact rootJacobian_inverse_le_of_odd_inverse hχ hlower hM hinverse

end ContinuousFlexibility.Analysis
