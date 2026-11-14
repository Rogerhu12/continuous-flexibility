module

public import ContinuousFlexibility.Analysis.RootScaledAngularBounds
public import ContinuousFlexibility.Analysis.RootSmoothHeight

/-!
# A true uniform Jacobian lower bound on the normalized root band

The same parameter-scaled flow satisfies the physical transport
equations. Its Jacobian is the angular product times the scaled speed
divided by the square root of the smooth radial factor. The apparent
sqrt(x) cancels exactly. Positive value bounds therefore give a lower
bound selected before the state, without a state-dependent collar.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

theorem rootScaledCharacteristic_transport
    {d c : PolarPoint → ℝ} {δ : ℝ}
    {Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ} {h : ℝ → ℝ}
    (hd : ContDiff ℝ ∞ d) (hc : ContDiff ℝ ∞ c)
    (hdperiod : ∀ r, Function.Periodic (fun θ => d (r, θ)) Real.pi)
    (hcperiod : ∀ r, Function.Periodic (fun θ => c (r, θ)) Real.pi)
    (hΘ : N04FlowEquations (rootRescaledField d c δ) Θ)
    (hh : ContDiff ℝ ∞ h) (τ σ : ℝ) {x : ℝ} (hx : 0 < x) (θ : ℝ) :
    radialPartial (rootCharacteristicCoordinate (rootScaledInverseCoordinate Θ h τ) σ) (x, θ) =
      -(δ * d (δ * x, θ) + σ * Real.sqrt x * ((δ * τ) * c (δ * x, θ))) *
        angularPartial (rootCharacteristicCoordinate (rootScaledInverseCoordinate Θ h τ) σ)
          (x, θ) := by
  let Φ := rootFlowParameterScale Θ τ
  let d' := rootParameterScaledDrift d δ
  let c' := rootParameterScaledSpeed c δ τ
  have hregular := contDiff_rootParameterScaledFields hd hc δ τ
  have hperiod := periodic_rootParameterScaledFields hdperiod hcperiod δ τ
  have hΦ : N04FlowEquations (rootRegularizedField d' c') Φ :=
    rootFlowParameterScale_equations hΘ τ
  have hF := contDiff_rootRegularizedField hregular.1 hregular.2
  have hFp := rootRegularizedField_periodic hperiod.1 hperiod.2
  have ht : (1 : ℝ) ∈ Icc 0 1 := ⟨zero_le_one, le_rfl⟩
  have hEndpoint := n04Flow_contDiff_slice hF hFp hΦ ht
  have hpositive := n04Flow_angular_deriv_pos hF hFp hΦ ht
  have hflowperiod := fun p φ => n04Flow_period_add hF hFp hΦ p φ ht
  simpa only [rootScaledInverseCoordinate, rootPhysicalSpeed,
    rootParameterScaledDrift, rootParameterScaledSpeed] using
    rootInverseCoordinate_characteristic_transport Real.pi_ne_zero
      hregular.1 hregular.2 hperiod.1 hperiod.2 hΦ.1 hΦ.2
      hEndpoint hpositive hflowperiod hh σ hx θ

/-- The radial square root is absent from the actual Jacobian formula. -/
theorem rootScaledJacobian_eq
    {d c : PolarPoint → ℝ} {δ τ Λ : ℝ}
    {Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ} {h : ℝ → ℝ}
    (hd : ContDiff ℝ ∞ d) (hc : ContDiff ℝ ∞ c)
    (hdperiod : ∀ r, Function.Periodic (fun θ => d (r, θ)) Real.pi)
    (hcperiod : ∀ r, Function.Periodic (fun θ => c (r, θ)) Real.pi)
    (hΘ : N04FlowEquations (rootRescaledField d c δ) Θ)
    (hcontrol : N04FlowAngularControl (rootRescaledField d c δ) Λ)
    (hh : ContDiff ℝ ∞ h) (hhperiod : ∀ θ, h (θ + Real.pi) = h θ + Real.pi)
    (hhbounds : ∀ θ, deriv h θ ∈ Icc (1 / 4 : ℝ) 4)
    (hτ : |τ| ≤ 1) {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1) (θ : ℝ)
    (hχ : 0 < extendedRootOddCoefficient (rootScaledInverseCoordinate Θ h τ) (x, θ)) :
    let G := rootScaledInverseCoordinate Θ h τ
    planeJacobian (extendedRootEvenOddChart G) (x, θ) =
      ((δ * τ) * c (δ * x, θ)) * rootAngularProduct G (x, θ) /
        Real.sqrt (extendedRootRadialFactor G (x, θ)) := by
  let G := rootScaledInverseCoordinate Θ h τ
  change planeJacobian (extendedRootEvenOddChart G) (x, θ) =
    ((δ * τ) * c (δ * x, θ)) * rootAngularProduct G (x, θ) /
      Real.sqrt (extendedRootRadialFactor G (x, θ))
  have hG := rootScaledInverseCoordinate_regular hd hc hdperiod hcperiod hΘ hh hhperiod τ
  have hχperiod := fun (r : ℝ) (_ : 0 ≤ r) => rootOddCoefficient_periodic hG.2 r
  have hφperiod := fun (r : ℝ) (_ : 0 ≤ r) η => rootEven_period_add hG.2 r η
  have hχraw : 0 < rootOddCoefficient G (x, θ) := by
    rw [← extendedRootOddCoefficient_of_nonneg G (p := (x, θ)) hx.1.le]
    exact hχ
  have hU := rootScaledCharacteristic_angularPartial_bounds hd hc hdperiod hcperiod
    hΘ hcontrol hh hhperiod hhbounds hτ (Or.inl rfl : (1 : ℝ) = 1 ∨ (1 : ℝ) = -1) hx θ
  have hV := rootScaledCharacteristic_angularPartial_bounds hd hc hdperiod hcperiod
    hΘ hcontrol hh hhperiod hhbounds hτ (Or.inr rfl : (-1 : ℝ) = 1 ∨ (-1 : ℝ) = -1) hx θ
  have hl : 0 < Real.exp (-Λ) / 4 := div_pos (Real.exp_pos _) (by norm_num)
  have hU0 := (hl.trans_le hU.1).ne'
  have hV0 := (hl.trans_le hV.1).ne'
  have hUr := rootScaledCharacteristic_transport hd hc hdperiod hcperiod hΘ hh τ 1 hx.1 θ
  have hVr := rootScaledCharacteristic_transport hd hc hdperiod hcperiod hΘ hh τ (-1) hx.1 θ
  have hUr' : radialPartial (rootCharacteristicCoordinate G 1) (x, θ) =
      -(δ * d (δ * x, θ) + Real.sqrt x * ((δ * τ) * c (δ * x, θ))) *
        angularPartial (rootCharacteristicCoordinate G 1) (x, θ) := by
    simpa only [one_mul] using hUr
  have hVr' : radialPartial (rootCharacteristicCoordinate G (-1)) (x, θ) =
      -(δ * d (δ * x, θ) - Real.sqrt x * ((δ * τ) * c (δ * x, θ))) *
        angularPartial (rootCharacteristicCoordinate G (-1)) (x, θ) := by
    simpa only [one_mul, neg_one_mul, neg_mul, sub_eq_add_neg] using hVr
  have he := rootHeightFactor_eq_characteristicFactor (fun _ => (1 : ℝ))
    hG.1 Real.pi_ne_zero hχperiod hφperiod (p := (x, θ)) hx.1 hχraw hUr' hVr' hU0 hV0
  have hB0 : rootAngularProduct G (x, θ) ≠ 0 := by
    rw [rootAngularProduct_eq_characteristicProduct hG.1 Real.pi_ne_zero
      hχperiod hφperiod (p := (x, θ)) hx.1]
    exact mul_ne_zero hU0 hV0
  have hJ : planeJacobian (extendedRootEvenOddChart G) (x, θ) =
      (Real.sqrt x * ((δ * τ) * c (δ * x, θ))) * extendedRootScale G (x, θ) *
        rootAngularProduct G (x, θ) := by
    apply (div_eq_iff hB0).mp
    simpa only [rootHeightFactor, one_mul] using he
  have hFpos : 0 < extendedRootRadialFactor G (x, θ) :=
    Real.rpow_pos_of_pos (mul_pos (by norm_num) hχ) _
  have hradial : (extendedRootEvenOddChart G (x, θ)).1 =
      x * extendedRootRadialFactor G (x, θ) := rfl
  rw [hJ, extendedRootScale, hradial, Real.sqrt_mul hx.1.le]
  field_simp [(Real.sqrt_pos.mpr hx.1).ne', (Real.sqrt_pos.mpr hFpos).ne']
  <;> ring

theorem rootScaledJacobian_uniform_lower
    {d c : PolarPoint → ℝ} {δ τ Λ κ uχ : ℝ}
    {Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ} {h : ℝ → ℝ}
    (hd : ContDiff ℝ ∞ d) (hc : ContDiff ℝ ∞ c)
    (hdperiod : ∀ r, Function.Periodic (fun θ => d (r, θ)) Real.pi)
    (hcperiod : ∀ r, Function.Periodic (fun θ => c (r, θ)) Real.pi)
    (hΘ : N04FlowEquations (rootRescaledField d c δ) Θ)
    (hcontrol : N04FlowAngularControl (rootRescaledField d c δ) Λ)
    (hh : ContDiff ℝ ∞ h) (hhperiod : ∀ θ, h (θ + Real.pi) = h θ + Real.pi)
    (hhbounds : ∀ θ, deriv h θ ∈ Icc (1 / 4 : ℝ) 4)
    (hδ : 0 < δ) (hτpos : 0 < τ) (hτ : |τ| ≤ 1) (hκ : 0 < κ)
    {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1) (θ : ℝ)
    (hcvalue : κ ≤ c (δ * x, θ))
    (hχ : 0 < extendedRootOddCoefficient (rootScaledInverseCoordinate Θ h τ) (x, θ))
    (hχupper : extendedRootOddCoefficient (rootScaledInverseCoordinate Θ h τ) (x, θ) ≤ uχ) :
    let J₀ := ((δ * τ) * κ) * (Real.exp (-Λ) / 4) ^ 2 /
      Real.sqrt (((3 / 2 : ℝ) * uχ) ^ (2 / 3 : ℝ))
    0 < J₀ ∧ J₀ ≤
      planeJacobian (extendedRootEvenOddChart (rootScaledInverseCoordinate Θ h τ)) (x, θ) := by
  let G := rootScaledInverseCoordinate Θ h τ
  have hfactor : 0 < extendedRootRadialFactor G (x, θ) :=
    Real.rpow_pos_of_pos (mul_pos (by norm_num) hχ) _
  have hupper : 0 < ((3 / 2 : ℝ) * uχ) ^ (2 / 3 : ℝ) :=
    Real.rpow_pos_of_pos (mul_pos (by norm_num) (hχ.trans_le hχupper)) _
  have hdenom : Real.sqrt (extendedRootRadialFactor G (x, θ)) ≤
      Real.sqrt (((3 / 2 : ℝ) * uχ) ^ (2 / 3 : ℝ)) := by
    apply Real.sqrt_le_sqrt
    exact Real.rpow_le_rpow (mul_nonneg (by norm_num) hχ.le)
      (mul_le_mul_of_nonneg_left hχupper (by norm_num)) (by norm_num)
  have hB := rootScaledAngularProduct_bounds hd hc hdperiod hcperiod
    hΘ hcontrol hh hhperiod hhbounds hτ hx θ
  have hnumpos : 0 < ((δ * τ) * κ) * (Real.exp (-Λ) / 4) ^ 2 :=
    mul_pos (mul_pos (mul_pos hδ hτpos) hκ)
      (pow_pos (div_pos (Real.exp_pos _) (by norm_num)) 2)
  have hnumerator : ((δ * τ) * κ) * (Real.exp (-Λ) / 4) ^ 2 ≤
      ((δ * τ) * c (δ * x, θ)) * rootAngularProduct G (x, θ) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hcvalue (mul_pos hδ hτpos).le)
      hB.1 (sq_nonneg _) (mul_nonneg (mul_pos hδ hτpos).le (hκ.le.trans hcvalue))
  refine ⟨div_pos hnumpos (Real.sqrt_pos.mpr hupper), ?_⟩
  calc
    _ ≤ ((δ * τ) * κ) * (Real.exp (-Λ) / 4) ^ 2 /
        Real.sqrt (extendedRootRadialFactor G (x, θ)) :=
      div_le_div_of_nonneg_left hnumpos.le (Real.sqrt_pos.mpr hfactor) hdenom
    _ ≤ ((δ * τ) * c (δ * x, θ)) * rootAngularProduct G (x, θ) /
        Real.sqrt (extendedRootRadialFactor G (x, θ)) :=
      div_le_div_of_nonneg_right hnumerator (Real.sqrt_nonneg _)
    _ = _ := (rootScaledJacobian_eq hd hc hdperiod hcperiod
      hΘ hcontrol hh hhperiod hhbounds hτ hx θ hχ).symm

end ContinuousFlexibility.Analysis
