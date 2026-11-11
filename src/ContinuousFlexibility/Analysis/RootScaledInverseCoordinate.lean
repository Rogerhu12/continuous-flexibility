import ContinuousFlexibility.Analysis.RootInverseNormalizedBounds
import ContinuousFlexibility.Analysis.RootRescaledAngularControl
import ContinuousFlexibility.Analysis.RootPhysicalCharacteristicFlow
import ContinuousFlexibility.Analysis.ActualRootChart

/-!
# The exact normalized parameters of the actual root inverse

The controlled field scales both independent parameters by δ. A physical
root sample at distance δ x therefore uses normalized second parameter
± sqrt(δ) x^(3/2). Reparametrizing that actual flow gives a standard root
flow with coefficients δ d(δ x,θ) and δ τ c(δ x,θ). Its true inverse has
the negative forcing derivative at the root; negating that derivative
gives the positive odd coefficient when τ = sqrt(δ).
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

def rootParameterScaledDrift (d : PolarPoint → ℝ) (δ : ℝ) (p : PolarPoint) : ℝ :=
  δ * d (δ * p.1, p.2)

def rootParameterScaledSpeed (c : PolarPoint → ℝ) (δ τ : ℝ) (p : PolarPoint) : ℝ :=
  (δ * τ) * c (δ * p.1, p.2)

def rootFlowParameterScale
    (Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ) (τ : ℝ)
    (p : ℝ × ℝ) (t θ : ℝ) : ℝ :=
  Θ (p.1, τ * p.2) t θ

def rootScaledInverseCoordinate
    (Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ) (h : ℝ → ℝ) (τ : ℝ) :
    ℝ × ℝ × ℝ → ℝ :=
  rootInverseCoordinate (rootFlowParameterScale Θ τ) h

theorem contDiff_rootParameterScaledFields
    {d c : PolarPoint → ℝ} (hd : ContDiff ℝ ∞ d) (hc : ContDiff ℝ ∞ c)
    (δ τ : ℝ) :
    ContDiff ℝ ∞ (rootParameterScaledDrift d δ) ∧
      ContDiff ℝ ∞ (rootParameterScaledSpeed c δ τ) := by
  have harg : ContDiff ℝ ∞ (fun p : PolarPoint => (δ * p.1, p.2)) :=
    (contDiff_const.mul contDiff_fst).prodMk contDiff_snd
  exact ⟨contDiff_const.mul (hd.comp harg), contDiff_const.mul (hc.comp harg)⟩

theorem periodic_rootParameterScaledFields
    {d c : PolarPoint → ℝ} {T : ℝ}
    (hd : ∀ r, Function.Periodic (fun θ => d (r, θ)) T)
    (hc : ∀ r, Function.Periodic (fun θ => c (r, θ)) T) (δ τ : ℝ) :
    (∀ r, Function.Periodic (fun θ => rootParameterScaledDrift d δ (r, θ)) T) ∧
      (∀ r, Function.Periodic
        (fun θ => rootParameterScaledSpeed c δ τ (r, θ)) T) := by
  constructor
  · intro r θ
    change δ * d (δ * r, θ + T) = δ * d (δ * r, θ)
    rw [hd (δ * r) θ]
  · intro r θ
    change (δ * τ) * c (δ * r, θ + T) = (δ * τ) * c (δ * r, θ)
    rw [hc (δ * r) θ]

theorem rootRegularizedField_parameterScale
    (d c : PolarPoint → ℝ) (δ τ t : ℝ) (p : ℝ × ℝ) (θ : ℝ) :
    rootRegularizedField (rootParameterScaledDrift d δ)
        (rootParameterScaledSpeed c δ τ) (t, (p, θ)) =
      rootRescaledField d c δ (t, ((p.1, τ * p.2), θ)) := by
  simp only [rootRegularizedField, rootRescaledField, rootParameterScaledDrift,
    rootParameterScaledSpeed, mul_assoc]
  ring

/-- The normalized family solves the standard root equation exactly,
including both closed time endpoints. -/
theorem rootFlowParameterScale_equations
    {d c : PolarPoint → ℝ} {δ : ℝ}
    {Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ}
    (hΘ : N04FlowEquations (rootRescaledField d c δ) Θ) (τ : ℝ) :
    N04FlowEquations
      (rootRegularizedField (rootParameterScaledDrift d δ)
        (rootParameterScaledSpeed c δ τ)) (rootFlowParameterScale Θ τ) := by
  constructor
  · intro p θ
    exact hΘ.1 (p.1, τ * p.2) θ
  · intro p θ t ht
    simpa only [rootFlowParameterScale, rootRegularizedField_parameterScale] using
      hΘ.2 (p.1, τ * p.2) θ t ht

/-- Reparametrization commutes with the actual chosen angular inverse;
the two invFun expressions are the same one-dimensional function. -/
theorem rootScaledInverseCoordinate_eq_normalizedArgument
    (Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ) (h : ℝ → ℝ) (τ : ℝ) :
    rootScaledInverseCoordinate Θ h τ = h ∘
      ((parameterizedCircleInverse (fun q : N04FlowPoint => Θ q.1 1 q.2)) ∘
        rootFlowNormalizedArgument τ) := by
  funext q
  simp only [rootScaledInverseCoordinate, rootInverseCoordinate, Function.comp_apply,
    rootFlowNormalizedArgument_apply, parameterizedCircleInverse, rootFlowParameterScale]

theorem csBound_rootScaledInverseCoordinate
    (Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ) (h : ℝ → ℝ) (τ : ℝ)
    {s : ℕ} {U : Set (ℝ × ℝ × ℝ)} {M : ℝ}
    (hb : CSBound s U
      (h ∘ ((parameterizedCircleInverse (fun q : N04FlowPoint => Θ q.1 1 q.2)) ∘
        rootFlowNormalizedArgument τ)) M) :
    CSBound s U (rootScaledInverseCoordinate Θ h τ) M := by
  rw [rootScaledInverseCoordinate_eq_normalizedArgument]
  exact hb

/-- Smoothness and the lift law follow from the original actual ODE,
not from any regularity assumption on the chosen inverse. -/
theorem rootScaledInverseCoordinate_regular
    {d c : PolarPoint → ℝ} {δ : ℝ}
    {Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ} {h : ℝ → ℝ}
    (hd : ContDiff ℝ ∞ d) (hc : ContDiff ℝ ∞ c)
    (hdperiod : ∀ r, Function.Periodic (fun θ => d (r, θ)) Real.pi)
    (hcperiod : ∀ r, Function.Periodic (fun θ => c (r, θ)) Real.pi)
    (hΘ : N04FlowEquations (rootRescaledField d c δ) Θ)
    (hh : ContDiff ℝ ∞ h) (hhperiod : ∀ θ, h (θ + Real.pi) = h θ + Real.pi)
    (τ : ℝ) :
    ContDiff ℝ ∞ (rootScaledInverseCoordinate Θ h τ) ∧
      ∀ x ζ θ, rootScaledInverseCoordinate Θ h τ (x, ζ, θ + Real.pi) =
        rootScaledInverseCoordinate Θ h τ (x, ζ, θ) + Real.pi := by
  have hF := contDiff_rootRescaledField hd hc δ
  have hperiod := rootRescaledField_periodic hdperiod hcperiod δ
  have ht : (1 : ℝ) ∈ Icc 0 1 := ⟨zero_le_one, le_rfl⟩
  have hEndpoint := n04Flow_contDiff_slice hF hperiod hΘ ht
  have hpositive := n04Flow_angular_deriv_pos hF hperiod hΘ ht
  have hper := fun v θ => n04Flow_period_add hF hperiod hΘ v θ ht
  rw [rootScaledInverseCoordinate_eq_normalizedArgument]
  constructor
  · exact hh.comp ((contDiff_n04FlowInverse hF hperiod hΘ ht).comp
      (rootFlowNormalizedArgument τ).contDiff)
  · intro x ζ θ
    simp only [Function.comp_apply, rootFlowNormalizedArgument_apply]
    rw [parameterizedCircleInverse_period_add Real.pi_ne_zero hEndpoint
      (fun q => hpositive q.1 q.2) hper (x, τ * ζ) θ, hhperiod]

/-- Both signs of the physical characteristic use the same common
parameter box; the signed contraction is ± sqrt(δ). -/
theorem abs_signed_sqrt_le_one {δ η : ℝ} (hδ : 0 ≤ δ) (hδone : δ ≤ 1)
    (hη : η = 1 ∨ η = -1) : |η * Real.sqrt δ| ≤ 1 := by
  have hs : 0 ≤ Real.sqrt δ := Real.sqrt_nonneg δ
  have hsone : Real.sqrt δ ≤ 1 := by nlinarith [Real.sq_sqrt hδ]
  rcases hη with rfl | rfl <;>
    simpa only [one_mul, neg_one_mul, abs_neg, abs_of_nonneg hs] using hsone

theorem rootScaled_physical_parameter {δ x : ℝ} (hδ : 0 ≤ δ) (hx : 0 ≤ x)
    (η : ℝ) :
    δ * ((η * Real.sqrt δ) * x ^ (3 / 2 : ℝ)) =
      η * (δ * x) ^ (3 / 2 : ℝ) := by
  rw [rpow_three_halves_eq_mul_sqrt hx,
    rpow_three_halves_eq_mul_sqrt (mul_nonneg hδ hx), Real.sqrt_mul hδ]
  ring

/-- The zero-section and the signed odd root coefficient come from the
actual ODE and its actual inverse, without an assumed parameter jet. -/
theorem rootScaledInverseCoordinate_zero_and_odd
    {d c : PolarPoint → ℝ} {δ : ℝ}
    {Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ} {h : ℝ → ℝ}
    (hd : ContDiff ℝ ∞ d) (hc : ContDiff ℝ ∞ c)
    (hdperiod : ∀ r, Function.Periodic (fun θ => d (r, θ)) Real.pi)
    (hcperiod : ∀ r, Function.Periodic (fun θ => c (r, θ)) Real.pi)
    (hΘ : N04FlowEquations (rootRescaledField d c δ) Θ)
    (hh : ContDiff ℝ ∞ h) (τ θ : ℝ) :
    rootScaledInverseCoordinate Θ h τ (0, 0, θ) = h θ ∧
      rootOddCoefficient (rootScaledInverseCoordinate Θ h τ) (0, θ) =
        ((2 : ℝ) / 3) * δ * τ * c (0, θ) * deriv h θ := by
  let Φ := rootFlowParameterScale Θ τ
  let d' := rootParameterScaledDrift d δ
  let c' := rootParameterScaledSpeed c δ τ
  have hregular := contDiff_rootParameterScaledFields hd hc δ τ
  have hperiod := periodic_rootParameterScaledFields hdperiod hcperiod δ τ
  have hΦ : N04FlowEquations (rootRegularizedField d' c') Φ :=
    rootFlowParameterScale_equations hΘ τ
  have hF : ContDiff ℝ ∞ (rootRegularizedField d' c') :=
    contDiff_rootRegularizedField hregular.1 hregular.2
  have hFp := rootRegularizedField_periodic hperiod.1 hperiod.2
  have ht : (1 : ℝ) ∈ Icc 0 1 := ⟨zero_le_one, le_rfl⟩
  have hEndpoint := n04Flow_contDiff_slice hF hFp hΦ ht
  have hpositive := n04Flow_angular_deriv_pos hF hFp hΦ ht
  have hflowperiod := fun p θ => n04Flow_period_add hF hFp hΦ p θ ht
  constructor
  · exact rootInverseCoordinate_zero Real.pi_ne_zero hΦ.1 hΦ.2 hEndpoint hflowperiod θ
  · have he := rootOddCoefficient_rootInverseCoordinate_zero Real.pi_ne_zero hregular.2
      hΦ.1 hΦ.2 (n04Flow_joint_continuousOn hF hFp hΦ)
      hEndpoint hpositive hflowperiod hh θ
    change rootOddCoefficient (rootInverseCoordinate Φ h) (0, θ) = _
    rw [he]
    simp only [c', rootParameterScaledSpeed, mul_zero]
    ring

/-- A state-independent positive speed and angular lower bound give a
state-independent positive root coefficient after the exact rescaling. -/
theorem rootScaledInverseCoordinate_odd_lower
    {d c : PolarPoint → ℝ} {δ κ λ : ℝ}
    {Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ} {h : ℝ → ℝ}
    (hd : ContDiff ℝ ∞ d) (hc : ContDiff ℝ ∞ c)
    (hdperiod : ∀ r, Function.Periodic (fun θ => d (r, θ)) Real.pi)
    (hcperiod : ∀ r, Function.Periodic (fun θ => c (r, θ)) Real.pi)
    (hΘ : N04FlowEquations (rootRescaledField d c δ) Θ)
    (hh : ContDiff ℝ ∞ h) (hδ : 0 ≤ δ) (hκ : 0 ≤ κ) (hλ : 0 ≤ λ)
    (θ : ℝ) (hcθ : κ ≤ c (0, θ)) (hhθ : λ ≤ deriv h θ) :
    ((2 : ℝ) / 3) * δ * Real.sqrt δ * κ * λ ≤
      rootOddCoefficient (rootScaledInverseCoordinate Θ h (Real.sqrt δ)) (0, θ) := by
  rw [(rootScaledInverseCoordinate_zero_and_odd hd hc hdperiod hcperiod hΘ hh
    (Real.sqrt δ) θ).2]
  have hb := mul_le_mul_of_nonneg_left
    (mul_le_mul hcθ hhθ hλ (hκ.trans hcθ))
    (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2 / 3) hδ)
      (Real.sqrt_nonneg δ))
  simpa only [mul_assoc] using hb

/-- The canonical radial scale contains exactly one power of δ after
the root exponent. The signed forcing derivative has already been
negated in rootOddCoefficient. -/
theorem rootScaledInverseCoordinate_radialFactor_zero
    {d c : PolarPoint → ℝ} {δ : ℝ}
    {Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ} {h : ℝ → ℝ}
    (hd : ContDiff ℝ ∞ d) (hc : ContDiff ℝ ∞ c)
    (hdperiod : ∀ r, Function.Periodic (fun θ => d (r, θ)) Real.pi)
    (hcperiod : ∀ r, Function.Periodic (fun θ => c (r, θ)) Real.pi)
    (hΘ : N04FlowEquations (rootRescaledField d c δ) Θ)
    (hh : ContDiff ℝ ∞ h) (hδ : 0 ≤ δ) (θ : ℝ)
    (hcθ : 0 ≤ c (0, θ)) (hhθ : 0 ≤ deriv h θ) :
    rootRadialFactor (rootScaledInverseCoordinate Θ h (Real.sqrt δ)) (0, θ) =
      δ * (c (0, θ) * deriv h θ) ^ (2 / 3 : ℝ) := by
  rw [rootRadialFactor,
    (rootScaledInverseCoordinate_zero_and_odd hd hc hdperiod hcperiod hΘ hh
      (Real.sqrt δ) θ).2]
  have he : ((3 : ℝ) / 2) *
      (((2 : ℝ) / 3) * δ * Real.sqrt δ * c (0, θ) * deriv h θ) =
      δ ^ (3 / 2 : ℝ) * (c (0, θ) * deriv h θ) := by
    rw [rpow_three_halves_eq_mul_sqrt hδ]
    ring
  rw [he, Real.mul_rpow (Real.rpow_nonneg hδ _) (mul_nonneg hcθ hhθ),
    ← Real.rpow_mul hδ, show (3 / 2 : ℝ) * (2 / 3 : ℝ) = 1 by norm_num,
    Real.rpow_one]

end ContinuousFlexibility.Analysis
