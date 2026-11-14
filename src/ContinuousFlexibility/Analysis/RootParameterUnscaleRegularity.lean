module

public import ContinuousFlexibility.Analysis.RootPhysicalModelParameterUnscale
public import ContinuousFlexibility.Analysis.RootChartExtensionGeometry

/-!
# Actual regularity of the same root model at unit parameter scale

The unit-scale inverse coordinate is an explicit linear reparametrization
of the original chosen inverse. The true extended odd coefficient has the
same three-halves scaling at the root by continuity from the physical
side. These are qualitative regularity and positivity statements only;
no inverse normalization factor is used as a numerical jet majorant.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-- Both independent inverse parameters are changed in the same existing
invFun expression. This is an identity of the displayed functions. -/
theorem rootInverseCoordinate_parameterUnscale_eq_reparam
    (Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ) (h : ℝ → ℝ)
    {δ : ℝ} (hδ : 0 < δ) (x ζ θ : ℝ) :
    rootInverseCoordinate (rootFlowParameterUnscale Θ δ) h (x, ζ, θ) =
      rootScaledInverseCoordinate Θ h (Real.sqrt δ)
        (x / δ, ζ / (δ * Real.sqrt δ), θ) := by
  have hfirst : δ * (x / δ) = x := by field_simp [hδ.ne']
  have hsecond : δ * (Real.sqrt δ * (ζ / (δ * Real.sqrt δ))) = ζ := by
    field_simp [hδ.ne', (Real.sqrt_pos.2 hδ).ne']
  simpa only [hfirst, hsecond] using
    (rootScaledInverseCoordinate_eq_parameterUnscale Θ h hδ.ne'
      (Real.sqrt δ) (x / δ) (ζ / (δ * Real.sqrt δ)) θ).symm

theorem rootInverseCoordinate_parameterUnscale_regular
    (Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ) (h : ℝ → ℝ)
    {δ : ℝ} (hδ : 0 < δ)
    (hG : ContDiff ℝ ∞ (rootScaledInverseCoordinate Θ h (Real.sqrt δ)))
    (hperiod : ∀ x ζ θ,
      rootScaledInverseCoordinate Θ h (Real.sqrt δ) (x, ζ, θ + Real.pi) =
        rootScaledInverseCoordinate Θ h (Real.sqrt δ) (x, ζ, θ) + Real.pi) :
    ContDiff ℝ ∞ (rootInverseCoordinate (rootFlowParameterUnscale Θ δ) h) ∧
      ∀ x ζ θ, rootInverseCoordinate (rootFlowParameterUnscale Θ δ) h
          (x, ζ, θ + Real.pi) =
        rootInverseCoordinate (rootFlowParameterUnscale Θ δ) h (x, ζ, θ) + Real.pi := by
  have he : rootInverseCoordinate (rootFlowParameterUnscale Θ δ) h =
      fun p : ℝ × ℝ × ℝ => rootScaledInverseCoordinate Θ h (Real.sqrt δ)
        (p.1 / δ, p.2.1 / (δ * Real.sqrt δ), p.2.2) := by
    funext p
    exact rootInverseCoordinate_parameterUnscale_eq_reparam Θ h hδ p.1 p.2.1 p.2.2
  constructor
  · rw [he]
    exact hG.comp ((contDiff_fst.div_const δ).prodMk
      ((contDiff_snd.fst.div_const (δ * Real.sqrt δ)).prodMk contDiff_snd.snd))
  · intro x ζ θ
    simp only [rootInverseCoordinate_parameterUnscale_eq_reparam Θ h hδ, hperiod]

/-- The positive-side exact scale identity extends to the actual smooth
odd coefficient at the root. The total unextended odd quotient is never
differentiated across its nonphysical half-plane. -/
theorem extendedRootOddCoefficient_parameterUnscale_zero
    (Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ) (h : ℝ → ℝ)
    {δ : ℝ} (hδ : 0 < δ)
    (hG : ContDiff ℝ ∞ (rootScaledInverseCoordinate Θ h (Real.sqrt δ)))
    (hperiod : ∀ x ζ θ,
      rootScaledInverseCoordinate Θ h (Real.sqrt δ) (x, ζ, θ + Real.pi) =
        rootScaledInverseCoordinate Θ h (Real.sqrt δ) (x, ζ, θ) + Real.pi)
    (θ : ℝ) :
    extendedRootOddCoefficient (rootScaledInverseCoordinate Θ h (Real.sqrt δ)) (0, θ) =
      δ ^ (3 / 2 : ℝ) * extendedRootOddCoefficient
        (rootInverseCoordinate (rootFlowParameterUnscale Θ δ) h) (0, θ) := by
  obtain ⟨hG1, hperiod1⟩ := rootInverseCoordinate_parameterUnscale_regular Θ h hδ hG hperiod
  have hχ := contDiff_extendedRootOddCoefficient hG Real.pi_ne_zero
    (fun r _ => rootOddCoefficient_periodic hperiod r)
  have hχ1 := contDiff_extendedRootOddCoefficient hG1 Real.pi_ne_zero
    (fun r _ => rootOddCoefficient_periodic hperiod1 r)
  have he : EqOn (extendedRootOddCoefficient
        (rootScaledInverseCoordinate Θ h (Real.sqrt δ)))
      (fun p : PolarPoint => δ ^ (3 / 2 : ℝ) * extendedRootOddCoefficient
        (rootInverseCoordinate (rootFlowParameterUnscale Θ δ) h) (δ * p.1, p.2))
      (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := by
    intro p hp
    dsimp only
    rw [extendedRootOddCoefficient_of_nonneg _ hp.1.le,
      extendedRootOddCoefficient_of_nonneg _ (p := (δ * p.1, p.2)) (mul_pos hδ hp.1).le]
    exact rootScaledInverseCoordinate_odd_parameterUnscale Θ h hδ hp.1 p.2
  have hroot : (0, θ) ∈ closure (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := by
    rw [closure_prod_eq, closure_Ioi, closure_univ]
    exact ⟨Set.mem_Ici.mpr le_rfl, mem_univ _⟩
  have hc := he.closure hχ.continuous
    (continuous_const.mul (hχ1.continuous.comp
      ((continuous_const.mul continuous_fst).prodMk continuous_snd))) hroot
  simpa only [mul_zero] using hc

/-- The original scaled inverse regularity and positive root coefficient
supply the true unit-scale chart and height regularity at the same root.
The supplied V is the actual unscaled divided coefficient. -/
theorem rootDividedModel_parameterUnscale_root_regular
    (Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ) (h : ℝ → ℝ) (V : PolarPoint → ℝ)
    {δ θ : ℝ} (hδ : 0 < δ)
    (hG : ContDiff ℝ ∞ (rootScaledInverseCoordinate Θ h (Real.sqrt δ)))
    (hperiod : ∀ x ζ θ,
      rootScaledInverseCoordinate Θ h (Real.sqrt δ) (x, ζ, θ + Real.pi) =
        rootScaledInverseCoordinate Θ h (Real.sqrt δ) (x, ζ, θ) + Real.pi)
    (hχ : 0 < extendedRootOddCoefficient
      (rootScaledInverseCoordinate Θ h (Real.sqrt δ)) (0, θ))
    (hV : ContDiffAt ℝ ∞ V (0, θ)) (hVp : 0 < V (0, θ)) :
    let G := rootInverseCoordinate (rootFlowParameterUnscale Θ δ) h
    ContDiffAt ℝ ∞ (extendedRootEvenOddChart G) (0, θ) ∧
      ContDiffAt ℝ ∞ (rootDividedHeight 1 V G) (0, θ) ∧
      0 < rootDividedHeight 1 V G (0, θ) := by
  obtain ⟨hG1, hperiod1⟩ := rootInverseCoordinate_parameterUnscale_regular Θ h hδ hG hperiod
  let G := rootInverseCoordinate (rootFlowParameterUnscale Θ δ) h
  have hχp : 0 < extendedRootOddCoefficient G (0, θ) := by
    have he := extendedRootOddCoefficient_parameterUnscale_zero Θ h hδ hG hperiod θ
    have hd : 0 < δ ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hδ _
    change 0 < extendedRootOddCoefficient
      (rootInverseCoordinate (rootFlowParameterUnscale Θ δ) h) (0, θ)
    nlinarith [hχ]
  have hχperiod : ∀ r, 0 ≤ r →
      Function.Periodic (fun η => rootOddCoefficient G (r, η)) Real.pi :=
    fun r _ => rootOddCoefficient_periodic hperiod1 r
  have hφperiod : ∀ r, 0 ≤ r → ∀ η,
      rootEven G (r, η + Real.pi) = rootEven G (r, η) + Real.pi :=
    fun r _ η => rootEven_period_add hperiod1 r η
  have hchart := contDiffAt_extendedRootEvenOddChart_of_ne_zero
    hG1 Real.pi_ne_zero hχperiod hφperiod hχp.ne'
  have hheight := contDiffAt_rootDividedHeight zero_lt_one hV
    (contDiff_extendedRootOddCoefficient hG1 Real.pi_ne_zero hχperiod).contDiffAt hVp hχp
  exact ⟨hchart, hheight.1, hheight.2⟩

end ContinuousFlexibility.Analysis
