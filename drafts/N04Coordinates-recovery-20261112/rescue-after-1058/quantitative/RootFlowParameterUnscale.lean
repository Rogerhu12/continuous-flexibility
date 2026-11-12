import ContinuousFlexibility.Analysis.RootScaledInverseCoordinate

/-!
# Removing the normalization scale from the same chosen root flow

Draft: not independently reviewed or compiled.

Reparametrizing the already chosen scaled flow gives a solution of the
unscaled equation for the very same coefficient functions. This chooses
neither a new atlas nor a new flow. The inverse-coordinate equality keeps
both physical parameters, including the three-halves root scaling.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

def rootFlowParameterUnscale
    (Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ) (δ : ℝ)
    (p : ℝ × ℝ) (t θ : ℝ) : ℝ :=
  Θ (p.1 / δ, p.2 / δ) t θ

/-- The original family is recovered exactly by the inverse linear
parameter substitution. No uniqueness or extra existence is needed. -/
theorem rootFlowParameterUnscale_recover
    (Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ) {δ : ℝ} (hδ : δ ≠ 0)
    (p : ℝ × ℝ) (t θ : ℝ) :
    rootFlowParameterUnscale Θ δ (δ * p.1, δ * p.2) t θ = Θ p t θ := by
  have hdiv (x : ℝ) : (δ * x) / δ = x := by field_simp [hδ]
  simp only [rootFlowParameterUnscale, hdiv]

/-- This same reparametrized family solves the unscaled actual ODE.
There is no smallness or radial-domain hypothesis in this identity. -/
theorem rootFlowParameterUnscale_equations
    {d c : PolarPoint → ℝ} {δ : ℝ} (hδ : δ ≠ 0)
    {Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ}
    (hΘ : N04FlowEquations (rootRescaledField d c δ) Θ) :
    N04FlowEquations (rootRegularizedField d c) (rootFlowParameterUnscale Θ δ) := by
  have hmul (x : ℝ) : δ * (x / δ) = x := by field_simp [hδ]
  constructor
  · intro p θ
    exact hΘ.1 (p.1 / δ, p.2 / δ) θ
  · intro p θ t ht
    simpa only [rootFlowParameterUnscale, rootRescaledField, hmul] using
      hΘ.2 (p.1 / δ, p.2 / δ) θ t ht

/-- Exact equality of the two invFun expressions, including the independent
root parameter. The height/angular label is the same original function. -/
theorem rootScaledInverseCoordinate_eq_parameterUnscale
    (Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ) (h : ℝ → ℝ)
    {δ : ℝ} (hδ : δ ≠ 0) (τ x ζ θ : ℝ) :
    rootScaledInverseCoordinate Θ h τ (x, ζ, θ) =
      rootInverseCoordinate (rootFlowParameterUnscale Θ δ) h
        (δ * x, δ * (τ * ζ), θ) := by
  have hdiv (y : ℝ) : (δ * y) / δ = y := by field_simp [hδ]
  simp only [rootScaledInverseCoordinate, rootInverseCoordinate,
    parameterizedCircleInverse, rootFlowParameterScale, rootFlowParameterUnscale, hdiv]

/-- At the actual physical root samples, both parameters become the
unscaled physical parameters exactly. This does not bound any inverse
power of the arbitrary normalization scale. -/
theorem rootScaledInverseCoordinate_physical_eq_parameterUnscale
    (Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ) (h : ℝ → ℝ)
    {δ x : ℝ} (hδ : 0 < δ) (hx : 0 ≤ x) (η θ : ℝ) :
    rootScaledInverseCoordinate Θ h (Real.sqrt δ) (x, η * x ^ (3 / 2 : ℝ), θ) =
      rootInverseCoordinate (rootFlowParameterUnscale Θ δ) h
        (δ * x, η * (δ * x) ^ (3 / 2 : ℝ), θ) := by
  rw [rootScaledInverseCoordinate_eq_parameterUnscale Θ h hδ.ne']
  have he : δ * (Real.sqrt δ * (η * x ^ (3 / 2 : ℝ))) =
      η * (δ * x) ^ (3 / 2 : ℝ) := by
    calc
      _ = δ * ((η * Real.sqrt δ) * x ^ (3 / 2 : ℝ)) := by ring
      _ = _ := rootScaled_physical_parameter hδ.le hx η
  rw [he]

end ContinuousFlexibility.Analysis
