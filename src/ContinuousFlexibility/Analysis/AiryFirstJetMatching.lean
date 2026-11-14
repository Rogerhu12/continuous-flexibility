module

public import ContinuousFlexibility.Analysis.AdjugateAiryTransport
public import ContinuousFlexibility.Geometry.Primitive
public import ContinuousFlexibility.Geometry.PlanarOrientation

/-!
# Matching actual Airy first integrals at a reflected cut

Both signs of the characteristic first integral are treated by one real
parameter. A reflected radial chart derivative is exactly compensated by
reversing the Airy travel coordinate on the right half.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

theorem contDiffAt_airyFirstIntegral
    {F : PolarPoint → PolarPoint} {p : PolarPoint}
    (hF : ContDiffAt ℝ ∞ F p) (hξ : 0 < (F p).1) (σ : ℝ) :
    ContDiffAt ℝ ∞ (airyFirstIntegral F σ) p :=
  hF.snd.add (contDiffAt_const.mul
    (contDiffAt_const.mul (hF.fst.rpow_const_of_ne hξ.ne')))

/-- The full actual derivative follows from the two proved coordinate
derivatives and the coordinate decomposition of continuous linear maps. -/
theorem airyFirstIntegral_fderiv_apply
    {F : PolarPoint → PolarPoint} {p : PolarPoint}
    (hF : DifferentiableAt ℝ F p) (hξ : 0 < (F p).1) (σ : ℝ) (v : PolarPoint) :
    fderiv ℝ (airyFirstIntegral F σ) p v =
      (fderiv ℝ F p v).2 + σ * Real.sqrt (F p).1 * (fderiv ℝ F p v).1 := by
  have hp := airyFirstIntegral_partials hF hξ σ
  rw [polarCLM_apply_decompose, planeCLM_apply_decompose (fderiv ℝ F p) v]
  change v.1 * radialPartial (airyFirstIntegral F σ) p +
      v.2 * angularPartial (airyFirstIntegral F σ) p = _
  rw [hp.1, hp.2]
  ring

/-- The right travel offset gives matching values and full first jets. -/
theorem airyFirstIntegrals_match_of_reflected_derivative
    {F₀ F₁ : PolarPoint → PolarPoint} {p : PolarPoint} {ρ θ : ℝ}
    (hF₀ : DifferentiableAt ℝ F₀ p) (hF₁ : DifferentiableAt ℝ F₁ p)
    (hρ : 0 < ρ) (hvalue₀ : F₀ p = (ρ, θ)) (hvalue₁ : F₁ p = (ρ, θ))
    (hD : ∀ v : PolarPoint, fderiv ℝ F₁ p v =
      (-(fderiv ℝ F₀ p v).1, (fderiv ℝ F₀ p v).2)) (σ : ℝ) :
    airyFirstIntegral F₀ σ p =
        airyFirstIntegral F₁ (-σ) p + 2 * σ * airyTravelPrimitive ρ ∧
      fderiv ℝ (airyFirstIntegral F₀ σ) p =
        fderiv ℝ (fun y => airyFirstIntegral F₁ (-σ) y +
          2 * σ * airyTravelPrimitive ρ) p := by
  have hξ₀ : 0 < (F₀ p).1 := by simpa only [hvalue₀] using hρ
  have hξ₁ : 0 < (F₁ p).1 := by simpa only [hvalue₁] using hρ
  constructor
  · simp only [airyFirstIntegral, hvalue₀, hvalue₁]
    ring
  · rw [fderiv_add_const]
    apply ContinuousLinearMap.ext
    intro v
    rw [airyFirstIntegral_fderiv_apply hF₀ hξ₀ σ v,
      airyFirstIntegral_fderiv_apply hF₁ hξ₁ (-σ) v, hD v]
    simp only [hvalue₀, hvalue₁]
    ring

end ContinuousFlexibility.Analysis
