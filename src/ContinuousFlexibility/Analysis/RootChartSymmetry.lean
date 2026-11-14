module

public import ContinuousFlexibility.Analysis.ActualRootChart
public import ContinuousFlexibility.Analysis.RootFlowSymmetry
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Tactic.Ring

/-!
# Angular symmetries of the actual root chart

Degree-one angular equivariance of the input passes to its even root
coordinate; its odd divided coefficient is periodic. Simultaneous
reflection of the independent root parameter and angle makes the even
coordinate odd and the divided coefficient even in the angle, including
at the root where the coefficient is defined by an actual derivative.

The final interfaces obtain the input symmetries from the true inverse
endpoint flow and, for reflection, from uniqueness of the root ODE.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

theorem rootEven_period_add {G : ℝ × ℝ × ℝ → ℝ} {T : ℝ}
    (hperiod : ∀ x ζ θ, G (x, ζ, θ + T) = G (x, ζ, θ) + T)
    (x θ : ℝ) :
    rootEven G (x, θ + T) = rootEven G (x, θ) + T := by
  simp only [rootEven, hperiod]
  ring

theorem rootEven_sub_angle_periodic {G : ℝ × ℝ × ℝ → ℝ} {T : ℝ}
    (hperiod : ∀ x ζ θ, G (x, ζ, θ + T) = G (x, ζ, θ) + T)
    (x : ℝ) :
    Function.Periodic (fun θ => rootEven G (x, θ) - θ) T := by
  intro θ
  change rootEven G (x, θ + T) - (θ + T) = rootEven G (x, θ) - θ
  rw [rootEven_period_add hperiod]
  ring

theorem rootOdd_periodic {G : ℝ × ℝ × ℝ → ℝ} {T : ℝ}
    (hperiod : ∀ x ζ θ, G (x, ζ, θ + T) = G (x, ζ, θ) + T)
    (x : ℝ) :
    Function.Periodic (fun θ => rootOdd G (x, θ)) T := by
  intro θ
  change rootOdd G (x, θ + T) = rootOdd G (x, θ)
  by_cases hx : x = 0
  · subst x
    rw [rootOdd_zero, rootOdd_zero]
    have he : (fun ζ : ℝ => G (0, ζ, θ + T)) =
        (fun ζ : ℝ => G (0, ζ, θ) + T) :=
      funext fun ζ => hperiod 0 ζ θ
    rw [he, deriv_add_const]
  · rw [rootOdd_of_ne_zero G (p := (x, θ + T)) hx,
      rootOdd_of_ne_zero G (p := (x, θ)) hx]
    rw [hperiod, hperiod]
    congr 1
    ring

theorem rootOddCoefficient_periodic {G : ℝ × ℝ × ℝ → ℝ} {T : ℝ}
    (hperiod : ∀ x ζ θ, G (x, ζ, θ + T) = G (x, ζ, θ) + T)
    (x : ℝ) :
    Function.Periodic (fun θ => rootOddCoefficient G (x, θ)) T := by
  intro θ
  exact congrArg Neg.neg (rootOdd_periodic hperiod x θ)

theorem rootRadialCoordinate_periodic {G : ℝ × ℝ × ℝ → ℝ} {T : ℝ}
    (hperiod : ∀ x ζ θ, G (x, ζ, θ + T) = G (x, ζ, θ) + T)
    (x : ℝ) :
    Function.Periodic (fun θ => rootRadialCoordinate G (x, θ)) T := by
  intro θ
  simp only [rootRadialCoordinate, rootRadialFactor,
    rootOddCoefficient_periodic hperiod x θ]

theorem rootEven_reflect {G : ℝ × ℝ × ℝ → ℝ}
    (hreflect : ∀ x ζ θ, G (x, -ζ, -θ) = -G (x, ζ, θ))
    (x θ : ℝ) :
    rootEven G (x, -θ) = -rootEven G (x, θ) := by
  have hp : G (x, x ^ (3 / 2 : ℝ), -θ) =
      -G (x, -(x ^ (3 / 2 : ℝ)), θ) := by
    simpa only [neg_neg] using hreflect x (-(x ^ (3 / 2 : ℝ))) θ
  simp only [rootEven, hp, hreflect]
  ring

theorem rootOdd_reflect {G : ℝ × ℝ × ℝ → ℝ}
    (hG : ContDiff ℝ ∞ G)
    (hreflect : ∀ x ζ θ, G (x, -ζ, -θ) = -G (x, ζ, θ))
    (x θ : ℝ) :
    rootOdd G (x, -θ) = rootOdd G (x, θ) := by
  by_cases hx : x = 0
  · subst x
    rw [rootOdd_zero, rootOdd_zero]
    have hs : ContDiff ℝ ∞ (fun ζ : ℝ => G (0, ζ, θ)) :=
      hG.comp (contDiff_const.prodMk (contDiff_id.prodMk contDiff_const))
    have hd : HasDerivAt (fun ζ : ℝ => G (0, ζ, θ))
        (deriv (fun ζ : ℝ => G (0, ζ, θ)) 0) (-(0 : ℝ)) := by
      simpa only [neg_zero] using (hs.differentiable (by simp) 0).hasDerivAt
    have hc := (hd.comp 0 (hasDerivAt_neg (0 : ℝ))).fun_neg
    have he : (fun ζ : ℝ =>
        -(((fun u : ℝ => G (0, u, θ)) ∘ (fun u : ℝ => -u)) ζ)) =
        (fun ζ : ℝ => G (0, ζ, -θ)) := by
      funext ζ
      simpa only [Function.comp_apply, neg_neg] using (hreflect 0 (-ζ) θ).symm
    rw [he] at hc
    simpa only [mul_neg_one, neg_neg] using hc.deriv
  · have hp : G (x, x ^ (3 / 2 : ℝ), -θ) =
        -G (x, -(x ^ (3 / 2 : ℝ)), θ) := by
      simpa only [neg_neg] using hreflect x (-(x ^ (3 / 2 : ℝ))) θ
    rw [rootOdd_of_ne_zero G (p := (x, -θ)) hx,
      rootOdd_of_ne_zero G (p := (x, θ)) hx]
    rw [hp, hreflect]
    congr 1
    ring

theorem rootOddCoefficient_reflect {G : ℝ × ℝ × ℝ → ℝ}
    (hG : ContDiff ℝ ∞ G)
    (hreflect : ∀ x ζ θ, G (x, -ζ, -θ) = -G (x, ζ, θ))
    (x θ : ℝ) :
    rootOddCoefficient G (x, -θ) = rootOddCoefficient G (x, θ) :=
  congrArg Neg.neg (rootOdd_reflect hG hreflect x θ)

theorem rootRadialCoordinate_reflect {G : ℝ × ℝ × ℝ → ℝ}
    (hG : ContDiff ℝ ∞ G)
    (hreflect : ∀ x ζ θ, G (x, -ζ, -θ) = -G (x, ζ, θ))
    (x θ : ℝ) :
    rootRadialCoordinate G (x, -θ) = rootRadialCoordinate G (x, θ) := by
  simp only [rootRadialCoordinate, rootRadialFactor,
    rootOddCoefficient_reflect hG hreflect x θ]

/-- The actual normalized inverse flow has degree-one angular equivariance. -/
theorem rootInverseCoordinate_period_add
    {Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ} {T : ℝ} {hL : ℝ → ℝ}
    (hT : T ≠ 0)
    (hEndpoint : ContDiff ℝ ∞ (fun z : (ℝ × ℝ) × ℝ => Θ z.1 1 z.2))
    (hpositive : ∀ p θ, 0 < deriv (fun η => Θ p 1 η) θ)
    (hperiod : ∀ p θ, Θ p 1 (θ + T) = Θ p 1 θ + T)
    (hLperiod : ∀ θ, hL (θ + T) = hL θ + T)
    (x ζ θ : ℝ) :
    rootInverseCoordinate Θ hL (x, ζ, θ + T) =
      rootInverseCoordinate Θ hL (x, ζ, θ) + T := by
  simp only [rootInverseCoordinate]
  rw [parameterizedCircleInverse_period_add hT hEndpoint
    (fun z => hpositive z.1 z.2) hperiod, hLperiod]

/-- Reflection of the actual endpoint lifts and of hL passes to their
normalized actual inverse. -/
theorem rootInverseCoordinate_reflect
    {Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ} {T : ℝ} {hL : ℝ → ℝ}
    (hT : T ≠ 0)
    (hEndpoint : ContDiff ℝ ∞ (fun z : (ℝ × ℝ) × ℝ => Θ z.1 1 z.2))
    (hpositive : ∀ p θ, 0 < deriv (fun η => Θ p 1 η) θ)
    (hperiod : ∀ p θ, Θ p 1 (θ + T) = Θ p 1 θ + T)
    (hreflect : ∀ x ζ θ, Θ (x, -ζ) 1 (-θ) = -Θ (x, ζ) 1 θ)
    (hLodd : ∀ θ, hL (-θ) = -hL θ) (x ζ θ : ℝ) :
    rootInverseCoordinate Θ hL (x, -ζ, -θ) =
      -rootInverseCoordinate Θ hL (x, ζ, θ) := by
  have hi := parameterizedCircleInverse_reflect
    (σ := fun p : ℝ × ℝ => (p.1, -p.2))
    hT hEndpoint (fun z => hpositive z.1 z.2) hperiod
    (fun p η => hreflect p.1 p.2 η) (x, ζ) θ
  simp only [rootInverseCoordinate]
  rw [hi, hLodd]

/-- For the actual root ODE the required endpoint reflection is supplied
by uniqueness, rather than assumed as extra geometry of the flow. -/
theorem rootInverseCoordinate_reflect_of_rootFlow
    {d c₀ : ℝ × ℝ → ℝ} {T : ℝ} {hL : ℝ → ℝ}
    {Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ}
    (hT : T ≠ 0)
    (hd : ContDiff ℝ ∞ d) (hc₀ : ContDiff ℝ ∞ c₀)
    (hdperiod : ∀ r, Function.Periodic (fun θ => d (r, θ)) T)
    (hc₀period : ∀ r, Function.Periodic (fun θ => c₀ (r, θ)) T)
    (hdodd : ∀ r θ, d (r, -θ) = -d (r, θ))
    (hc₀even : ∀ r θ, c₀ (r, -θ) = c₀ (r, θ))
    (hinit : ∀ p θ, Θ p 0 θ = θ)
    (hflow : ∀ p θ t, t ∈ Icc (0 : ℝ) 1 →
      HasDerivWithinAt (fun r => Θ p r θ)
        (2 * p.1 * t * d (p.1 * t ^ 2, Θ p t θ) +
          2 * p.2 * t ^ 2 * c₀ (p.1 * t ^ 2, Θ p t θ))
        (Icc (0 : ℝ) 1) t)
    (hEndpoint : ContDiff ℝ ∞ (fun z : (ℝ × ℝ) × ℝ => Θ z.1 1 z.2))
    (hpositive : ∀ p θ, 0 < deriv (fun η => Θ p 1 η) θ)
    (hperiod : ∀ p θ, Θ p 1 (θ + T) = Θ p 1 θ + T)
    (hLodd : ∀ θ, hL (-θ) = -hL θ) (x ζ θ : ℝ) :
    rootInverseCoordinate Θ hL (x, -ζ, -θ) =
      -rootInverseCoordinate Θ hL (x, ζ, θ) :=
  rootInverseCoordinate_reflect hT hEndpoint hpositive hperiod
    (fun a b η => rootRegularizedFlow_reflect hT hd hc₀
      hdperiod hc₀period hdodd hc₀even hinit hflow a b η
      (show (1 : ℝ) ∈ Icc 0 1 from ⟨zero_le_one, le_rfl⟩))
    hLodd x ζ θ

end ContinuousFlexibility.Analysis
