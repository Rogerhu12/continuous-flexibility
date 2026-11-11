import ContinuousFlexibility.Analysis.ActualRootChart
import ContinuousFlexibility.Analysis.PeriodicScalarFlow
import Mathlib.Tactic.Ring

/-!
# The actual radial reference root chart

For zero drift and an angular-independent root coefficient, uniqueness of
the true ODE makes the flow affine in the initial angle and linear in the
independent root parameter. Its actual inverse is an angular translation.
Consequently the even root coordinate is exactly the original angle, and
the divided odd coefficient is radial on the physical half-plane.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-- The genuine displacement at unit independent-root parameter. -/
def rootRadialDisplacement (Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ) (x : ℝ) : ℝ :=
  Θ (x, 1) 1 0

/-- The radial specialization of the displayed root ODE is an actual
consequence of zero drift and angular independence of its coefficient. -/
theorem rootRegularizedFlow_radial_ode
    {d c₀ : PolarPoint → ℝ} {c : ℝ → ℝ}
    {Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ}
    (hd : ∀ p, d p = 0) (hc : ∀ r θ, c₀ (r, θ) = c r)
    (hflow : ∀ p θ t, t ∈ Icc (0 : ℝ) 1 →
      HasDerivWithinAt (fun s => Θ p s θ)
        (2 * p.1 * t * d (p.1 * t ^ 2, Θ p t θ) +
          2 * p.2 * t ^ 2 * c₀ (p.1 * t ^ 2, Θ p t θ))
        (Icc (0 : ℝ) 1) t) :
    ∀ p θ t, t ∈ Icc (0 : ℝ) 1 →
      HasDerivWithinAt (fun s => Θ p s θ)
        (2 * p.2 * t ^ 2 * c (p.1 * t ^ 2))
        (Icc (0 : ℝ) 1) t := by
  intro p θ t ht
  simpa only [hd, hc, mul_zero, zero_add] using hflow p θ t ht

section RadialFlow

variable {c : ℝ → ℝ} {Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ}
  (hinit : ∀ p θ, Θ p 0 θ = θ)
  (hflow : ∀ p θ t, t ∈ Icc (0 : ℝ) 1 →
    HasDerivWithinAt (fun s => Θ p s θ)
      (2 * p.2 * t ^ 2 * c (p.1 * t ^ 2))
      (Icc (0 : ℝ) 1) t)

include hinit hflow

/-- The complete angular and independent-root dependence follows from
the actual time ODE. No regularity of the selected family is assumed. -/
theorem rootRegularizedFlow_radial_formula
    (x ζ θ : ℝ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    Θ (x, ζ) t θ = θ + ζ * Θ (x, 1) t 0 := by
  apply eqOn_scalarFlow_of_same_initial
    (K := 0) (F := fun s _ => 2 * ζ * s ^ 2 * c (x * s ^ 2))
    (u := fun s => Θ (x, ζ) s θ)
    (v := fun s => θ + ζ * Θ (x, 1) s 0)
    (fun _ _ => LipschitzWith.const _)
    (fun s hs => hflow (x, ζ) θ s hs) ?_ ?_ ht
  · intro s hs
    have hd := ((hflow (x, 1) 0 s hs).const_mul ζ).const_add θ
    exact hd.congr_deriv (by ring)
  · simp only [hinit, mul_zero, add_zero]

/-- The actual chosen inverse is the opposite angular translation. -/
theorem rootInverseCoordinate_radial_formula (x ζ θ : ℝ) :
    rootInverseCoordinate Θ id (x, ζ, θ) =
      θ - ζ * rootRadialDisplacement Θ x := by
  have hEnd (η : ℝ) : Θ (x, ζ) 1 η = η + ζ * rootRadialDisplacement Θ x :=
    rootRegularizedFlow_radial_formula hinit hflow x ζ η
      (show (1 : ℝ) ∈ Icc 0 1 from ⟨zero_le_one, le_rfl⟩)
  have hInj : Function.Injective (Θ (x, ζ) 1) := by
    intro η ψ he
    have hh : η + ζ * rootRadialDisplacement Θ x =
        ψ + ζ * rootRadialDisplacement Θ x := by simpa only [hEnd] using he
    exact add_right_cancel hh
  have hValue : Θ (x, ζ) 1 (θ - ζ * rootRadialDisplacement Θ x) = θ := by
    rw [hEnd]
    ring
  have hi := Function.leftInverse_invFun hInj (θ - ζ * rootRadialDisplacement Θ x)
  rw [hValue] at hi
  simpa only [rootInverseCoordinate, parameterizedCircleInverse, id_eq] using hi

/-- The reference root angle is exactly θ at every radial value. -/
theorem rootEven_rootInverseCoordinate_radial (x θ : ℝ) :
    rootEven (rootInverseCoordinate Θ id) (x, θ) = θ := by
  simp only [rootEven, rootInverseCoordinate_radial_formula hinit hflow]
  ring

/-- On the physical half-plane the actual divided coefficient equals
the single genuine radial displacement function. -/
theorem rootOddCoefficient_rootInverseCoordinate_radial
    {x : ℝ} (hx : 0 ≤ x) (θ : ℝ) :
    rootOddCoefficient (rootInverseCoordinate Θ id) (x, θ) =
      rootRadialDisplacement Θ x := by
  rcases eq_or_lt_of_le hx with hx | hx
  · subst x
    rw [rootOddCoefficient_zero]
    have he : (fun ζ : ℝ => rootInverseCoordinate Θ id (0, ζ, θ)) =
        (fun ζ : ℝ => θ - ζ * rootRadialDisplacement Θ 0) :=
      funext fun ζ => rootInverseCoordinate_radial_formula hinit hflow 0 ζ θ
    rw [he]
    have hd := ((hasDerivAt_id (0 : ℝ)).mul_const (rootRadialDisplacement Θ 0)).const_sub θ
    simp only [id_eq] at hd
    rw [hd.deriv]
    ring
  · have hpow : x ^ (3 / 2 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hx _).ne'
    unfold rootOddCoefficient
    rw [rootOdd_of_ne_zero (rootInverseCoordinate Θ id) (p := (x, θ)) hx.ne']
    rw [rootInverseCoordinate_radial_formula hinit hflow,
      rootInverseCoordinate_radial_formula hinit hflow]
    field_simp [hpow]
    <;> ring

/-- The actual physical reference root chart has a scalar radial map
and leaves its angular coordinate unchanged. -/
theorem rootEvenOddChart_rootInverseCoordinate_radial
    {x : ℝ} (hx : 0 ≤ x) (θ : ℝ) :
    rootEvenOddChart (rootInverseCoordinate Θ id) (x, θ) =
      (x * (((3 : ℝ) / 2) * rootRadialDisplacement Θ x) ^ (2 / 3 : ℝ), θ) := by
  simp only [rootEvenOddChart, rootRadialCoordinate, rootRadialFactor,
    rootOddCoefficient_rootInverseCoordinate_radial hinit hflow hx θ,
    rootEven_rootInverseCoordinate_radial hinit hflow x θ]

end RadialFlow

/-- Joint smoothness already proved for the actual endpoint flow supplies
the true smooth radial displacement; it is not a prescribed reference profile. -/
theorem contDiff_rootRadialDisplacement
    {Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ}
    (hEndpoint : ContDiff ℝ ∞ (fun z : (ℝ × ℝ) × ℝ => Θ z.1 1 z.2)) :
    ContDiff ℝ ∞ (rootRadialDisplacement Θ) :=
  hEndpoint.comp ((contDiff_id.prodMk contDiff_const).prodMk contDiff_const)

end ContinuousFlexibility.Analysis
