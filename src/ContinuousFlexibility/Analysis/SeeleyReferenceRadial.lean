module

public import ContinuousFlexibility.Analysis.SeeleyRootReflection
public import ContinuousFlexibility.Analysis.RootReferenceRadial

/-!
# The actual radial reference chart after fixed Seeley extension

The fixed extension preserves angular-independent half-plane fields and
a zero angular displacement. Applied to the genuine radial ODE inverse,
its extended root chart is therefore a scalar radial coordinate paired
with the unchanged angle. No equation for the extended coefficients on
the reflected side is inferred from these symmetry identities.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements

/-- Arbitrary angular translations commute with the fixed extension,
so angular independence survives on the whole plane. -/
theorem seeleyPeriodicExtension_angle_independent
    {f : PolarPoint → ℝ}
    (hf : ∀ r, 0 ≤ r → ∀ θ, f (r, θ) = f (r, 0)) (r θ : ℝ) :
    seeleyPeriodicExtension f (r, θ) = seeleyPeriodicExtension f (r, 0) := by
  have hp : ∀ x, 0 ≤ x →
      Function.Periodic (fun η : ℝ => f (x, η)) θ := by
    intro x hx η
    exact (hf x hx (η + θ)).trans (hf x hx η).symm
  have he : seeleyPeriodicExtension f (r, 0 + θ) =
      seeleyPeriodicExtension f (r, 0) :=
    seeleyPeriodicExtension_periodic hp r 0
  simpa only [zero_add] using he

/-- Only half-plane values enter the negative reflection series. -/
theorem seeleyPeriodicExtension_eq_zero_of_halfPlane
    {f : PolarPoint → ℝ}
    (hf : ∀ r, 0 ≤ r → ∀ θ, f (r, θ) = 0) (p : PolarPoint) :
    seeleyPeriodicExtension f p = 0 := by
  by_cases hp : 0 ≤ p.1
  · rw [seeleyPeriodicExtension_of_nonneg f hp, hf p.1 hp p.2]
  · rw [seeleyPeriodicExtension_of_neg f (lt_of_not_ge hp)]
    calc
      _ = ∑' _i : SeeleyIndex, (0 : ℝ) := by
        apply tsum_congr
        intro i
        rw [hf (-seeleyData.b i * p.1)
          (mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr (seeleyData.b_nonneg i))
            (lt_of_not_ge hp).le) p.2, mul_zero, smul_zero]
      _ = 0 := tsum_zero

theorem extendedRootEven_eq_angle_of_halfPlane
    {G : ℝ × ℝ × ℝ → ℝ}
    (hφ : ∀ r, 0 ≤ r → ∀ θ, rootEven G (r, θ) = θ)
    (r θ : ℝ) :
    extendedRootEven G (r, θ) = θ := by
  have hz : seeleyPeriodicExtension (fun q => rootEven G q - q.2) (r, θ) = 0 :=
    seeleyPeriodicExtension_eq_zero_of_halfPlane
      (fun x hx η => by rw [hφ x hx η, sub_self]) (r, θ)
  simp only [extendedRootEven, hz, zero_add]

/-- The scalar radial coordinate is taken from the actual extended chart
at angle zero. This identity holds on both sides of the root. -/
theorem extendedRootEvenOddChart_radial_of_halfPlane
    {G : ℝ × ℝ × ℝ → ℝ}
    (hχ : ∀ r, 0 ≤ r → ∀ θ,
      rootOddCoefficient G (r, θ) = rootOddCoefficient G (r, 0))
    (hφ : ∀ r, 0 ≤ r → ∀ θ, rootEven G (r, θ) = θ)
    (r θ : ℝ) :
    extendedRootEvenOddChart G (r, θ) =
      (extendedRootRadialCoordinate G (r, 0), θ) := by
  have heχ : extendedRootOddCoefficient G (r, θ) =
      extendedRootOddCoefficient G (r, 0) :=
    seeleyPeriodicExtension_angle_independent hχ r θ
  apply Prod.ext
  · simp only [extendedRootEvenOddChart, extendedRootRadialCoordinate,
      extendedRootRadialFactor, heχ]
  · exact extendedRootEven_eq_angle_of_halfPlane hφ r θ

/-- The preceding scalar form applies to the actual reference ODE and
its genuine inverse, with no prescribed formula for that inverse. -/
theorem extendedRootEvenOddChart_rootInverseCoordinate_radial
    {c : ℝ → ℝ} {Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ}
    (hinit : ∀ p θ, Θ p 0 θ = θ)
    (hflow : ∀ p θ t, t ∈ Icc (0 : ℝ) 1 →
      HasDerivWithinAt (fun s => Θ p s θ)
        (2 * p.2 * t ^ 2 * c (p.1 * t ^ 2))
        (Icc (0 : ℝ) 1) t)
    (r θ : ℝ) :
    extendedRootEvenOddChart (rootInverseCoordinate Θ id) (r, θ) =
      (extendedRootRadialCoordinate (rootInverseCoordinate Θ id) (r, 0), θ) := by
  apply extendedRootEvenOddChart_radial_of_halfPlane
  · intro x hx η
    exact (rootOddCoefficient_rootInverseCoordinate_radial hinit hflow hx η).trans
      (rootOddCoefficient_rootInverseCoordinate_radial hinit hflow hx 0).symm
  · intro x _ η
    exact rootEven_rootInverseCoordinate_radial hinit hflow x η

end ContinuousFlexibility.Analysis

