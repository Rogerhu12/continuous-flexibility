module

public import ContinuousFlexibility.Analysis.RootChartExtension

/-!
# Angular reflection through the fixed endpoint extension

The extension only samples the radial coordinate. Angular evenness
passes term by term through its reflection formula; angular oddness
uses linearity under negation. These identities require no assumed
derivative or smoothness of the input outside the half-plane.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements

/-- The negative-side formula exposes the fixed cutoff and coefficients. -/
theorem seeleyPeriodicExtension_of_neg
    (f : ℝ × ℝ → ℝ) {p : ℝ × ℝ} (hp : p.1 < 0) :
    seeleyPeriodicExtension f p =
      ∑' i, seeleyData.a i •
        (boundaryTaylorCutoff (-seeleyData.b i * p.1) *
          f (-seeleyData.b i * p.1, p.2)) := by
  unfold seeleyPeriodicExtension
  rw [if_neg (not_le.mpr hp)]
  unfold seeleyCylinderExtend seeleyExtend
  rw [if_neg (not_le.mpr hp)]
  change (∑' i, (seeleyData.a i * (-seeleyData.b i) ^ 0) •
      (boundaryTaylorCutoff (-seeleyData.b i * p.1) *
        f (-seeleyData.b i * p.1, p.2))) = _
  simp only [pow_zero, mul_one]

theorem seeleyPeriodicExtension_angle_even
    {f : ℝ × ℝ → ℝ}
    (heven : ∀ r, 0 ≤ r → ∀ θ, f (r, -θ) = f (r, θ)) (r θ : ℝ) :
    seeleyPeriodicExtension f (r, -θ) = seeleyPeriodicExtension f (r, θ) := by
  by_cases hr : 0 ≤ r
  · rw [seeleyPeriodicExtension_of_nonneg f hr, seeleyPeriodicExtension_of_nonneg f hr]
    exact heven r hr θ
  · rw [seeleyPeriodicExtension_of_neg f (lt_of_not_ge hr),
      seeleyPeriodicExtension_of_neg f (lt_of_not_ge hr)]
    apply tsum_congr
    intro i
    rw [heven (-seeleyData.b i * r)
      (mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr (seeleyData.b_nonneg i))
        (lt_of_not_ge hr).le) θ]

theorem seeleyPeriodicExtension_angle_odd
    {f : ℝ × ℝ → ℝ}
    (hodd : ∀ r, 0 ≤ r → ∀ θ, f (r, -θ) = -f (r, θ)) (r θ : ℝ) :
    seeleyPeriodicExtension f (r, -θ) = -seeleyPeriodicExtension f (r, θ) := by
  by_cases hr : 0 ≤ r
  · rw [seeleyPeriodicExtension_of_nonneg f hr, seeleyPeriodicExtension_of_nonneg f hr]
    exact hodd r hr θ
  · rw [seeleyPeriodicExtension_of_neg f (lt_of_not_ge hr),
      seeleyPeriodicExtension_of_neg f (lt_of_not_ge hr), ← tsum_neg]
    apply tsum_congr
    intro i
    rw [hodd (-seeleyData.b i * r)
      (mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr (seeleyData.b_nonneg i))
        (lt_of_not_ge hr).le) θ, mul_neg, smul_neg]

theorem extendedRootOddCoefficient_reflect
    {G : ℝ × ℝ × ℝ → ℝ}
    (hχ : ∀ r, 0 ≤ r → ∀ θ, rootOddCoefficient G (r, -θ) = rootOddCoefficient G (r, θ))
    (r θ : ℝ) :
    extendedRootOddCoefficient G (r, -θ) = extendedRootOddCoefficient G (r, θ) :=
  seeleyPeriodicExtension_angle_even hχ r θ

theorem extendedRootEven_reflect
    {G : ℝ × ℝ × ℝ → ℝ}
    (hφ : ∀ r, 0 ≤ r → ∀ θ, rootEven G (r, -θ) = -rootEven G (r, θ))
    (r θ : ℝ) :
    extendedRootEven G (r, -θ) = -extendedRootEven G (r, θ) := by
  have hd : ∀ s, 0 ≤ s → ∀ t,
      (rootEven G (s, -t) - (-t)) = -(rootEven G (s, t) - t) := by
    intro s hs t
    rw [hφ s hs t]
    ring
  have he := seeleyPeriodicExtension_angle_odd
    (f := fun q => rootEven G q - q.2) hd r θ
  unfold extendedRootEven
  rw [he]
  ring

/-- The extended chart has the same reflection law as the original
physical-side chart on the entire plane. -/
theorem extendedRootEvenOddChart_reflect
    {G : ℝ × ℝ × ℝ → ℝ}
    (hχ : ∀ r, 0 ≤ r → ∀ θ, rootOddCoefficient G (r, -θ) = rootOddCoefficient G (r, θ))
    (hφ : ∀ r, 0 ≤ r → ∀ θ, rootEven G (r, -θ) = -rootEven G (r, θ))
    (r θ : ℝ) :
    extendedRootEvenOddChart G (r, -θ) =
      ((extendedRootEvenOddChart G (r, θ)).1, -(extendedRootEvenOddChart G (r, θ)).2) := by
  apply Prod.ext
  · change r * (((3 : ℝ) / 2) * extendedRootOddCoefficient G (r, -θ)) ^ (2 / 3 : ℝ) =
      r * (((3 : ℝ) / 2) * extendedRootOddCoefficient G (r, θ)) ^ (2 / 3 : ℝ)
    rw [extendedRootOddCoefficient_reflect hχ r θ]
  · exact extendedRootEven_reflect hφ r θ

end ContinuousFlexibility.Analysis
