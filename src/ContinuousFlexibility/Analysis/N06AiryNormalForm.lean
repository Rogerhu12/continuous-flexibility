import ContinuousFlexibility.Analysis.N06AiryRadialGerm
import ContinuousFlexibility.Analysis.N06RootSpeedExtension

/-!
# The genuine reference Airy principal normal form

The same explicitly extended speed defines the coordinate and height.
On its actual root collar it agrees with the physical speed factor.
The true derivative identity therefore gives radial principal coefficient
one and angular coefficient minus the new radial coordinate, on both sides.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Real
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-- The actual coordinate derivative satisfies the exact Airy identity. -/
theorem n06_airyRadialCoordinate_mul_deriv_sq {c : ℝ → ℝ}
    (hc : ContDiff ℝ ∞ c) (x : ℝ) (hp : 0 < n06AiryAverage c x) :
    n06AiryRadialCoordinate c x * deriv (n06AiryRadialCoordinate c) x ^ 2 =
      x * c x ^ 2 := by
  rw [(n06_hasDerivAt_airyRadialCoordinate hc x hp).deriv]
  have hpow : n06AiryAverage c x ^ (2 / 3 : ℝ) *
      (n06AiryAverage c x ^ (-1 / 3 : ℝ)) ^ 2 = 1 := by
    rw [← Real.rpow_mul_natCast hp.le (-1 / 3 : ℝ) 2, ← Real.rpow_add hp]
    norm_num
  calc
    _ = (x * c x ^ 2) *
        (n06AiryAverage c x ^ (2 / 3 : ℝ) *
          (n06AiryAverage c x ^ (-1 / 3 : ℝ)) ^ 2) := by
      dsimp only [n06AiryRadialCoordinate, n06AiryRadialSlope]
      ring
    _ = x * c x ^ 2 := by rw [hpow, mul_one]

/-- The existing physical root-speed expression has the literal square
given by the divided derivative of the original profile. -/
theorem n06_referenceRootSpeedFactor_sq
    {w g : ℝ → ℝ} {r ι x : ℝ}
    (hr : 0 < r + ι * x) (hw : 0 < w (r + ι * x)) (hg : 0 < g x) :
    referenceRootSpeedFactor w g r ι x ^ 2 =
      g x / ((r + ι * x) * w (r + ι * x)) := by
  rw [referenceRootSpeedFactor, div_pow,
    Real.sq_sqrt (rootProfileRadicand_pos hr hw hg).le]
  unfold rootProfileRadicand
  field_simp [hr.ne', hw.ne']

/-- On the explicit inner collar, the new two-sided coordinate obeys
the equation of the same physical profile, including the root itself. -/
theorem n06_airyRoot_physical_identity
    {w g : ℝ → ℝ} {r ι δ x : ℝ}
    (hδ : 0 < δ) (hx : |x| ≤ δ / 4)
    (hr : 0 < r + ι * x) (hw : 0 < w (r + ι * x)) (hg : 0 < g x)
    (hdivide : -deriv w (r + ι * x) = x * g x)
    (hext : ContDiff ℝ ∞
      (n06RootSpeedExtension δ (referenceRootSpeedFactor w g r ι)))
    (havg : 0 < n06AiryAverage
      (n06RootSpeedExtension δ (referenceRootSpeedFactor w g r ι)) x) :
    let c := n06RootSpeedExtension δ (referenceRootSpeedFactor w g r ι)
    n06AiryRadialCoordinate c x * deriv (n06AiryRadialCoordinate c) x ^ 2 =
      -deriv w (r + ι * x) / ((r + ι * x) * w (r + ι * x)) := by
  dsimp only
  rw [n06_airyRadialCoordinate_mul_deriv_sq hext x havg,
    n06_rootSpeedExtension_eq hδ _ hx, n06_referenceRootSpeedFactor_sq hr hw hg,
    hdivide]
  ring

/-- These are the actual scalar density expressions of the radial
coordinate-height change. The zero and first-order root terms are retained;
the statement is valid on both sides and at the actual turning radius. -/
theorem n06_airyRoot_principal_normal_form
    {w g : ℝ → ℝ} {r ι δ x : ℝ}
    (hδ : 0 < δ) (hx : |x| ≤ δ / 4)
    (hr : 0 < r + ι * x) (hw : 0 < w (r + ι * x)) (hg : 0 < g x)
    (hdivide : -deriv w (r + ι * x) = x * g x)
    (hext : ContDiff ℝ ∞
      (n06RootSpeedExtension δ (referenceRootSpeedFactor w g r ι)))
    (havg : ∀ t : ℝ, 0 < n06AiryAverage
      (n06RootSpeedExtension δ (referenceRootSpeedFactor w g r ι)) t) :
    let c := n06RootSpeedExtension δ (referenceRootSpeedFactor w g r ι)
    let H := n06AiryRadialHeight c (fun t => w (r + ι * t))
    let s := deriv (n06AiryRadialCoordinate c) x
    0 < s ∧ H x ^ 2 * w (r + ι * x) * s = 1 ∧
      H x ^ 2 * (deriv w (r + ι * x) / (r + ι * x)) / s =
        -n06AiryRadialCoordinate c x := by
  let c := n06RootSpeedExtension δ (referenceRootSpeedFactor w g r ι)
  let H := n06AiryRadialHeight c (fun t => w (r + ι * t))
  let s := deriv (n06AiryRadialCoordinate c) x
  change 0 < s ∧ H x ^ 2 * w (r + ι * x) * s = 1 ∧
    H x ^ 2 * (deriv w (r + ι * x) / (r + ι * x)) / s =
      -n06AiryRadialCoordinate c x
  have hc : 0 < c x := by
    rw [show c x = referenceRootSpeedFactor w g r ι x from
      n06_rootSpeedExtension_eq hδ _ hx]
    exact referenceRootSpeedFactor_pos hr hw hg
  have hslope : 0 < n06AiryRadialSlope c x :=
    mul_pos hc (Real.rpow_pos_of_pos (havg x) _)
  have hs : 0 < s := by
    rw [show s = n06AiryRadialSlope c x from
      (n06_hasDerivAt_airyRadialCoordinate hext x (havg x)).deriv]
    exact hslope
  have hH : H x = (Real.sqrt (w (r + ι * x) * s))⁻¹ :=
    n06_airyRadialHeight_eq_actual hext havg x hw hslope
  have hHsq : H x ^ 2 = (w (r + ι * x) * s)⁻¹ := by
    rw [hH, inv_pow, Real.sq_sqrt (mul_pos hw hs).le]
  have hAiry : n06AiryRadialCoordinate c x * s ^ 2 =
      -deriv w (r + ι * x) / ((r + ι * x) * w (r + ι * x)) :=
    n06_airyRoot_physical_identity hδ hx hr hw hg hdivide hext (havg x)
  have hAiryMul := (eq_div_iff (mul_ne_zero hr.ne' hw.ne')).mp hAiry
  refine ⟨hs, ?_, ?_⟩
  · rw [hHsq]
    field_simp [hw.ne', hs.ne']
  · rw [hHsq]
    calc
      _ = deriv w (r + ι * x) / ((r + ι * x) * w (r + ι * x) * s ^ 2) := by
        field_simp [hr.ne', hw.ne', hs.ne']
        <;> ring
      _ = -n06AiryRadialCoordinate c x := by
        apply (div_eq_iff (mul_ne_zero (mul_ne_zero hr.ne' hw.ne')
          (pow_ne_zero 2 hs.ne'))).mpr
        nlinarith only [hAiryMul]

end ContinuousFlexibility.Analysis
