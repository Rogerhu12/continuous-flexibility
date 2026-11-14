module

public import ContinuousFlexibility.Analysis.IntervalFluxOffset
public import ContinuousFlexibility.Radial.R11bRadialTests

/-!
# The scalar equation after subtracting the left-tail datum

Only the zero angular mode may carry the left constant. Its subtraction
therefore changes the forcing by the fixed compact radial flux of
`chiLeft`, with no angular-frequency-dependent correction.
-/

@[expose] public section

open Set Filter MeasureTheory
open ContinuousFlexibility.Analysis ContinuousFlexibility.Statements
open scoped ContDiff

namespace ContinuousFlexibility.Radial

theorem profile_deriv_left_remainder {D : ReferenceData}
    (hborder : RadialTrueBorder D) {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ 1 u (radialCore D)) (a : ℝ)
    {r : ℝ} (hr : r ∈ radialCore D) :
    deriv (fun t => u t - a * D.chiLeft t) r =
      deriv u r - a * deriv D.chiLeft r := by
  have hud : DifferentiableAt ℝ u r :=
    (hu.differentiableOn (by simp) r hr).differentiableAt
      (isOpen_Ioo.mem_nhds hr)
  have hzd : DifferentiableAt ℝ (fun t => a * D.chiLeft t) r :=
    ((contDiff_const.mul hborder.2.2.2.2.1).differentiable (by simp)) r
  rw [deriv_fun_sub hud hzd, deriv_const_mul_field]

theorem profile_flux_sub_left_offset {D : ReferenceData}
    (hgeom : RadialProfileGeometry D) (hborder : RadialTrueBorder D)
    {u f : ℝ → ℝ} (hu : ContDiffOn ℝ 1 u (radialCore D))
    (huLp : MemLp u 2 (volume.restrict (radialCore D)))
    (hfLp : MemLp f 2 (volume.restrict (radialCore D)))
    (j a x₀ q : ℝ) (hx₀ : x₀ ∈ radialCore D) (ha : j ≠ 0 → a = 0)
    (hflux : ∀ r ∈ radialCore D, D.w r * deriv u r =
      intervalLocalPrimitive
        (fun y => f y + j ^ 2 * (deriv D.w y / y) * u y) x₀ r + q) :
    ∀ r ∈ radialCore D, D.w r * deriv (fun t => u t - a * D.chiLeft t) r =
      intervalLocalPrimitive
        (fun y => (f y - a * deriv (fun t => D.w t * deriv D.chiLeft t) y) +
          j ^ 2 * (deriv D.w y / y) * (u y - a * D.chiLeft y)) x₀ r +
            (q - D.w x₀ * (a * deriv D.chiLeft x₀)) := by
  let z : ℝ → ℝ := fun t => a * D.chiLeft t
  let V : ℝ → ℝ := fun t => j ^ 2 * (deriv D.w t / t)
  have hz : ContDiff ℝ ∞ z := contDiff_const.mul hborder.2.2.2.2.1
  have hV : Continuous V :=
    continuous_const.mul (r11b_continuous_flat_deriv_div hgeom.1 hgeom.2.2.1)
  have hja : a * j ^ 2 = 0 := by
    by_cases hj : j = 0
    · simp only [hj, zero_pow (by decide : 2 ≠ 0), mul_zero]
    · rw [ha hj, zero_mul]
  have hVz (t : ℝ) : V t * z t = 0 := by
    change (j ^ 2 * (deriv D.w t / t)) * (a * D.chiLeft t) = 0
    calc
      _ = (a * j ^ 2) * ((deriv D.w t / t) * D.chiLeft t) := by ring
      _ = 0 := by rw [hja, zero_mul]
  have hzder (t : ℝ) : deriv z t = a * deriv D.chiLeft t :=
    deriv_const_mul_field a
  have hzf : (fun t => D.w t * deriv z t) =
      (fun t => a * (D.w t * deriv D.chiLeft t)) := by
    funext t
    change D.w t * deriv z t = a * (D.w t * deriv D.chiLeft t)
    rw [hzder]
    ring
  have hzflux (t : ℝ) :
      deriv (fun s => D.w s * deriv z s) t =
        a * deriv (fun s => D.w s * deriv D.chiLeft s) t := by
    rw [hzf, deriv_const_mul_field]
  have hinput : (fun t => f t + u t * V t) =
      (fun t => f t + j ^ 2 * (deriv D.w t / t) * u t) := by
    funext t
    dsimp only [V]
    ring
  have hfluxV : ∀ r ∈ radialCore D, D.w r * deriv u r =
      intervalLocalPrimitive (fun t => f t + u t * V t) x₀ r + q := by
    intro r hr
    rw [hinput]
    exact hflux r hr
  have hforce :
      (fun t => (f t - (deriv (fun s => D.w s * deriv z s) t - V t * z t)) +
        (u t - z t) * V t) =
      (fun t => (f t - a * deriv (fun s => D.w s * deriv D.chiLeft s) t) +
        j ^ 2 * (deriv D.w t / t) * (u t - a * D.chiLeft t)) := by
    funext t
    change (f t - (deriv (fun s => D.w s * deriv z s) t - V t * z t)) +
      (u t - z t) * V t =
        (f t - a * deriv (fun s => D.w s * deriv D.chiLeft s) t) +
          j ^ 2 * (deriv D.w t / t) * (u t - a * D.chiLeft t)
    rw [hzflux, hVz]
    dsimp only [z, V]
    ring
  intro r hr
  have hb := interval_flux_sub_smooth hu huLp hfLp hgeom.2.2.1.1 hV hz
    x₀ q hx₀ hfluxV r hr
  rw [hforce, hzder] at hb
  exact hb

end ContinuousFlexibility.Radial
