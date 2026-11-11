import ContinuousFlexibility.Radial.InnerRadialL2Mass
import ContinuousFlexibility.Radial.MorseCellLiouville

/-!
# The physical Liouville mass on a retained interval

This is the exact local radial mass identity, for the same radius,
profile and field that occur in the differential conjugacy. The
density root covers both the Morse value one and the central
Liouville density. The second theorem converts a model energy bound
into a physical leading Poisson bound without losing the height scale.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory Real
open scoped ContDiff

theorem innerLiouville_mass_change {R s w u ψ : ℝ → ℝ} {a b λ : ℝ}
    (hab : a ≤ b) (hR : ContDiff ℝ ∞ R)
    (hRp : ∀ x ∈ Icc a b, 0 < R x) (hVp : ∀ x ∈ Icc a b, 0 < deriv R x)
    (hs : ∀ x ∈ Icc a b, s x ≠ 0)
    (hw : ∀ x ∈ Icc a b, w (R x) = λ * s x ^ 2 * deriv R x)
    (hu : ∀ x ∈ Icc a b, u (R x) = ψ x / s x) :
    innerRadialGapMass w u (R a) (R b) =
      12 * λ * ∫ x in a..b, ((deriv R x / R x) * ψ x) ^ 2 := by
  have hmono := morseCell_strictMonoOn hR hVp
  have hrange : R a ≤ R b :=
    hmono.monotoneOn (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab) hab
  have him := hR.continuous.continuousOn.image_Ioc_of_strictMonoOn hab hmono
  have hD (x : ℝ) (_hx : x ∈ Ioc a b) : HasDerivWithinAt R (deriv R x) (Ioc a b) x :=
    (hR.differentiable (by simp) x).hasDerivAt.hasDerivWithinAt
  have hi : InjOn R (Ioc a b) := hmono.injOn.mono Ioc_subset_Icc_self
  have hchange := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioc hD hi
    (fun r => (12 * w r / r ^ 2) * u r ^ 2)
  rw [him] at hchange
  rw [innerRadialGapMass, intervalIntegral.integral_of_le hrange, hchange,
    intervalIntegral.integral_of_le hab, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro x hx
  have hx' := Ioc_subset_Icc_self hx
  rw [abs_of_pos (hVp x hx'), smul_eq_mul, hw x hx', hu x hx']
  field_simp [(hRp x hx').ne', hs x hx'] <;> ring

/-- Only the support of the leading field needs the small velocity
bound. In particular the long cap never pays the larger velocity of
the opposite cap. -/
theorem innerLiouville_mass_le_of_model_energy {R s w u ψ : ℝ → ℝ} {a b λ U m α : ℝ}
    (hab : a ≤ b) (hR : ContDiff ℝ ∞ R)
    (hRp : ∀ x ∈ Icc a b, 0 < R x) (hVp : ∀ x ∈ Icc a b, 0 < deriv R x)
    (hs : ∀ x ∈ Icc a b, s x ≠ 0)
    (hw : ∀ x ∈ Icc a b, w (R x) = λ * s x ^ 2 * deriv R x)
    (hu : ∀ x ∈ Icc a b, u (R x) = ψ x / s x)
    (hψ : ContinuousOn ψ (Icc a b)) (hλ : 0 ≤ λ) (hU : 0 ≤ U) (hm : 0 < m)
    (hvelocity : ∀ x ∈ Icc a b, ψ x ≠ 0 → |deriv R x / R x| ≤ U)
    (henergy : m ^ 2 * (∫ x in a..b, ψ x ^ 2) ≤ α) :
    innerRadialGapMass w u (R a) (R b) ≤ 12 * λ * (U / m) ^ 2 * α := by
  have hvcont : ContinuousOn (fun x => deriv R x / R x) (Icc a b) :=
    (contDiff_infty_iff_deriv.mp hR).2.continuous.continuousOn.div
      hR.continuous.continuousOn (fun x hx => (hRp x hx).ne')
  have hI : (∫ x in a..b, ((deriv R x / R x) * ψ x) ^ 2) ≤
      U ^ 2 * ∫ x in a..b, ψ x ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hab
      (((hvcont.mul hψ).pow 2).intervalIntegrable_of_Icc hab)
      ((continuousOn_const.mul (hψ.pow 2)).intervalIntegrable_of_Icc hab)
    intro x hx
    by_cases hz : ψ x = 0
    · simp only [hz, mul_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)]
    · have hv := (sq_le_sq₀ (abs_nonneg (deriv R x / R x)) hU).mpr (hvelocity x hx hz)
      rw [sq_abs] at hv
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right hv (sq_nonneg _)
  have hmodel : (∫ x in a..b, ψ x ^ 2) ≤ α / m ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hm)).mpr
    simpa only [mul_comm (∫ x in a..b, ψ x ^ 2)] using henergy
  rw [innerLiouville_mass_change hab hR hRp hVp hs hw hu]
  calc
    _ ≤ 12 * λ * (U ^ 2 * (∫ x in a..b, ψ x ^ 2)) :=
      mul_le_mul_of_nonneg_left hI (mul_nonneg (by norm_num) hλ)
    _ ≤ 12 * λ * (U ^ 2 * (α / m ^ 2)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hmodel (sq_nonneg U))
        (mul_nonneg (by norm_num) hλ)
    _ = _ := by rw [div_pow]; ring

end ContinuousFlexibility.Radial
