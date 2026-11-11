import ContinuousFlexibility.Radial.R07DeepTailDensity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Exact outward-coordinate mass and resistance identities

The physical density in the `R06` statement is normalized by the endpoint
radius.  These finite-interval substitution identities relate its
frequency-two mass and resistance to the exact radial integrands in `R05`.
The single orientation sign treats the reversed left-tail interval and the
right-tail interval in the same statement.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory Real
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

def r07OutwardSign (right : Bool) : ℝ := if right then 1 else -1

theorem r07_outwardSign_mul_self (right : Bool) :
    r07OutwardSign right * r07OutwardSign right = 1 := by
  cases right <;> norm_num [r07OutwardSign]

theorem r07_hasDerivAt_radius (right : Bool) (x : ℝ) :
    HasDerivAt (tailPhysicalRadius right)
      (r07OutwardSign right * tailPhysicalRadius right x) x := by
  cases right
  · simp only [tailPhysicalRadius, r07OutwardSign, Bool.false_eq_true, if_false, neg_one_mul]
    simpa only [Function.comp_def, mul_neg_one] using
      (hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)
  · simp only [tailPhysicalRadius, r07OutwardSign, if_true, one_mul]
    exact hasDerivAt_exp x

/-- Substitution by the outward radius map, with the orientation recorded
explicitly outside the physical radial integral. -/
theorem r07_integral_radius_change (right : Bool) (a b : ℝ) {f : ℝ → ℝ}
    (hf : ContinuousOn f (tailPhysicalRadius right '' uIcc a b)) :
    (∫ x in a..b, f (tailPhysicalRadius right x) * tailPhysicalRadius right x) =
      r07OutwardSign right *
        (∫ r in tailPhysicalRadius right a..tailPhysicalRadius right b, f r) := by
  have hchange := intervalIntegral.integral_comp_mul_deriv'
    (a := a) (b := b) (f := tailPhysicalRadius right)
    (f' := fun x => r07OutwardSign right * tailPhysicalRadius right x)
    (g := f) (fun x _ => r07_hasDerivAt_radius right x)
    (continuous_const.mul (r07_contDiff_radius right).continuous).continuousOn hf
  have hfactor :
      (∫ x in a..b, (f ∘ tailPhysicalRadius right) x *
        (r07OutwardSign right * tailPhysicalRadius right x)) =
      r07OutwardSign right *
        (∫ x in a..b, f (tailPhysicalRadius right x) * tailPhysicalRadius right x) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _
    simp only [Function.comp_apply]
    ring
  rw [hfactor] at hchange
  calc
    _ = r07OutwardSign right * (r07OutwardSign right *
        (∫ x in a..b, f (tailPhysicalRadius right x) * tailPhysicalRadius right x)) := by
      rw [← mul_assoc, r07_outwardSign_mul_self, one_mul]
    _ = _ := by rw [hchange]

theorem r07_density_two_pullback {D : ReferenceData} (right : Bool) (x : ℝ)
    (he : 0 < (if right then D.b else D.a)) :
    r07PhysicalDensity D right 2 x =
      ((if right then D.b else D.a) ^ 8)⁻¹ *
        (D.w (tailPhysicalRadius right x) * tailPhysicalRadius right x ^ 6) *
        tailPhysicalRadius right x := by
  have hr : tailPhysicalRadius right x ≠ 0 := (r07_radius_pos right x).ne'
  have hpow :
      (tailPhysicalRadius right x / (if right then D.b else D.a)) ^
          (2 * (2 : ℝ) ^ 2) =
        (tailPhysicalRadius right x / (if right then D.b else D.a)) ^ (8 : ℕ) := by
    rw [show 2 * (2 : ℝ) ^ 2 = (8 : ℝ) by norm_num]
    exact rpow_natCast _ 8
  unfold r07PhysicalDensity
  simp only [Nat.cast_ofNat]
  rw [hpow]
  field_simp [hr, he.ne']

theorem r07_density_two_inverse_pullback {D : ReferenceData} (right : Bool) (x : ℝ)
    (he : 0 < (if right then D.b else D.a))
    (hw : D.w (tailPhysicalRadius right x) ≠ 0) :
    (r07PhysicalDensity D right 2 x)⁻¹ =
      (if right then D.b else D.a) ^ 8 *
        (D.w (tailPhysicalRadius right x) * tailPhysicalRadius right x ^ 8)⁻¹ *
        tailPhysicalRadius right x := by
  rw [r07_density_two_pullback right x he]
  field_simp [(r07_radius_pos right x).ne', he.ne', hw]

/-- The exact frequency-two mass in logarithmic coordinates, including the
constant normalization at the endpoint and the left-tail orientation. -/
theorem r07_density_two_mass_change {D : ReferenceData} (right : Bool) (a b : ℝ)
    (he : 0 < (if right then D.b else D.a)) (hw : Continuous D.w) :
    (∫ x in a..b, r07PhysicalDensity D right 2 x) =
      ((if right then D.b else D.a) ^ 8)⁻¹ * r07OutwardSign right *
        (∫ r in tailPhysicalRadius right a..tailPhysicalRadius right b, D.w r * r ^ 6) := by
  calc
    _ = ∫ x in a..b, ((if right then D.b else D.a) ^ 8)⁻¹ *
        (D.w (tailPhysicalRadius right x) * tailPhysicalRadius right x ^ 6 *
          tailPhysicalRadius right x) := by
      apply intervalIntegral.integral_congr
      intro x _
      rw [r07_density_two_pullback right x he]
      ring
    _ = ((if right then D.b else D.a) ^ 8)⁻¹ *
        (∫ x in a..b, D.w (tailPhysicalRadius right x) * tailPhysicalRadius right x ^ 6 *
          tailPhysicalRadius right x) := intervalIntegral.integral_const_mul _ _
    _ = _ := by
      have hc : ContinuousOn (fun r : ℝ => D.w r * r ^ 6)
          (tailPhysicalRadius right '' uIcc a b) :=
        (hw.mul (continuous_id.pow 6)).continuousOn
      have hsub := r07_integral_radius_change right a b hc
      rw [hsub]
      ring

/-- The exact resistance identity.  Only nonvanishing on the physical
interval is required to justify continuity of the reciprocal integrand. -/
theorem r07_density_two_resistance_change {D : ReferenceData} (right : Bool) (a b : ℝ)
    (he : 0 < (if right then D.b else D.a)) (hw : Continuous D.w)
    (hw0 : ∀ x ∈ uIcc a b, D.w (tailPhysicalRadius right x) ≠ 0) :
    (∫ x in a..b, (r07PhysicalDensity D right 2 x)⁻¹) =
      (if right then D.b else D.a) ^ 8 * r07OutwardSign right *
        (∫ r in tailPhysicalRadius right a..tailPhysicalRadius right b, (D.w r * r ^ 8)⁻¹) := by
  have hcont : ContinuousOn (fun r : ℝ => (D.w r * r ^ 8)⁻¹)
      (tailPhysicalRadius right '' uIcc a b) := by
    apply (hw.mul (continuous_id.pow 8)).continuousOn.inv₀
    rintro r ⟨x, hx, rfl⟩
    exact mul_ne_zero (hw0 x hx) (pow_ne_zero 8 (r07_radius_pos right x).ne')
  calc
    _ = ∫ x in a..b, (if right then D.b else D.a) ^ 8 *
        ((D.w (tailPhysicalRadius right x) * tailPhysicalRadius right x ^ 8)⁻¹ *
          tailPhysicalRadius right x) := by
      apply intervalIntegral.integral_congr
      intro x hx
      dsimp only
      rw [r07_density_two_inverse_pullback right x he (hw0 x hx)]
      ring
    _ = (if right then D.b else D.a) ^ 8 *
        (∫ x in a..b, (D.w (tailPhysicalRadius right x) * tailPhysicalRadius right x ^ 8)⁻¹ *
          tailPhysicalRadius right x) := intervalIntegral.integral_const_mul _ _
    _ = _ := by
      have hsub := r07_integral_radius_change right a b hcont
      rw [hsub]
      ring

end ContinuousFlexibility.Radial
