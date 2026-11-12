import ContinuousFlexibility.Radial.MorseModelReturn

/-!
# Optical density under an actual positive radius scaling

The profile identity is used on an open interval, so its derivative is
the derivative of the actual glued profile. The height factor cancels.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Filter Real Set
open scoped ContDiff Topology

theorem opticalDensity_radius_scaling
    {w W : ℝ → ℝ} {R H a b s : ℝ}
    (hR : 0 < R) (hH : H ≠ 0) (hw : ContDiff ℝ ∞ w) (hW : ContDiff ℝ ∞ W)
    (hprofile : ∀ t ∈ Ioo a b, W (R * t) = H * R * w t)
    (hs : s ∈ Ioo a b) (hs0 : s ≠ 0) (hws : w s ≠ 0) :
    -deriv W (R * s) / ((R * s) * W (R * s)) =
      (-deriv w s / (s * w s)) / R ^ 2 := by
  have he : (fun t : ℝ => W (R * t)) =ᶠ[𝓝 s] (fun t => H * R * w t) := by
    filter_upwards [isOpen_Ioo.mem_nhds hs] with t ht
    exact hprofile t ht
  have hdL : HasDerivAt (fun t : ℝ => W (R * t)) (deriv W (R * s) * R) s := by
    simpa only [mul_one] using
      (hW.differentiable (by simp) (R * s)).hasDerivAt.comp s
        ((hasDerivAt_id s).const_mul R)
  have hdR : HasDerivAt (fun t : ℝ => H * R * w t) ((H * R) * deriv w s) s :=
    (hw.differentiable (by simp) s).hasDerivAt.const_mul (H * R)
  have hd := he.deriv_eq
  rw [hdL.deriv, hdR.deriv] at hd
  have hderiv : deriv W (R * s) = H * deriv w s := by
    apply (mul_right_cancel₀ hR.ne').mp
    calc
      deriv W (R * s) * R = (H * R) * deriv w s := hd
      _ = (H * deriv w s) * R := by ring
  rw [hderiv, hprofile s hs]
  field_simp [hR.ne', hH, hs0, hws] <;> ring

/-- The normalized density costs `R⁻²` and endpoint distance costs `R`;
the lower coefficient therefore becomes exactly `κ / R³`. -/
theorem optical_lower_of_radius_scaling
    {w W : ℝ → ℝ} {R H a b κ : ℝ}
    (hR : 0 < R) (hH : H ≠ 0) (hw : ContDiff ℝ ∞ w) (hW : ContDiff ℝ ∞ W)
    (hprofile : ∀ t ∈ Ioo a b, W (R * t) = H * R * w t)
    (hpos : ∀ t ∈ Ioo a b, t ≠ 0 ∧ w t ≠ 0)
    (hlower : ∀ t ∈ Ioo a b,
      κ * min (t - a) (b - t) ≤ -deriv w t / (t * w t)) :
    ∀ r ∈ Ioo (R * a) (R * b),
      (κ / R ^ 3) * min (r - R * a) (R * b - r) ≤
        -deriv W r / (r * W r) := by
  intro r hr
  let s := r / R
  have hs : s ∈ Ioo a b := by
    constructor
    · exact (lt_div_iff₀ hR).mpr (by simpa only [mul_comm] using hr.1)
    · exact (div_lt_iff₀ hR).mpr (by simpa only [mul_comm] using hr.2)
  have hrs : R * s = r := by dsimp only [s]; field_simp [hR.ne']
  have hm : min (R * s - R * a) (R * b - R * s) =
      R * min (s - a) (b - s) := by
    by_cases he : s - a ≤ b - s
    · have hp : R * s - R * a ≤ R * b - R * s := by
        nlinarith only [mul_le_mul_of_nonneg_left he hR.le]
      rw [min_eq_left he, min_eq_left hp]
      ring
    · have hp : R * b - R * s ≤ R * s - R * a := by
        nlinarith only [mul_le_mul_of_nonneg_left (le_of_not_ge he) hR.le]
      rw [min_eq_right (le_of_not_ge he), min_eq_right hp]
      ring
  rw [← hrs, opticalDensity_radius_scaling hR hH hw hW hprofile hs
    (hpos s hs).1 (hpos s hs).2, hm]
  calc
    _ = (κ * min (s - a) (b - s)) / R ^ 2 := by field_simp [hR.ne']; ring
    _ ≤ _ := div_le_div_of_nonneg_right (hlower s hs) (sq_nonneg R)

theorem optical_lower_scaled_inverse {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R) :
    0 < κ / R ^ 3 ∧ (κ / R ^ 3)⁻¹ = R ^ 3 * κ⁻¹ := by
  exact ⟨div_pos hκ (pow_pos hR 3), by rw [inv_div, div_eq_mul_inv]⟩

end ContinuousFlexibility.Radial
