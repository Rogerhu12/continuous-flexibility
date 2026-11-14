module

public import ContinuousFlexibility.Radial.MorseJoinHeightContrast

/-!
# From the endpoint heights to the transfer contrast

The coefficient bound in the join-state system uses the larger of the
two endpoint height ratios. This quantity is unchanged when the direction
of traversal is reversed. The actual logarithmic contrast estimate gives
the exponential bound used in `R07JoinSmallness`.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real

/-- The larger of two reciprocal positive height ratios is at least one. -/
theorem r07_one_le_height_contrast {W Z : ℝ} (hW : 0 < W) (hZ : 0 < Z) :
    1 ≤ max (Z / W) (W / Z) := by
  rcases le_total W Z with h | h
  · have hratio : 1 ≤ Z / W := (le_div_iff₀ hW).mpr (by simpa only [one_mul] using h)
    exact hratio.trans (le_max_left _ _)
  · have hratio : 1 ≤ W / Z := (le_div_iff₀ hZ).mpr (by simpa only [one_mul] using h)
    exact hratio.trans (le_max_right _ _)

/-- Values between the endpoint heights satisfy both relative coefficient
bounds of the join-state system, whichever endpoint supplies the reference
height `W`. -/
theorem r07_height_between_bounds {W Z z : ℝ} (hW : 0 < W) (hZ : 0 < Z)
    (hz : min W Z ≤ z ∧ z ≤ max W Z) :
    0 < z ∧ z ≤ max (Z / W) (W / Z) * W ∧
      W ≤ max (Z / W) (W / Z) * z := by
  let contrast : ℝ := max (Z / W) (W / Z)
  have hcontrast : 1 ≤ contrast := r07_one_le_height_contrast hW hZ
  have hcontrast₀ : 0 ≤ contrast := zero_le_one.trans hcontrast
  have hWW : W ≤ contrast * W := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hcontrast hW.le
  have hZW : Z ≤ contrast * W :=
    (div_le_iff₀ hW).mp (le_max_left _ _)
  have hWZ : W ≤ contrast * Z :=
    (div_le_iff₀ hZ).mp (le_max_right _ _)
  have hmin : W ≤ contrast * min W Z := by
    rcases le_total W Z with h | h
    · rw [min_eq_left h]
      exact hWW
    · rw [min_eq_right h]
      exact hWZ
  exact ⟨(lt_min hW hZ).trans_le hz.1,
    hz.2.trans (max_le hWW hZW),
    hmin.trans (mul_le_mul_of_nonneg_left hz.1 hcontrast₀)⟩

/-- An absolute logarithmic bound controls either direction of height
contrast by the same exponential. -/
theorem r07_height_contrast_le_of_log {W Z H : ℝ} (hW : 0 < W) (hZ : 0 < Z)
    (hlog : |log (Z / W)| ≤ H) :
    max (Z / W) (W / Z) ≤ exp H := by
  have hratio : 0 < Z / W := div_pos hZ hW
  apply max_le
  · calc
      Z / W = exp (log (Z / W)) := (exp_log hratio).symm
      _ ≤ exp H := exp_le_exp.mpr (abs_le.mp hlog).2
  · calc
      W / Z = exp (-log (Z / W)) := by rw [exp_neg, exp_log hratio, inv_div]
      _ ≤ exp H := exp_le_exp.mpr (by linarith only [(abs_le.mp hlog).1])

/-- The actual adjacent-cell contrast estimate supplies the coarse bound
needed at band `n`; the long cap may be cell `n` or the preceding cell. -/
theorem r07_height_contrast_le_of_error {W Z : ℝ} {m n : ℕ}
    (hW : 0 < W) (hZ : 0 < Z) (hm : 100 ≤ m) (hmn : m ≤ n)
    (herror : |log (Z / W) - 4 * (m : ℝ) ^ 2| ≤
      10 * (m : ℝ) ^ (3 / 2 : ℝ) + 2 * (m : ℝ) + 63) :
    1 ≤ max (Z / W) (W / Z) ∧
      max (Z / W) (W / Z) ≤ exp (6 * (n : ℝ) ^ 2) := by
  have hlog := morseJoin_height_log_range_of_error hm herror
  have hlog₀ : 0 ≤ log (Z / W) := (by positivity : (0 : ℝ) ≤ 2 * (m : ℝ) ^ 2).trans hlog.1
  refine ⟨r07_one_le_height_contrast hW hZ, r07_height_contrast_le_of_log hW hZ ?_⟩
  rw [abs_of_nonneg hlog₀]
  exact hlog.2.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (Nat.cast_nonneg m) (Nat.cast_le.mpr hmn) 2) (by norm_num))

end ContinuousFlexibility.Radial
