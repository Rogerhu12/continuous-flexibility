import ContinuousFlexibility.Radial.LogSlopeConnector
import ContinuousFlexibility.Radial.MorsePositiveJoin

/-!
# Quantitative interpolation of a second-mode logarithmic slope

One estimate treats both cone slopes and both ends of the annulus.
The cutoff is constant on neighborhoods of the retained and cone sides.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter
open scoped Topology ContDiff

def connectorInterpolatedSlope (χ k : ℝ → ℝ) (a y : ℝ) : ℝ :=
  a + χ y * (k y - a)

theorem connectorInterpolatedSlope_contDiff {χ k : ℝ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hk : ContDiff ℝ ∞ k) (a : ℝ) :
    ContDiff ℝ ∞ (connectorInterpolatedSlope χ k a) :=
  contDiff_const.add (hχ.mul (hk.sub contDiff_const))

theorem connectorInterpolatedSlope_eq_of_one {χ k : ℝ → ℝ} {a y : ℝ}
    (hχ : χ y = 1) : connectorInterpolatedSlope χ k a y = k y := by
  simp only [connectorInterpolatedSlope, hχ, one_mul]
  ring

theorem connectorInterpolatedSlope_eq_of_zero {χ k : ℝ → ℝ} {a y : ℝ}
    (hχ : χ y = 0) : connectorInterpolatedSlope χ k a y = a := by
  simp only [connectorInterpolatedSlope, hχ, zero_mul, add_zero]

theorem connectorInterpolatedSlope_germ_of_one {χ k : ℝ → ℝ} {a y : ℝ}
    (hχ : χ =ᶠ[𝓝 y] fun _ => 1) :
    connectorInterpolatedSlope χ k a =ᶠ[𝓝 y] k := by
  filter_upwards [hχ] with t ht
  exact connectorInterpolatedSlope_eq_of_one ht

theorem connectorInterpolatedSlope_germ_of_zero {χ k : ℝ → ℝ} {a y : ℝ}
    (hχ : χ =ᶠ[𝓝 y] fun _ => 0) :
    connectorInterpolatedSlope χ k a =ᶠ[𝓝 y] fun _ => a := by
  filter_upwards [hχ] with t ht
  exact connectorInterpolatedSlope_eq_of_zero ht

theorem hasDerivAt_connectorInterpolatedSlope {χ k : ℝ → ℝ} {a y : ℝ}
    (hχ : DifferentiableAt ℝ χ y) (hk : DifferentiableAt ℝ k y) :
    HasDerivAt (connectorInterpolatedSlope χ k a)
      (deriv χ y * (k y - a) + χ y * deriv k y) y :=
  (hχ.hasDerivAt.mul (hk.hasDerivAt.sub_const a)).const_add a

theorem deriv_connectorInterpolatedSlope {χ k : ℝ → ℝ} {a y : ℝ}
    (hχ : DifferentiableAt ℝ χ y) (hk : DifferentiableAt ℝ k y) :
    deriv (connectorInterpolatedSlope χ k a) y =
      deriv χ y * (k y - a) + χ y * deriv k y :=
  (hasDerivAt_connectorInterpolatedSlope hχ hk).deriv

theorem connectorInterpolatedSlope_lt_four {χ k : ℝ → ℝ} {a y : ℝ}
    (hχ0 : 0 ≤ χ y) (hχ1 : χ y ≤ 1) (ha : a < 4) (hk : k y < 4) :
    connectorInterpolatedSlope χ k a y < 4 := by
  by_cases hka : k y ≤ a
  · have hm := mul_nonpos_of_nonneg_of_nonpos hχ0 (sub_nonpos.mpr hka)
    dsimp only [connectorInterpolatedSlope]
    linarith
  · have hm := mul_le_mul_of_nonneg_right hχ1
      (sub_nonneg.mpr (le_of_lt (lt_of_not_ge hka)))
    dsimp only [connectorInterpolatedSlope]
    linarith

theorem connectorInterpolatedSlope_error {χ k : ℝ → ℝ} {a y ε : ℝ}
    (hχ0 : 0 ≤ χ y) (hχ1 : χ y ≤ 1) (hk : |k y - a| ≤ ε) :
    |connectorInterpolatedSlope χ k a y - a| ≤ ε := by
  have hχabs : |χ y| ≤ 1 := by
    simpa only [abs_of_nonneg hχ0] using hχ1
  calc
    |connectorInterpolatedSlope χ k a y - a| =
        |χ y| * |k y - a| := by
      rw [connectorInterpolatedSlope, show a + χ y * (k y - a) - a =
        χ y * (k y - a) by ring, abs_mul]
    _ ≤ 1 * ε := mul_le_mul hχabs hk (abs_nonneg _) zero_le_one
    _ = ε := one_mul ε

theorem connectorInterpolatedSlope_derivative_bound {χ k : ℝ → ℝ}
    {a y B ε η : ℝ} (hχ : DifferentiableAt ℝ χ y)
    (hk : DifferentiableAt ℝ k y) (hB : 0 ≤ B)
    (hχ0 : 0 ≤ χ y) (hχ1 : χ y ≤ 1) (hχ' : |deriv χ y| ≤ B)
    (hk0 : |k y - a| ≤ ε) (hk1 : |deriv k y| ≤ η) :
    |deriv (connectorInterpolatedSlope χ k a) y| ≤ B * ε + η := by
  rw [deriv_connectorInterpolatedSlope hχ hk]
  have hχabs : |χ y| ≤ 1 := by
    simpa only [abs_of_nonneg hχ0] using hχ1
  calc
    |deriv χ y * (k y - a) + χ y * deriv k y| ≤
        |deriv χ y * (k y - a)| + |χ y * deriv k y| := abs_add_le _ _
    _ = |deriv χ y| * |k y - a| + |χ y| * |deriv k y| := by
      rw [abs_mul, abs_mul]
    _ ≤ B * ε + 1 * η :=
      add_le_add (mul_le_mul hχ' hk0 (abs_nonneg _) hB)
        (mul_le_mul hχabs hk1 (abs_nonneg _) zero_le_one)
    _ = B * ε + η := by rw [one_mul]

theorem connector_ratio_ge_three_quarters {a k d : ℝ}
    (ha : a ^ 2 = 4) (hk : |k - a| ≤ 1 / 16) (hd : |d| ≤ 1 / 16) :
    k < 4 ∧ (3 / 4 : ℝ) ≤ (k ^ 2 - k + d) / (4 - k) := by
  have ha' : a = 2 ∨ a = -2 := by
    have hprod : (a - 2) * (a + 2) = 0 := by nlinarith [ha]
    rcases mul_eq_zero.mp hprod with h | h
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  have hk' := abs_le.mp hk
  have hd' := abs_le.mp hd
  rcases ha' with rfl | rfl
  · have hk4 : k < 4 := by linarith [hk'.2]
    refine ⟨hk4, (le_div_iff₀ (sub_pos.mpr hk4)).mpr ?_⟩
    nlinarith [sq_nonneg (k - 2)]
  · have hk4 : k < 4 := by linarith [hk'.2]
    refine ⟨hk4, (le_div_iff₀ (sub_pos.mpr hk4)).mpr ?_⟩
    nlinarith [sq_nonneg (k + 2)]

def connectorInterpolationTolerance (B : ℝ) : ℝ := 1 / (16 * (B + 1))

theorem connectorInterpolationTolerance_pos {B : ℝ} (hB : 0 ≤ B) :
    0 < connectorInterpolationTolerance B := by
  unfold connectorInterpolationTolerance
  positivity

theorem connectorInterpolationTolerance_le {B : ℝ} (hB : 0 ≤ B) :
    connectorInterpolationTolerance B ≤ 1 / 16 := by
  unfold connectorInterpolationTolerance
  apply (div_le_iff₀ (by positivity : 0 < 16 * (B + 1))).mpr
  linarith

theorem connectorInterpolationTolerance_budget {B : ℝ} (hB : 0 ≤ B) :
    B * connectorInterpolationTolerance B + connectorInterpolationTolerance B =
      1 / 16 := by
  have hden : 16 * (B + 1) ≠ 0 := (show 0 < 16 * (B + 1) by positivity).ne'
  have hc : connectorInterpolationTolerance B * (16 * (B + 1)) = 1 :=
    div_mul_cancel₀ 1 hden
  nlinarith [hc]

theorem connectorInterpolatedSlope_admissible {χ k : ℝ → ℝ} {a y B : ℝ}
    (hχ : DifferentiableAt ℝ χ y) (hk : DifferentiableAt ℝ k y)
    (ha : a ^ 2 = 4) (hB : 0 ≤ B)
    (hχ0 : 0 ≤ χ y) (hχ1 : χ y ≤ 1) (hχ' : |deriv χ y| ≤ B)
    (hk0 : |k y - a| ≤ connectorInterpolationTolerance B)
    (hk1 : |deriv k y| ≤ connectorInterpolationTolerance B) :
    connectorInterpolatedSlope χ k a y < 4 ∧
      (3 / 4 : ℝ) ≤
        (connectorInterpolatedSlope χ k a y ^ 2 -
          connectorInterpolatedSlope χ k a y +
          deriv (connectorInterpolatedSlope χ k a) y) /
        (4 - connectorInterpolatedSlope χ k a y) := by
  apply connector_ratio_ge_three_quarters ha
  · exact (connectorInterpolatedSlope_error hχ0 hχ1 hk0).trans
      (connectorInterpolationTolerance_le hB)
  · exact (connectorInterpolatedSlope_derivative_bound hχ hk hB hχ0 hχ1
      hχ' hk0 hk1).trans_eq (connectorInterpolationTolerance_budget hB)

/-- Keep the old slope on the central side of the splice. -/
def connectorRetainWeight (right : Bool) (cut y : ℝ) : ℝ :=
  if right then morseJoinLeftWeight cut 1 y else morseJoinRightWeight cut 1 y

theorem connectorRetainWeight_contDiff (right : Bool) (cut : ℝ) :
    ContDiff ℝ ∞ (connectorRetainWeight right cut) := by
  cases right with
  | false => exact contDiff_morseJoinRightWeight cut 1
  | true => exact contDiff_morseJoinLeftWeight cut 1

theorem connectorRetainWeight_bounds (right : Bool) (cut y : ℝ) :
    0 ≤ connectorRetainWeight right cut y ∧
      connectorRetainWeight right cut y ≤ 1 := by
  cases right <;> exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

theorem connectorRetainWeight_one (right : Bool) (cut y : ℝ)
    (hy : if right then y ≤ cut + 1 / 2 else cut - 1 / 2 ≤ y) :
    connectorRetainWeight right cut y = 1 := by
  cases right with
  | false => exact morseJoinRightWeight_one (by norm_num) hy
  | true => exact morseJoinLeftWeight_one (by norm_num) hy

theorem connectorRetainWeight_zero (right : Bool) (cut y : ℝ)
    (hy : if right then cut + 1 ≤ y else y ≤ cut - 1) :
    connectorRetainWeight right cut y = 0 := by
  cases right with
  | false => exact morseJoinRightWeight_zero (by norm_num) hy
  | true => exact morseJoinLeftWeight_zero (by norm_num) hy

theorem connectorRetainWeight_one_near (right : Bool) (cut : ℝ) :
    connectorRetainWeight right cut =ᶠ[𝓝 cut] fun _ => 1 := by
  filter_upwards [Ioo_mem_nhds (show cut - 1 / 2 < cut by linarith)
    (show cut < cut + 1 / 2 by linarith)] with y hy
  apply connectorRetainWeight_one
  cases right with
  | false => exact hy.1.le
  | true => exact hy.2.le

theorem exists_connectorRetainWeight_derivative_bound :
    ∃ B : ℝ, 0 < B ∧ ∀ right : Bool, ∀ cut y : ℝ,
      |deriv (connectorRetainWeight right cut) y| ≤ B := by
  obtain ⟨C, hC, hb⟩ := exists_morseJoinWeight_jet_bound 1
  refine ⟨2 * C + 1, by positivity, ?_⟩
  intro right cut y
  have h := hb cut cut 1 (by norm_num) y
  simp only [iteratedDeriv_one, div_one, pow_one] at h
  cases right with
  | false =>
    change |deriv (morseJoinRightWeight cut 1) y| ≤ 2 * C + 1
    linarith [h.2]
  | true =>
    change |deriv (morseJoinLeftWeight cut 1) y| ≤ 2 * C + 1
    linarith [h.1]

end ContinuousFlexibility.Radial
