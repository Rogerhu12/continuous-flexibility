module

public import ContinuousFlexibility.Analysis.N06RadialGeometryJets
public import ContinuousFlexibility.Analysis.N06PositiveWeakGraph

/-!
# Primitive radial bounds imply the unit modal coefficient bounds

The inputs concern w, H, Y, and the smooth inverse extension R. Their
finite jets and positive lower bounds give an explicit polynomial bound
for the actual radial formulas. In particular no modal equation or graph
estimate is included among the inputs.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped ContDiff
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

/-- R is a smooth extension of the inverse on the unit interval. Its
extension need only avoid the three denominators; it need not be a
global inverse of Y. -/
structure N06RadialPrimitiveRegularity (w H Y R : ℝ → ℝ) : Prop where
  profile : ContDiff ℝ ∞ w
  height : ContDiff ℝ ∞ H
  coordinate : ContDiff ℝ ∞ Y
  inverse : ContDiff ℝ ∞ R
  radius_ne : ∀ y, R y ≠ 0
  profile_ne : ∀ y, w (R y) ≠ 0
  slope_ne : ∀ y, deriv Y (R y) ≠ 0

/-- The finite bounds are on the primitive fields after substitution of
the inverse coordinate. The angular lower bound is on the physical
quantity w'/r and the two endpoint distances in the unit coordinate. -/
structure N06RadialPrimitiveJetBounds
    (w H Y R : ℝ → ℝ) (y B : ℝ) : Prop where
  radius : N06ScalarJetTwoBound R y B
  profile : N06ScalarJetTwoBound (fun t => w (R t)) y B
  profile_derivative : N06ScalarJetTwoBound (fun t => deriv w (R t)) y B
  height : N06ScalarJetTwoBound (fun t => H (R t)) y B
  slope : N06ScalarJetTwoBound (fun t => deriv Y (R t)) y B
  radius_lower : 1 / B ≤ R y
  profile_lower : 1 / B ≤ w (R y)
  height_lower : 1 / B ≤ H (R y)
  slope_lower : 1 / B ≤ deriv Y (R y)
  angular_lower : cylinderWeight y / B ≤ deriv w (R y) / R y
  height_first : |deriv H (R y)| ≤ B
  height_second : |deriv (deriv H) (R y)| ≤ B

def n06RadialReferenceConstant (B : ℝ) : ℝ := 65536 * B ^ 25

theorem n06_radialReferenceConstant_dominates {B C : ℝ} {n : ℕ}
    (hB : 1 ≤ B) (hn : n ≤ 25) (hC : C ≤ 65536) :
    C * B ^ n ≤ n06RadialReferenceConstant B := by
  exact mul_le_mul hC (pow_le_pow_right₀ hB hn)
    (pow_nonneg (zero_le_one.trans hB) _) (by norm_num)

theorem n06_radialReferenceConstant_one_le {B : ℝ} (hB : 1 ≤ B) :
    1 ≤ n06RadialReferenceConstant B := by
  simpa only [pow_zero, mul_one] using
    n06_radialReferenceConstant_dominates (C := 1) hB (by norm_num : 0 ≤ 25) (by norm_num)

theorem n06_abs_inv_le_of_lower {B t : ℝ}
    (hB : 0 < B) (hlower : 1 / B ≤ t) : |t⁻¹| ≤ B := by
  have ht : 0 < t := (one_div_pos.mpr hB).trans_le hlower
  rw [abs_of_pos (inv_pos.mpr ht), inv_eq_one_div]
  apply (div_le_iff₀ ht).2
  simpa only [mul_comm] using (div_le_iff₀ hB).1 hlower

theorem N06RadialPrimitiveRegularity.coefficients_smooth
    {w H Y R : ℝ → ℝ} (h : N06RadialPrimitiveRegularity w H Y R) :
    ContDiff ℝ ∞ (n06RadialReferenceA w H Y R) ∧
      ContDiff ℝ ∞ (n06RadialReferenceC w H Y R) ∧
      ContDiff ℝ ∞ (n06RadialReferenceV w H Y R) ∧
      ContDiff ℝ ∞ (n06RadialReferenceQ w Y R) := by
  have hw := h.profile.comp h.inverse
  have hw' := (contDiff_infty_iff_deriv.mp h.profile).2.comp h.inverse
  have hH := h.height.comp h.inverse
  have hH' := (contDiff_infty_iff_deriv.mp h.height).2
  have hH'' := (contDiff_infty_iff_deriv.mp hH').2
  have hs := (contDiff_infty_iff_deriv.mp h.coordinate).2.comp h.inverse
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ((hH.pow 2).mul hw).mul hs
  · exact ((hH.pow 2).mul (hw'.div h.inverse h.radius_ne)).div hs h.slope_ne
  · exact (hH.mul ((hw'.mul (hH'.comp h.inverse)).add
      (hw.mul (hH''.comp h.inverse)))).neg.div hs h.slope_ne
  · exact (hw'.div h.inverse h.radius_ne).div (hw.mul (hs.pow 2))
      (fun y => mul_ne_zero (h.profile_ne y) (pow_ne_zero 2 (h.slope_ne y)))

theorem n06_radialReferenceA_jet_bound
    {w H Y R : ℝ → ℝ} (h : N06RadialPrimitiveRegularity w H Y R)
    {y B : ℝ} (hB : 1 ≤ B) (hb : N06RadialPrimitiveJetBounds w H Y R y B) :
    N06ScalarJetTwoBound (n06RadialReferenceA w H Y R) y (64 * B ^ 4) := by
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hH := h.height.comp h.inverse
  have hw := h.profile.comp h.inverse
  have hs := (contDiff_infty_iff_deriv.mp h.coordinate).2.comp h.inverse
  have h1 := N06ScalarJetTwoBound.mul hH hH hB0 hB0 hb.height hb.height
  have h2 := N06ScalarJetTwoBound.mul (hH.mul hH) hw (by positivity) hB0 h1 hb.profile
  have h3 := N06ScalarJetTwoBound.mul ((hH.mul hH).mul hw) hs
    (by positivity) hB0 h2 hb.slope
  have he : n06RadialReferenceA w H Y R =
      fun t => (H (R t) * H (R t) * w (R t)) * deriv Y (R t) := by
    funext t
    simp only [n06RadialReferenceA, pow_two]
  rw [he]
  have hnum : 4 * (4 * (4 * B * B) * B) * B = 64 * B ^ 4 := by ring
  simpa only [hnum, Function.comp_apply, Pi.mul_apply] using h3

theorem n06_radialReferenceQ_jet_bound
    {w H Y R : ℝ → ℝ} (h : N06RadialPrimitiveRegularity w H Y R)
    {y B : ℝ} (hB : 1 ≤ B) (hb : N06RadialPrimitiveJetBounds w H Y R y B) :
    N06ScalarJetTwoBound (n06RadialReferenceQ w Y R) y (62208 * B ^ 25) := by
  have hBpos : 0 < B := zero_lt_one.trans_le hB
  have hw := h.profile.comp h.inverse
  have hw' := (contDiff_infty_iff_deriv.mp h.profile).2.comp h.inverse
  have hs := (contDiff_infty_iff_deriv.mp h.coordinate).2.comp h.inverse
  have hRi := h.inverse.inv h.radius_ne
  have hwi := hw.inv h.profile_ne
  have hsi := hs.inv h.slope_ne
  let J : ℝ := 3 * B ^ 5
  have hJ0 : 0 ≤ J := by dsimp only [J]; positivity
  have hBJ : B ≤ J := by
    have hp : B ≤ B ^ 5 := by
      simpa only [pow_one] using pow_le_pow_right₀ hB (by norm_num : 1 ≤ 5)
    dsimp only [J]
    nlinarith [pow_nonneg hBpos.le 5]
  have h0 := hb.profile_derivative.mono hBJ
  have h1 := N06ScalarJetTwoBound.inv h.inverse h.radius_ne hB hb.radius
    (n06_abs_inv_le_of_lower hBpos hb.radius_lower)
  have h2 := N06ScalarJetTwoBound.inv hw h.profile_ne hB hb.profile
    (n06_abs_inv_le_of_lower hBpos hb.profile_lower)
  have h3 := N06ScalarJetTwoBound.inv hs h.slope_ne hB hb.slope
    (n06_abs_inv_le_of_lower hBpos hb.slope_lower)
  have h01 := N06ScalarJetTwoBound.mul hw' hRi hJ0 hJ0 h0 h1
  have h012 := N06ScalarJetTwoBound.mul (hw'.mul hRi) hwi
    (by positivity) hJ0 h01 h2
  have h0123 := N06ScalarJetTwoBound.mul ((hw'.mul hRi).mul hwi) hsi
    (by positivity) hJ0 h012 h3
  have h01233 := N06ScalarJetTwoBound.mul (((hw'.mul hRi).mul hwi).mul hsi) hsi
    (by positivity) hJ0 h0123 h3
  have he : n06RadialReferenceQ w Y R = fun t =>
      (((deriv w (R t) * (R t)⁻¹) * (w (R t))⁻¹) *
        (deriv Y (R t))⁻¹) * (deriv Y (R t))⁻¹ := by
    funext t
    simp only [n06RadialReferenceQ, div_eq_mul_inv, mul_inv_rev, inv_pow, pow_two]
    ring
  rw [he]
  have hnum : 4 * (4 * (4 * (4 * J * J) * J) * J) * J = 62208 * B ^ 25 := by
    dsimp only [J]
    ring
  simpa only [hnum, Function.comp_apply, Pi.mul_apply, Pi.inv_apply] using h01233

theorem n06_radialReferenceA_lower
    {w H Y R : ℝ → ℝ} {y B : ℝ}
    (hB : 1 ≤ B) (hb : N06RadialPrimitiveJetBounds w H Y R y B) :
    1 / B ^ 4 ≤ n06RadialReferenceA w H Y R y := by
  have hBpos : 0 < B := zero_lt_one.trans_le hB
  have hi : 0 ≤ 1 / B := (one_div_pos.mpr hBpos).le
  have hw : 0 ≤ w (R y) := hi.trans hb.profile_lower
  have hh : (1 / B) ^ 2 ≤ H (R y) ^ 2 :=
    pow_le_pow_left₀ hi hb.height_lower 2
  calc
    _ = (1 / B) ^ 2 * (1 / B) * (1 / B) := by field_simp
    _ ≤ H (R y) ^ 2 * w (R y) * deriv Y (R y) :=
      mul_le_mul (mul_le_mul hh hb.profile_lower hi (sq_nonneg _))
        hb.slope_lower hi (mul_nonneg (sq_nonneg _) hw)
    _ = _ := rfl

theorem n06_radialReferenceC_lower
    {w H Y R : ℝ → ℝ} {y B : ℝ}
    (hB : 1 ≤ B) (hy : y ∈ Icc (0 : ℝ) 1)
    (hb : N06RadialPrimitiveJetBounds w H Y R y B) :
    cylinderWeight y / B ^ 4 ≤ n06RadialReferenceC w H Y R y := by
  have hBpos : 0 < B := zero_lt_one.trans_le hB
  have hi : 0 ≤ 1 / B := (one_div_pos.mpr hBpos).le
  have hd : 0 ≤ cylinderWeight y := cylinderWeight_nonneg hy
  have hspos : 0 < deriv Y (R y) := (one_div_pos.mpr hBpos).trans_le hb.slope_lower
  have hsupper : deriv Y (R y) ≤ B := (le_abs_self _).trans hb.slope.value
  have hh : (1 / B) ^ 2 ≤ H (R y) ^ 2 :=
    pow_le_pow_left₀ hi hb.height_lower 2
  have hρ : 0 ≤ deriv w (R y) / R y :=
    (div_nonneg hd hBpos.le).trans hb.angular_lower
  have hnum := mul_le_mul hh hb.angular_lower (div_nonneg hd hBpos.le) (sq_nonneg (H (R y)))
  calc
    _ = ((1 / B) ^ 2 * (cylinderWeight y / B)) / B := by field_simp
    _ ≤ (H (R y) ^ 2 * (deriv w (R y) / R y)) / B :=
      div_le_div_of_nonneg_right hnum hBpos.le
    _ ≤ (H (R y) ^ 2 * (deriv w (R y) / R y)) / deriv Y (R y) :=
      div_le_div_of_nonneg_left (mul_nonneg (sq_nonneg _) hρ) hspos hsupper
    _ = _ := rfl

theorem n06_radialReferenceV_bound
    {w H Y R : ℝ → ℝ} {y B : ℝ}
    (hB : 1 ≤ B) (hb : N06RadialPrimitiveJetBounds w H Y R y B) :
    |n06RadialReferenceV w H Y R y| ≤ 2 * B ^ 4 := by
  have hBpos : 0 < B := zero_lt_one.trans_le hB
  have h1 : |deriv w (R y) * deriv H (R y)| ≤ B * B := by
    rw [abs_mul]
    exact mul_le_mul hb.profile_derivative.value hb.height_first (abs_nonneg _) hBpos.le
  have h2 : |w (R y) * deriv (deriv H) (R y)| ≤ B * B := by
    rw [abs_mul]
    exact mul_le_mul hb.profile.value hb.height_second (abs_nonneg _) hBpos.le
  have hinv := n06_abs_inv_le_of_lower hBpos hb.slope_lower
  change |-(H (R y) * (deriv w (R y) * deriv H (R y) +
    w (R y) * deriv (deriv H) (R y))) / deriv Y (R y)| ≤ _
  rw [abs_div, abs_neg, abs_mul, div_eq_mul_inv, ← abs_inv]
  calc
    _ ≤ (B * (B * B + B * B)) * B :=
      mul_le_mul
        (mul_le_mul hb.height.value ((abs_add_le _ _).trans (add_le_add h1 h2))
          (abs_nonneg _) hBpos.le) hinv (abs_nonneg _) (by positivity)
    _ = 2 * B ^ 4 := by ring

/-- All numerical hypotheses of the unit weak graph theorem follow from
the finite primitive bounds, with one explicit polynomial constant. -/
theorem n06_radialReference_modal_bounds
    {w H Y R : ℝ → ℝ} (h : N06RadialPrimitiveRegularity w H Y R)
    {y B : ℝ} (hB : 1 ≤ B) (hy : y ∈ Icc (0 : ℝ) 1)
    (hb : N06RadialPrimitiveJetBounds w H Y R y B) :
    1 / n06RadialReferenceConstant B ≤ n06RadialReferenceA w H Y R y ∧
      n06RadialReferenceA w H Y R y ≤ n06RadialReferenceConstant B ∧
      |deriv (n06RadialReferenceA w H Y R) y| ≤ n06RadialReferenceConstant B ∧
      cylinderWeight y / n06RadialReferenceConstant B ≤ n06RadialReferenceC w H Y R y ∧
      |n06RadialReferenceV w H Y R y| ≤ n06RadialReferenceConstant B ∧
      n06RadialReferenceC w H Y R y =
        n06RadialReferenceA w H Y R y * n06RadialReferenceQ w Y R y ∧
      |deriv (deriv (n06RadialReferenceQ w Y R)) y| ≤ n06RadialReferenceConstant B := by
  have hBpos : 0 < B := zero_lt_one.trans_le hB
  have hB4 : B ^ 4 ≤ n06RadialReferenceConstant B := by
    simpa only [one_mul] using
      n06_radialReferenceConstant_dominates (C := 1) hB (by norm_num : 4 ≤ 25) (by norm_num)
  have h64 := n06_radialReferenceConstant_dominates (C := 64) hB
    (by norm_num : 4 ≤ 25) (by norm_num)
  have h2 := n06_radialReferenceConstant_dominates (C := 2) hB
    (by norm_num : 4 ≤ 25) (by norm_num)
  have h62208 := n06_radialReferenceConstant_dominates (C := 62208) hB
    (by norm_num : 25 ≤ 25) (by norm_num)
  have ha := n06_radialReferenceA_jet_bound h hB hb
  refine ⟨?_, (le_abs_self _).trans (ha.value.trans h64), ha.first.trans h64,
    ?_, (n06_radialReferenceV_bound hB hb).trans h2,
    n06_radialReferenceC_eq_aq w H Y R y (h.profile_ne y) (h.slope_ne y),
    (n06_radialReferenceQ_jet_bound h hB hb).second.trans h62208⟩
  · exact (div_le_div_of_nonneg_left zero_le_one (pow_pos hBpos 4) hB4).trans
      (n06_radialReferenceA_lower hB hb)
  · exact (div_le_div_of_nonneg_left (cylinderWeight_nonneg hy) (pow_pos hBpos 4) hB4).trans
      (n06_radialReferenceC_lower hB hy hb)

end ContinuousFlexibility.Analysis
