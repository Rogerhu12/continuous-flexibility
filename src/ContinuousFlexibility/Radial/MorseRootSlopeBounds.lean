module

public import ContinuousFlexibility.Radial.MorseCellCriticalPoints

/-!
# The quantitative simple-root scale of an actual Morse height

The model root derivatives have polynomial lower bounds. At a physical
turning point the height amplitude and radius cancel from the normalized
second derivative; the remaining denominator is the cube of the physical
model speed. These identities also apply to a glued profile with the same
local germ.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Filter Real Set
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

/-- Uniform lower and upper bounds at the two actual Morse roots.
The additional separation is satisfied by the small retained parameters. -/
theorem morseRho_turn_derivative_bounds {A B : ℝ}
    (hB : 0 < B) (hAB : 4 * B < A) (hsmall : 8 * B ≤ A) :
    A / 4 ≤ deriv (morseRho A B) (morseLeftTurn A B) ∧
      deriv (morseRho A B) (morseLeftTurn A B) ≤ A ∧
      B / 2 ≤ -deriv (morseRho A B) (morseRightTurn A B) ∧
      -deriv (morseRho A B) (morseRightTurn A B) ≤ 2 * B := by
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  obtain ⟨hR, hRhi, hLlo, hLhi⟩ := morseRootT_bounds hB hAB
  have hdiv : 4 * B / A ≤ (1 / 2 : ℝ) := by
    apply (div_le_iff₀ hA).mpr
    nlinarith only [hsmall]
  have hd : 0 ≤ 1 - 4 * B / A := by linarith only [hdiv]
  have hsqrt : (1 / 2 : ℝ) ≤ sqrt (1 - 4 * B / A) := by
    apply (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) (sqrt_nonneg _)).mp
    rw [sq_sqrt hd]
    nlinarith only [hdiv]
  have hLf : (1 / 2 : ℝ) ≤ 2 * morseLeftRootT A B - 1 := by
    dsimp only [morseLeftRootT]
    linarith only [hsqrt]
  have hLf' : 2 * morseLeftRootT A B - 1 ≤ 1 := by linarith only [hLhi]
  have hRf : (1 / 2 : ℝ) ≤ 1 - 2 * morseRightRootT A B := by
    dsimp only [morseRightRootT]
    linarith only [hsqrt]
  have hRf' : 1 - 2 * morseRightRootT A B ≤ 1 := by linarith only [hR]
  have hratio := morseRightRootT_ratio_bounds hB hAB
  have hleft :
      deriv (morseRho A B) (morseLeftTurn A B) =
        A * (morseLeftRootT A B * (2 * morseLeftRootT A B - 1)) := by
    rw [(hasDerivAt_morseRho A B _).deriv, exp_neg_morseLeftTurn hB hAB]
  have hright :
      -deriv (morseRho A B) (morseRightTurn A B) =
        A * (morseRightRootT A B * (1 - 2 * morseRightRootT A B)) := by
    rw [(hasDerivAt_morseRho A B _).deriv, exp_neg_morseRightTurn hB hAB]
    ring
  rw [hleft, hright]
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc
      A / 4 = A * ((1 / 2 : ℝ) * (1 / 2)) := by ring
      _ ≤ A * (morseLeftRootT A B * (2 * morseLeftRootT A B - 1)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul hLlo.le hLf (by norm_num) (by linarith only [hLlo])) hA.le
  · calc
      A * (morseLeftRootT A B * (2 * morseLeftRootT A B - 1)) ≤ A * (1 * 1) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul hLhi.le hLf' (by linarith only [hLf]) (by norm_num)) hA.le
      _ = A := by ring
  · calc
      B / 2 = A * ((B / A) * (1 / 2)) := by field_simp [hA.ne'] <;> ring
      _ ≤ A * (morseRightRootT A B * (1 - 2 * morseRightRootT A B)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul hratio.1 hRf (by norm_num) hR.le) hA.le
  · calc
      A * (morseRightRootT A B * (1 - 2 * morseRightRootT A B)) ≤
          A * ((2 * (B / A)) * 1) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul hratio.2 hRf' (by linarith only [hRf]) (by positivity)) hA.le
      _ = 2 * B := by field_simp [hA.ne'] <;> ring

/-- The normalized ordinary second derivative at a turning point is
independent of the positive height amplitude. -/
theorem morseCollarExpHeight_rootSlope_eq
    {A B amplitude s a b x : ℝ} {r : ℝ → ℝ}
    (hAmp : 0 < amplitude) (hs : 0 < s) (hr : ContDiff ℝ ∞ r)
    (hv : ∀ t ∈ Ioo a b, 0 < deriv r t) (hx : x ∈ Ioo a b)
    (hrx : 0 < r x)
    (hEq : ∀ t ∈ Ioo a b, deriv (deriv r) t = -morseRho A B t * r t)
    (hRoot : morseRho A B x = 0) :
    |deriv (deriv (morseCollarExpHeight r amplitude s a b)) (s * r x)| /
        ((s * r x) * morseCollarExpHeight r amplitude s a b (s * r x)) =
      |deriv (morseRho A B) x| / (s ^ 3 * deriv r x ^ 3) := by
  rw [morseCollarExpHeight_second_deriv_at_root hAmp hs hr hv hx hEq hRoot,
    morseCollarExpHeight_at_model hAmp hs hr hv hx (hEq x hx)]
  simp only [abs_div, abs_mul, abs_pow, abs_neg, abs_of_pos hAmp,
    abs_of_pos hs, abs_of_pos hrx, abs_of_pos (hv x hx)]
  field_simp [hAmp.ne', hs.ne', hrx.ne', (hv x hx).ne'] <;> ring

/-- The same root scale holds for an actual glued height on any
neighborhood where it equals the Morse cell height. -/
theorem morseCollarExpHeight_rootSlope_eq_of_germ
    {A B amplitude s a b x : ℝ} {r w : ℝ → ℝ}
    (hAmp : 0 < amplitude) (hs : 0 < s) (hr : ContDiff ℝ ∞ r)
    (hv : ∀ t ∈ Ioo a b, 0 < deriv r t) (hx : x ∈ Ioo a b)
    (hrx : 0 < r x)
    (hEq : ∀ t ∈ Ioo a b, deriv (deriv r) t = -morseRho A B t * r t)
    (hRoot : morseRho A B x = 0)
    (hw : w =ᶠ[𝓝 (s * r x)] morseCollarExpHeight r amplitude s a b) :
    |deriv (deriv w) (s * r x)| / ((s * r x) * w (s * r x)) =
      |deriv (morseRho A B) x| / (s ^ 3 * deriv r x ^ 3) := by
  rw [hw.deriv.deriv_eq, hw.eq_of_nhds]
  exact morseCollarExpHeight_rootSlope_eq hAmp hs hr hv hx hrx hEq hRoot

end ContinuousFlexibility.Radial
