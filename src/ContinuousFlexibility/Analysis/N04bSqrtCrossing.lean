module

public import ContinuousFlexibility.Analysis.N04bSqrtAffine
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# An affine optical radicand cannot cross zero smoothly

`Real.sqrt` is zero on the negative half-line. Its total extension still
cannot be differentiable at a transverse zero. Consequently a positive
affine radicand stays positive along a segment on which its actual square
root is differentiable at every parameter. No positivity is assumed away
from the initial parameter.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set

set_option backward.isDefEq.respectTransparency false

theorem n04b_not_differentiableAt_sqrt_zero :
    ¬ DifferentiableAt ℝ Real.sqrt 0 :=
  n04b_sqrt_not_differentiableAt_zero

theorem n04b_not_differentiableAt_sqrt_affine_zero
    {a b t : ℝ} (hb : b ≠ 0) (hzero : a + b * t = 0) :
    ¬ DifferentiableAt ℝ (fun s : ℝ => Real.sqrt (a + b * s)) t :=
  n04b_sqrt_affine_not_differentiableAt_zero hzero hb

theorem n04b_affine_pos_of_sqrt_differentiable
    {a b : ℝ} (ha : 0 < a)
    (hregular : ∀ t ∈ Icc (0 : ℝ) 1,
      DifferentiableAt ℝ (fun s : ℝ => Real.sqrt (a + b * s)) t) :
    0 < a + b := by
  by_contra h
  have hab : a + b ≤ 0 := le_of_not_gt h
  have hb : b < 0 := by linarith
  have hden : 0 < -b := neg_pos.mpr hb
  have ht0 : 0 ≤ a / (-b) := (div_pos ha hden).le
  have ht1 : a / (-b) ≤ 1 := (div_le_iff₀ hden).mpr (by linarith)
  have hzero : a + b * (a / (-b)) = 0 := by
    field_simp [hb.ne]
    <;> ring
  exact n04b_not_differentiableAt_sqrt_affine_zero hb.ne hzero
    (hregular (a / (-b)) ⟨ht0, ht1⟩)

end ContinuousFlexibility.Analysis
