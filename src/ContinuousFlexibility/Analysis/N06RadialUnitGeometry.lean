module

public import ContinuousFlexibility.Analysis.N06RadialPrimitiveBounds

/-!
# The unit graph geometry of a controlled radial family

The coefficient functions are the actual formulas in the profile, height,
coordinate and inverse. A uniform material bound for their primitive jets
gives the precise geometric package used by the positive weak graph theorem.
The multiplicative constant and material exponent remain independent; no
lower bound by one is required for the material envelope.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped ContDiff
open ContinuousFlexibility.Statements

theorem n06_radialReferenceConstant_material_bound {B C E A : ℝ}
    (hB : 0 ≤ B) (hE : 0 ≤ E) (hbound : B ≤ C * E ^ A) :
    n06RadialReferenceConstant B ≤ (65536 * C ^ 25) * E ^ (A * 25) := by
  calc
    n06RadialReferenceConstant B = 65536 * B ^ 25 := rfl
    _ ≤ 65536 * (C * E ^ A) ^ 25 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hB hbound 25) (by norm_num)
    _ = (65536 * C ^ 25) * E ^ (A * 25) := by
      rw [mul_pow, ← Real.rpow_mul_natCast hE A 25]
      ring

/-- Primitive radial geometry supplies all modal hypotheses, for the
actual coefficient formulas on every positive piece. -/
theorem n06_positiveUnitGeometry_of_radial_primitives
    {S : PhysicalSpacesData} (T : MaterialData) (K : CanonicalData S)
    (w : ℝ → ℝ) (H Y R : ℕ → ℝ → ℝ) (B : ℕ → ℝ) (C A : ℝ)
    (hC : 1 ≤ C)
    (hl : ∀ m, K.positive m = true → K.left m = 0)
    (hr : ∀ m, K.positive m = true → K.right m = 1)
    (hregular : ∀ m, K.positive m = true →
      N06RadialPrimitiveRegularity w (H m) (Y m) (R m))
    (hB : ∀ m, K.positive m = true → 1 ≤ B m)
    (hjets : ∀ m, K.positive m = true → ∀ y ∈ Icc (0 : ℝ) 1,
      N06RadialPrimitiveJetBounds w (H m) (Y m) (R m) y (B m))
    (hE : ∀ m, K.positive m = true → 0 ≤ T.E0 (T.sample (K.cell m)))
    (hbound : ∀ m, K.positive m = true →
      B m ≤ C * T.E0 (T.sample (K.cell m)) ^ A) :
    N06PositiveUnitGeometry T K
      (fun m => n06RadialReferenceA w (H m) (Y m) (R m))
      (fun m => n06RadialReferenceC w (H m) (Y m) (R m))
      (fun m => n06RadialReferenceV w (H m) (Y m) (R m))
      (fun m => n06RadialReferenceQ w (Y m) (R m))
      (fun m => n06RadialReferenceConstant (B m))
      (n06RadialReferenceConstant C) := by
  have hs (m : ℕ) (hm : K.positive m = true) :=
    (hregular m hm).coefficients_smooth
  have hb (m : ℕ) (hm : K.positive m = true) (y : ℝ)
      (hy : y ∈ Icc (0 : ℝ) 1) :=
    n06_radialReference_modal_bounds (hregular m hm) (hB m hm) hy (hjets m hm y hy)
  refine
    { constant_one_le := n06_radialReferenceConstant_one_le hC
      left := hl
      right := hr
      a_smooth := fun m hm => (hs m hm).1
      c_continuous := fun m hm => (hs m hm).2.1.continuous
      potential_continuous := fun m hm => (hs m hm).2.2.1.continuous
      q_twice := fun m hm => (hs m hm).2.2.2.of_le (by simp)
      one_le := fun m hm => n06_radialReferenceConstant_one_le (hB m hm)
      a_lower := fun m hm y hy => (hb m hm y hy).1
      a_upper := fun m hm y hy => (hb m hm y hy).2.1
      a_derivative := fun m hm y hy => (hb m hm y hy).2.2.1
      c_lower := fun m hm y hy => (hb m hm y hy).2.2.2.1
      potential_bound := fun m hm y hy => (hb m hm y hy).2.2.2.2.1
      c_eq_aq := fun m hm y hy => (hb m hm y hy).2.2.2.2.2.1
      q_second := fun m hm y hy => (hb m hm y hy).2.2.2.2.2.2
      material_growth := ?_ }
  refine ⟨A * 25, ?_⟩
  intro m hm
  exact n06_radialReferenceConstant_material_bound
    (zero_le_one.trans (hB m hm)) (hE m hm) (hbound m hm)

end ContinuousFlexibility.Analysis
