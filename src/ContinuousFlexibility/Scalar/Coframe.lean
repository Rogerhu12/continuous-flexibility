module

public import ContinuousFlexibility.Scalar.Positivity
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.FieldSimp

/-!
# Pointwise coframe identity

Section 3, immediately after `height-jet-notation`. This proves the equality
of the quadratic expressions. The Cartan structure equations and the
identification with a geometric connection remain separate obligations.
-/

@[expose] public section

namespace ContinuousFlexibility

/-- The first one-form of the manuscript evaluated on `(x,y)`. -/
noncomputable def coframeOne (E k p x : ℝ) : ℝ :=
  Real.sqrt (heightDiscriminant E k p) / Real.sqrt (1 - p ^ 2) * x

/-- The second one-form of the manuscript evaluated on `(x,y)`. -/
noncomputable def coframeTwo (r k p x y : ℝ) : ℝ :=
  r * Real.sqrt (1 - p ^ 2) * y - k * p / Real.sqrt (1 - p ^ 2) * x

/-- The displayed coframe reproduces the actual remainder quadratic form. -/
theorem coframe_square_sum {r E k p : ℝ} (hE : 0 < E)
    (hD : 0 < heightDiscriminant E k p) (x y : ℝ) :
    coframeOne E k p x ^ 2 + coframeTwo r k p x y ^ 2 =
      remainderQuadratic r E k p x y := by
  have hp := angular_factor_pos_of_discriminant_pos hE hD
  have hs : Real.sqrt (1 - p ^ 2) ≠ 0 := (Real.sqrt_pos.2 hp).ne'
  have hs2 := Real.sq_sqrt hp.le
  have hd2 := Real.sq_sqrt hD.le
  dsimp [coframeOne, coframeTwo]
  calc
    _ = (Real.sqrt (heightDiscriminant E k p) ^ 2 * x ^ 2 +
          (r * Real.sqrt (1 - p ^ 2) ^ 2 * y - k * p * x) ^ 2) /
            Real.sqrt (1 - p ^ 2) ^ 2 := by
      field_simp [hs]
    _ = (heightDiscriminant E k p * x ^ 2 +
          (r * (1 - p ^ 2) * y - k * p * x) ^ 2) / (1 - p ^ 2) := by
      rw [hd2, hs2]
    _ = remainderQuadratic r E k p x y := by
      rw [← remainder_complete_square]
      exact mul_div_cancel_left₀ _ hp.ne'

end ContinuousFlexibility
