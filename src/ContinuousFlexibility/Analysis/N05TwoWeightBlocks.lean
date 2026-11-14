module

public import ContinuousFlexibility.Radial.WeightKernelBounds

/-!
# Selecting the two endpoint bounds for one reference block

The hypotheses have the physical source and output weights of
`ReferenceInverseProperties`.  Conjugating at the middle exponent and
using the upper exponent on one side of the diagonal, and the lower
exponent on the other, produces the decaying block required by the
existing Schur estimates.  These are numerical implications: the
localization and canonical change-of-variables estimates remain separate
proof obligations.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

/-- Rewrite a physical block estimate after conjugation at a chosen endpoint
exponent. The factors involving `M0` and `M1` retain their original signs. -/
theorem n05_endpointBlock_conjugate
    (Sk Sm Qk Qm β γ M0 M1 C x y : ℝ)
    (h : Real.exp (-M1 * Qk + γ * Sk) * y ≤
      C * Real.exp (M0 * Qm + γ * Sm) * x) :
    Real.exp (β * (Sk - Sm)) * y ≤
      C * Real.exp (M1 * Qk + M0 * Qm + (β - γ) * (Sk - Sm)) * x := by
  let A : ℝ := M1 * Qk + (β - γ) * Sk - β * Sm
  have hleft : A + (-M1 * Qk + γ * Sk) = β * (Sk - Sm) := by
    dsimp only [A]
    ring
  have hright : A + (M0 * Qm + γ * Sm) =
      M1 * Qk + M0 * Qm + (β - γ) * (Sk - Sm) := by
    dsimp only [A]
    ring
  calc
    Real.exp (β * (Sk - Sm)) * y =
        Real.exp A * (Real.exp (-M1 * Qk + γ * Sk) * y) := by
      rw [← mul_assoc, ← Real.exp_add, hleft]
    _ ≤ Real.exp A * (C * Real.exp (M0 * Qm + γ * Sm) * x) :=
      mul_le_mul_of_nonneg_left h (Real.exp_pos A).le
    _ = C * (Real.exp A * Real.exp (M0 * Qm + γ * Sm)) * x := by ring
    _ = C * Real.exp (M1 * Qk + M0 * Qm + (β - γ) * (Sk - Sm)) * x := by
      rw [← Real.exp_add, hright]

/-- The two bounds for the same block give exponential decay after
conjugation at their midpoint. The source magnitude `x` is nonnegative;
no choice of a different inverse is made on either side of the diagonal. -/
theorem n05_twoEndpoint_block_bound
    (Sk Sm Qk Qm β ε M0 M1 Cminus Cplus x y : ℝ) (hx : 0 ≤ x)
    (hminus : Real.exp (-M1 * Qk + (β - ε) * Sk) * y ≤
      Cminus * Real.exp (M0 * Qm + (β - ε) * Sm) * x)
    (hplus : Real.exp (-M1 * Qk + (β + ε) * Sk) * y ≤
      Cplus * Real.exp (M0 * Qm + (β + ε) * Sm) * x) :
    Real.exp (β * (Sk - Sm)) * y ≤
      max Cminus Cplus * Real.exp (M1 * Qk + M0 * Qm - ε * |Sk - Sm|) * x := by
  by_cases hd : 0 ≤ Sk - Sm
  · have h := n05_endpointBlock_conjugate
      Sk Sm Qk Qm β (β + ε) M0 M1 Cplus x y hplus
    have he : M1 * Qk + M0 * Qm + (β - (β + ε)) * (Sk - Sm) =
        M1 * Qk + M0 * Qm - ε * |Sk - Sm| := by
      rw [abs_of_nonneg hd]
      ring
    rw [he] at h
    exact h.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right Cminus Cplus)
        (Real.exp_pos _).le) hx)
  · have h := n05_endpointBlock_conjugate
      Sk Sm Qk Qm β (β - ε) M0 M1 Cminus x y hminus
    have he : M1 * Qk + M0 * Qm + (β - (β - ε)) * (Sk - Sm) =
        M1 * Qk + M0 * Qm - ε * |Sk - Sm| := by
      rw [abs_of_nonpos (not_le.mp hd).le]
      ring
    rw [he] at h
    exact h.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left Cminus Cplus)
        (Real.exp_pos _).le) hx)

end ContinuousFlexibility.Analysis
