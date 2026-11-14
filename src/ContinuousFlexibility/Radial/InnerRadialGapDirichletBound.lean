module

public import ContinuousFlexibility.Radial.InnerRadialActualPieces

/-!
# The actual gap Hilbert Dirichlet bound

The gap operator has zero scalar output and uses only the field input.
Those two inclusions are contractions. Its norm therefore inherits the
exact physical coercive bound of the same gap inverse, without a spare
identity on the scalar coordinate.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open ContinuousFlexibility.Statements
open scoped ContDiff

namespace InnerRadialGapChart

variable {D : ReferenceData} {n : ℕ} {G : InnerRadialChainGeometry D n}
  {j : ℝ} {central piece : Fin (n + 1)} (A : InnerRadialGapChart D G j central piece)

theorem dirichlet_norm_le_field (hw : ContDiff ℝ ∞ D.w) :
    ‖A.dirichlet hw‖ ≤ ‖A.fieldDirichlet hw‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro F
  rw [A.dirichlet_apply, WithLp.norm_toLp_fst]
  exact ((A.fieldDirichlet hw).le_opNorm F.fst).trans
    (mul_le_mul_of_nonneg_left (WithLp.norm_fst_le (RadialModeL2 D) F) (norm_nonneg _))

theorem dirichlet_norm_le (hw : ContDiff ℝ ∞ D.w) :
    ‖A.dirichlet hw‖ ≤ 12 / (A.slope * j ^ 2) :=
  (A.dirichlet_norm_le_field hw).trans
    (innerGapDirichletInverse_norm_le D hw (G.left_lt_right piece).le (G.left_pos piece)
      A.frequency_pos A.slope_pos (G.in_core piece) (G.weight_pos piece) A.slope_lower)

theorem dirichlet_norm_le_uniform (hw : ContDiff ℝ ∞ D.w)
    {s : ℝ} (hs : 0 < s) (hslope : s ≤ A.slope) :
    ‖A.dirichlet hw‖ ≤ 12 / (s * j ^ 2) :=
  (A.dirichlet_norm_le hw).trans
    (div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 12)
      (mul_pos hs (sq_pos_of_pos A.frequency_pos))
      (mul_le_mul_of_nonneg_right hslope (sq_nonneg j)))

end InnerRadialGapChart

end ContinuousFlexibility.Radial
