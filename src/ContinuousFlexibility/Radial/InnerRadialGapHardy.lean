import ContinuousFlexibility.Radial.InnerGapHardyCoercivity
import ContinuousFlexibility.Radial.InnerGapHardyPoisson
import ContinuousFlexibility.Radial.InnerRadialActualPieces

/-!
# Uniform Hardy bounds for the same actual gap operators

The chart supplies the original positive-gap inverse and classical
columns. The auxiliary positive slope constructs these operators; the
bounds below use only monotonicity of the actual profile. The entire
gap conormal matrix, including its off-diagonal entries, is retained.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff InnerProductSpace

namespace InnerRadialGapChart

variable {D : ReferenceData} {n : ℕ} {G : InnerRadialChainGeometry D n}
  {j : ℝ} {central piece : Fin (n + 1)}
  (Q : InnerRadialGapChart D G j central piece)

theorem dirichlet_norm_le_hardy (hw : ContDiff ℝ ∞ D.w)
    (hjhalf : (1 / 2 : ℝ) ≤ j ^ 2) : ‖Q.dirichlet hw‖ ≤ 48 := by
  have hfield : ‖Q.fieldDirichlet hw‖ ≤ 48 :=
    innerGapDirichletInverse_norm_le_hardy D hw (G.left_lt_right piece).le
      (G.left_pos piece) Q.frequency_pos Q.slope_pos (G.in_core piece)
      (G.weight_pos piece) Q.slope_lower hjhalf
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro F
  have hsquare : ‖Q.dirichlet hw F‖ ^ 2 = ‖Q.fieldDirichlet hw F.fst‖ ^ 2 := by
    rw [Q.dirichlet_apply, innerBorderL2_norm_sq]
    simp
  have hnorm : ‖Q.dirichlet hw F‖ = ‖Q.fieldDirichlet hw F.fst‖ :=
    (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsquare
  rw [hnorm]
  exact ((Q.fieldDirichlet hw).le_opNorm F.fst).trans
    (mul_le_mul hfield (WithLp.norm_fst_le F) (norm_nonneg _) (by norm_num))

theorem poisson_norm_sq_hardy (hw : ContDiff ℝ ∞ D.w)
    (hjhalf : (1 / 2 : ℝ) ≤ j ^ 2) (z : EuclideanSpace ℝ (Fin 2)) :
    ‖Q.poisson hw.continuous z‖ ^ 2 ≤
      48 * ⟪z, Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) Q.fluxMatrix z⟫_ℝ +
        24 * (D.w (G.left piece) / G.left piece) * (z 0) ^ 2 := by
  have hwp := innerGap_deriv_nonneg_of_slope (G.left_pos piece) Q.slope_pos.le
    (G.weight_pos piece) Q.slope_lower
  have h := innerGapPoissonL2_norm_sq_hardy D hw (G.left_lt_right piece).le
    (G.left_pos piece) (G.in_core piece)
    (fun r hr => (G.weight_pos piece r hr).le) hwp hjhalf
    Q.columns Q.columns_smooth Q.columns_boundary Q.columns_homogeneous z
  rw [Q.poisson_apply, innerBorderL2_norm_sq]
  simpa only [fieldPoisson, fluxMatrix, innerGapFluxOperator,
    norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero] using h

end InnerRadialGapChart

end ContinuousFlexibility.Radial
