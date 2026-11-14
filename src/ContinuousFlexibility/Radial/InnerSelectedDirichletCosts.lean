module

public import ContinuousFlexibility.Radial.InnerSelectedMorseEstimates
public import ContinuousFlexibility.Radial.InnerRadialDirichletWeights
public import ContinuousFlexibility.Radial.InnerMorseInnerWeightCosts

/-!
# Uniform local Dirichlet costs on the selected physical chain

The same central and Morse models used by the Poisson and conormal
estimates have their actual Hilbert Dirichlet bounds. Positive gaps
use the already constructed radial inverse. One constant, chosen from
the fixed geometry and the two original model constants, controls
every piece in every finite band with the fixed power thirty-six.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set ContinuousFlexibility.Statements
open scoped ContDiff

namespace InnerSelectedPhysicalGeometry

variable {S : SelectedTailData} {D : ReferenceData} {X₀ : ℝ}
  (P : InnerSelectedPhysicalGeometry S D X₀)

/-- Independent of the finite truncation, frequency and weight. -/
def dirichletConstant (CC CM : ℝ) : ℝ :=
  max (innerCentralDirichletConstant X₀ CC)
    (max (innerMorseDirichletConstant CM) (12 / P.gapSlope))

theorem dirichletConstant_pos (CC CM : ℝ) : 0 < P.dirichletConstant CC CM :=
  (div_pos (by norm_num : (0 : ℝ) < 12) P.gapSlope_pos).trans_le
    ((le_max_right _ _).trans (le_max_right _ _))

theorem dirichletConstant_nonneg (CC CM : ℝ) : 0 ≤ P.dirichletConstant CC CM :=
  (P.dirichletConstant_pos CC CM).le

theorem centralDirichletConstant_le (CC CM : ℝ) :
    innerCentralDirichletConstant X₀ CC ≤ P.dirichletConstant CC CM :=
  le_max_left _ _

theorem morseDirichletConstant_le (CC CM : ℝ) :
    innerMorseDirichletConstant CM ≤ P.dirichletConstant CC CM :=
  (le_max_left _ _).trans (le_max_right _ _)

theorem gapDirichletConstant_le (CC CM : ℝ) :
    12 / P.gapSlope ≤ P.dirichletConstant CC CM :=
  (le_max_right _ _).trans (le_max_right _ _)

private theorem one_le_coefficient_power (m : ℕ) :
    1 ≤ radialE m ^ (36 : ℝ) := by
  rw [radialE, ← exp_mul, one_le_exp_iff]
  exact mul_nonneg (radialQ_nonneg m) (by norm_num)

theorem dirichletConstant_le_coefficient_cost (CC CM : ℝ) (m : ℕ) :
    P.dirichletConstant CC CM ≤ P.dirichletConstant CC CM * radialE m ^ (36 : ℝ) := by
  calc
    P.dirichletConstant CC CM = P.dirichletConstant CC CM * 1 := (mul_one _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (one_le_coefficient_power m)
      (P.dirichletConstant_nonneg CC CM)

/-- The scalar-zero gap inverse has the same bound for every band and
even frequency. The gap slope was fixed from the raw physical geometry. -/
theorem gapChart_dirichlet_norm_le (K q : ℕ) (hq : 1 ≤ q)
    (hj : 0 < (2 : ℝ) * q) (g : Fin (2 * K + 2)) :
    ‖(P.gapChart K ((2 : ℝ) * q) hj g).dirichlet P.geometry.2.2.1.1‖ ≤
      12 / P.gapSlope := by
  have hqone : 1 ≤ (2 : ℝ) * q := by
    exact_mod_cast (show 1 ≤ 2 * q by omega)
  have hsq : 1 ≤ ((2 : ℝ) * q) ^ 2 := by nlinarith
  have hden : P.gapSlope ≤ P.gapSlope * ((2 : ℝ) * q) ^ 2 := by
    calc
      P.gapSlope = P.gapSlope * 1 := (mul_one _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hsq P.gapSlope_pos.le
  exact ((P.gapChart K ((2 : ℝ) * q) hj g).dirichlet_norm_le_uniform
    P.geometry.2.2.1.1 P.gapSlope_pos (by exact le_rfl)).trans
      (div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 12) P.gapSlope_pos hden)

section ActualChain

variable {a CC KC CM KM η : ℝ}
  (hCentralFamily : InnerCentralPhysicalFamily CC KC X₀ η)
  (hMorseFamily : InnerMorsePhysicalFamily a S.Cstar S.chain.index CM KM η)
  (hX : 8 ≤ X₀) (hsupport : innerCentralModelBorderRadius < X₀)
  (K q : ℕ) (hq : 1 ≤ q)
  (hband : radialFrequencyBand S.chain S.Cstar (S.chain.index + K) (2 * q))

/-- Every actual Dirichlet block has the cost of its own cell. The
model and gap cases are derived from their original constructors. -/
theorem actualChain_piece_dirichlet_bound (hCC : 0 ≤ CC) (hCM : 0 ≤ CM)
    (p : Fin (2 * (2 * K + 1) + 1)) :
    ‖((P.actualChain hCentralFamily hMorseFamily hX hsupport K q hq hband).piece p).dirichlet
      P.geometry.2.2.1.1‖ ≤
      P.dirichletConstant CC CM *
        radialE (innerMorseInnerPieceIndex S.chain.index K p) ^ (36 : ℝ) := by
  rcases innerModelChainPiece_or_gap p with ⟨m, rfl⟩ | ⟨g, rfl⟩
  · rw [P.actualChain_model, InnerRadialActualPiece.dirichlet,
      innerMorseInnerPieceIndex_model]
    rcases innerMorseInnerModel_cases K m with rfl | ⟨side, p, rfl⟩
    · rw [P.models_center, innerMorseInnerModelIndex_center]
      exact (P.centralModel_dirichlet_norm_le hCentralFamily hX hsupport (P.chain K)
        (innerModelChainPiece (innerMorseInnerCenter K)) q hq
        (P.center_left_cut K) (P.center_right_cut K) hCC).trans
          ((P.centralDirichletConstant_le CC CM).trans
            (P.dirichletConstant_le_coefficient_cost CC CM S.chain.index))
    · rw [P.models_tail, innerMorseInnerModelIndex_tail]
      exact (P.tailModel_dirichlet_norm_le hMorseFamily hsupport K q hq hband side p hCM).trans
        (mul_le_mul_of_nonneg_right (P.morseDirichletConstant_le CC CM)
          (rpow_nonneg (exp_pos _).le _))
  · rw [P.actualChain_gap, InnerRadialActualPiece.dirichlet,
      innerMorseInnerPieceIndex_gap]
    have hj : 0 < (2 : ℝ) * q := by
      exact_mod_cast (show 0 < 2 * q by omega)
    exact (P.gapChart_dirichlet_norm_le K q hq hj g).trans
      ((P.gapDirichletConstant_le CC CM).trans
        (P.dirichletConstant_le_coefficient_cost CC CM
          (innerMorseInnerGapIndex S.chain.index K g)))

end ActualChain

end InnerSelectedPhysicalGeometry

end ContinuousFlexibility.Radial
