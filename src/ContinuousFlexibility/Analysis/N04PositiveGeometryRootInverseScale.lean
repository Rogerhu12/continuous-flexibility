import ContinuousFlexibility.Analysis.N04PositiveGeometryActualRootInverseDifferential

/-!
# The scalar inverse radial scale

The zeroth power trace is an ordinary scalar power. Its normalization
identity is kept separate from all moving differential towers.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements
open scoped BigOperators

theorem n04PositiveGeometry_rootPowerTrace_zero (γ : ℝ) (v : ℕ → ℝ) :
    n04PositiveGeometry_rootPowerTrace γ 0 v = v 0 ^ γ := by
  classical
  rw [n04PositiveGeometry_rootPowerTrace, Fintype.sum_unique]
  have hc : (default : OrderedFinpartition 0).length = 0 :=
    Nat.eq_zero_of_le_zero (default : OrderedFinpartition 0).length_le
  have hp : (∏ i : Fin (default : OrderedFinpartition 0).length,
      v ((default : OrderedFinpartition 0).partSize i)) = 1 := by
    apply Finset.prod_eq_one
    intro i _
    have hi : i.val < (default : OrderedFinpartition 0).length := i.isLt
    rw [hc] at hi
    exact False.elim (Nat.not_lt_zero i.val hi)
  rw [hp, hc]
  simp only [rpowJetCoefficient, Nat.cast_zero, sub_zero, one_mul, mul_one]

theorem n04PositiveGeometry_rootBoundaryScale_inv_eq
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (g : ℝ → ℝ) (m : ℕ) (side : Bool) (y : (StateDirections S × ℝ) × ℝ)
    (hy : 0 ≤ n04PositiveGeometry_rootOddTrace D S C g m side 0 y) :
    (n04PositiveGeometry_rootBoundaryScale D S C g m side y)⁻¹ =
      (3 / 2 : ℝ) ^ (-(2 / 3 : ℝ)) *
        n04PositiveGeometry_rootOddPowerTrace D S C g m side (-(2 / 3 : ℝ)) 0 y := by
  rw [n04PositiveGeometry_rootOddPowerTrace, n04PositiveGeometry_rootPowerTrace_zero]
  unfold n04PositiveGeometry_rootBoundaryScale
  rw [← Real.rpow_neg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 2) hy),
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3 / 2) hy]

end ContinuousFlexibility.Analysis
