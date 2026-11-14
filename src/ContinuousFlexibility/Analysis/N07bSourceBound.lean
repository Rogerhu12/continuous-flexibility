module

public import ContinuousFlexibility.Analysis.N07bSourceBoundSummation
public import ContinuousFlexibility.Analysis.SolveStateSpaces
public import ContinuousFlexibility.Scalar.WeightedPointwise

/-!
# Geometric source coefficient conditions

This module names the coefficient growth condition and identifies its
multiplier with the actual Jacobian and height-ratio weight. The source
lift used by the final proof is constructed directly from primitive jet
bounds in `N07bSourceBoundPrimitiveLift`.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff BigOperators ENNReal

set_option backward.isDefEq.respectTransparency true

/-- The exact geometric condition used by the analytic source estimate.
The constants are chosen before the state, piece, path, and source. This
condition is not a field of the frozen canonical geometry statement. -/
def N07bSourceCoefficientBound (T : MaterialData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (K : CanonicalData S)
    (base : ℕ) (ε : ℝ) (b loss : ℕ) : Prop :=
  ∃ B A : ℝ, 0 ≤ B ∧ 0 ≤ A ∧
    ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      ∀ m x, x ∈ physicalPieceOpen S K z m →
        ∀ j : Fin (b + 1), ∀ i : n07bAngularChainIndex j.val,
          n07bSourceGeometricWeight T K z m x *
            n07bAngularChainCoefficient T K z m (3 / 4 : ℝ) j.val i x ^ 2 ≤
              B * T.E0 x.1 ^ A *
                (1 + stateGrading S (b + loss) (z.1 - C.referenceState) + |z.2|) ^ 2

/-- For positive actual heights, the coefficient multiplier is precisely
the physical Jacobian weight with height ratio exponent `3/2`. -/
theorem n07bSourceGeometricWeight_eq
    {S : PhysicalSpacesData} (T : MaterialData) (K : CanonicalData S)
    (z : AnnularState S × ℝ) (m : ℕ) (x : PolarPoint)
    (hx : 0 < T.H x.1) (hm : 0 < T.H (T.sample (K.cell m))) :
    n07bSourceGeometricWeight T K z m x =
      T.ell x.1 * |planeJacobian (K.chart z m) x| *
        (T.H x.1 / T.H (T.sample (K.cell m))) ^ (3 / 2 : ℝ) := by
  have hfactor : n07bCanonicalSourceFactor T K (3 / 4 : ℝ) 0 m =
      T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ) := by
    simp only [n07bCanonicalSourceFactor, neg_zero, Real.rpow_zero, one_mul]
  have hp : (T.H x.1 ^ (3 / 4 : ℝ) / T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ)) ^ 2 =
      (T.H x.1 / T.H (T.sample (K.cell m))) ^ (3 / 2 : ℝ) := by
    rw [← Real.div_rpow hx.le hm.le, ← Real.rpow_natCast,
      ← Real.rpow_mul (div_nonneg hx.le hm.le)]
    norm_num
  calc
    _ = T.ell x.1 * |planeJacobian (K.chart z m) x| *
        (T.H x.1 ^ (3 / 4 : ℝ) / T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ)) ^ 2 := by
      change T.ell x.1 * ((n07bCanonicalSourceFactor T K (3 / 4 : ℝ) 0 m)⁻¹ ^ 2 *
        |planeJacobian (K.chart z m) x| * (T.H x.1 ^ (3 / 4 : ℝ)) ^ 2) = _
      rw [hfactor]
      simp only [div_eq_mul_inv, mul_pow]
      ring
    _ = _ := by rw [hp]

end ContinuousFlexibility.Analysis
