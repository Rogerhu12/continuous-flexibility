module

public import ContinuousFlexibility.Radial.MatchedInnerCoarseWeights

/-!
# The two signed multipliers of the original finite chain

These are transparent names for the original physical weight and its
original coefficient loss. The finite bounds are used only to define
the existing multiplication equivalences, not as quantitative inverse
estimates.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real MeasureTheory ContinuousFlexibility.Statements

variable {D : ReferenceData} (N K : ℕ)
  (G : InnerRadialChainGeometry D (2 * (2 * K + 1)))
  (l r : Fin (2 * (2 * K + 1) + 1) → ℝ)

def matchedMorseSignedWeight (sign : Bool) : ℝ → ℝ :=
  fun x => (innerMorseInnerWeight N K 0 1 G l r x) ^ (if sign then (1 : ℝ) else -1)

def matchedMorseLocalizedWeight (sign : Bool) : ℝ → ℝ :=
  fun x => innerMorseInnerLoss N K G 37 x * matchedMorseSignedWeight N K G l r sign x

theorem matchedMorseSignedWeight_measurable (sign : Bool) :
    Measurable (matchedMorseSignedWeight N K G l r sign) :=
  (innerMorseInnerWeight_measurable N K 0 1 G l r).pow_const _

theorem matchedMorseLocalizedWeight_measurable (sign : Bool) :
    Measurable (matchedMorseLocalizedWeight N K G l r sign) :=
  (innerMorseInnerLoss_measurable N K G 37).mul
    (matchedMorseSignedWeight_measurable N K G l r sign)

theorem matchedMorseSignedWeight_pos (sign : Bool) (x : ℝ) :
    0 < matchedMorseSignedWeight N K G l r sign x :=
  rpow_pos_of_pos (innerMorseInnerWeight_pos N K 0 1 G l r x) _

theorem matchedMorseLocalizedWeight_pos (sign : Bool) (x : ℝ) :
    0 < matchedMorseLocalizedWeight N K G l r sign x :=
  mul_pos (innerMorseInnerLoss_pos N K G 37 x)
    (matchedMorseSignedWeight_pos N K G l r sign x)

theorem matchedMorseSignedWeight_inv (sign : Bool) (x : ℝ) :
    (matchedMorseSignedWeight N K G l r sign x)⁻¹ =
      matchedMorseSignedWeight N K G l r (!sign) x := by
  cases sign <;> simp only [matchedMorseSignedWeight, Bool.false_eq_true, ite_false,
    ite_true, Bool.not_false, Bool.not_true, rpow_one, rpow_neg_one, inv_inv]

theorem matchedMorseLocalizedWeight_bound {B : ℝ}
    (hB : ∀ sign x, |matchedMorseSignedWeight N K G l r sign x| ≤ B)
    (sign : Bool) (x : ℝ) :
    |matchedMorseLocalizedWeight N K G l r sign x| ≤ B :=
  innerWeight_mul_bound_one (innerMorseInnerLoss N K G 37)
    (matchedMorseSignedWeight N K G l r sign)
    (innerMorseInnerLoss_le_one N K G (by norm_num)) B (hB sign) x

def matchedMorseLossInverseBound : ℝ :=
  exp (37 * (radialQ (N + K) - radialQ N))

theorem matchedMorseLossInverseBound_ge_one : 1 ≤ matchedMorseLossInverseBound N K := by
  apply one_le_exp_iff.mpr
  exact mul_nonneg (by norm_num)
    (sub_nonneg.mpr (radialQ_monotone (Nat.le_add_right N K)))

theorem matchedMorseLocalizedWeight_inv_bound {B : ℝ}
    (hB : ∀ sign x, |matchedMorseSignedWeight N K G l r sign x| ≤ B)
    (sign : Bool) (x : ℝ) :
    |(matchedMorseLocalizedWeight N K G l r sign x)⁻¹| ≤
      matchedMorseLossInverseBound N K * B := by
  have hB₀ : 0 ≤ B := (abs_nonneg _).trans (hB true 0)
  have hw : |(matchedMorseSignedWeight N K G l r sign x)⁻¹| ≤ B := by
    rw [matchedMorseSignedWeight_inv]
    exact hB (!sign) x
  have hl : |(innerMorseInnerLoss N K G 37 x)⁻¹| ≤ matchedMorseLossInverseBound N K :=
    matchedInner_loss_inverse_bound N K G (by norm_num) x
  rw [matchedMorseLocalizedWeight, mul_inv_rev, abs_mul]
  exact (mul_le_mul hw hl (abs_nonneg _) hB₀).trans_eq (mul_comm _ _)

end ContinuousFlexibility.Radial
