module

public import ContinuousFlexibility.Analysis.IntervalSobolevCutoffCore
public import ContinuousFlexibility.Analysis.SobolevJetCompletion

/-!
# The cutoff bound in the complete derivative Sobolev norm

Every lower derivative in Leibniz's rule is a coordinate of the source jet.
Coordinate contraction in `PiLp 2` therefore turns the finite Leibniz estimate
into a bound in the usual sum-of-squares Sobolev norm.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open scoped ContDiff ENNReal

variable {χ : ℝ → ℝ}

/-- The sum of the coefficients in the order-`n` Leibniz bound. -/
def cutoffJetBound
    (hbounded : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖iteratedDeriv n χ x‖ ≤ C)
    (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * cutoffDerivativeBound hbounded i

theorem cutoffJetBound_nonneg
    (hbounded : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖iteratedDeriv n χ x‖ ≤ C)
    (n : ℕ) : 0 ≤ cutoffJetBound hbounded n :=
  Finset.sum_nonneg fun i _ =>
    mul_nonneg (Nat.cast_nonneg _) (cutoffDerivativeBound_nonneg hbounded i)

/-- One finite bound for the full derivative Sobolev norm of order `k`. -/
def cutoffSobolevBound
    (hbounded : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖iteratedDeriv n χ x‖ ≤ C)
    (k : ℕ) : ℝ := ∑ j : Fin (k + 1), cutoffJetBound hbounded j.val

theorem cutoffSobolevBound_nonneg
    (hbounded : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖iteratedDeriv n χ x‖ ≤ C)
    (k : ℕ) : 0 ≤ cutoffSobolevBound hbounded k :=
  Finset.sum_nonneg fun j _ => cutoffJetBound_nonneg hbounded j.val

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem cutoffHalfLineCoreLinear_derivative_bound {L c : ℝ} (hL : 0 < L) (hc : c < L)
    (hχ : ContDiff ℝ ∞ χ) (hzero : ∀ y, c ≤ y → χ y = 0)
    (hbounded : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖iteratedDeriv n χ x‖ ≤ C)
    {n k : ℕ} (hnk : n ≤ k) (f : IntervalSobolevCore F L hL) :
    ‖sobolevCoreDerivative F (Ici 0) measurableSet_Ici (uniqueDiffOn_Ici 0) n
        (cutoffHalfLineCoreLinear hL hc hχ hzero hbounded f)‖ ≤
      cutoffJetBound hbounded n *
        ‖sobolevCoreJet F (Icc 0 L) measurableSet_Icc (uniqueDiffOn_Icc hL) k f‖ := by
  rw [norm_sobolevCoreDerivative]
  refine (cutoffHalfLineCoreLinear_jet_norm_le hL hc hχ hzero hbounded f n).trans ?_
  rw [cutoffJetBound, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  have hindex : n - i < k + 1 := Nat.lt_succ_of_le ((Nat.sub_le n i).trans hnk)
  have hcoord :
      (eLpNorm (iteratedDerivWithin (n - i) f (Icc 0 L)) 2
        (volume.restrict (Icc 0 L))).toReal ≤
      ‖sobolevCoreJet F (Icc 0 L) measurableSet_Icc (uniqueDiffOn_Icc hL) k f‖ := by
    simpa only [sobolevCoreJet_apply, norm_sobolevCoreDerivative] using
      PiLp.norm_apply_le
        (sobolevCoreJet F (Icc 0 L) measurableSet_Icc (uniqueDiffOn_Icc hL) k f)
        (⟨n - i, hindex⟩ : Fin (k + 1))
  exact mul_le_mul_of_nonneg_left hcoord
    (mul_nonneg (Nat.cast_nonneg _) (cutoffDerivativeBound_nonneg hbounded i))

/-- The same linear cutoff map is bounded in every integer Sobolev norm. -/
theorem cutoffHalfLineCoreLinear_bound {L c : ℝ} (hL : 0 < L) (hc : c < L)
    (hχ : ContDiff ℝ ∞ χ) (hzero : ∀ y, c ≤ y → χ y = 0)
    (hbounded : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖iteratedDeriv n χ x‖ ≤ C)
    (k : ℕ) (f : IntervalSobolevCore F L hL) :
    ‖sobolevCoreJet F (Ici 0) measurableSet_Ici (uniqueDiffOn_Ici 0) k
        (cutoffHalfLineCoreLinear hL hc hχ hzero hbounded f)‖ ≤
      cutoffSobolevBound hbounded k *
        ‖sobolevCoreJet F (Icc 0 L) measurableSet_Icc (uniqueDiffOn_Icc hL) k f‖ :=
  sobolevCoreJet_norm_le_of_coordinate_bounds F
    (cutoffHalfLineCoreLinear hL hc hχ hzero hbounded) k
    (fun j => cutoffJetBound hbounded j.val)
    (fun j => cutoffJetBound_nonneg hbounded j.val)
    (fun j g => cutoffHalfLineCoreLinear_derivative_bound hL hc hχ hzero hbounded
      (Nat.le_of_lt_succ j.isLt) g) f

end ContinuousFlexibility.Analysis
