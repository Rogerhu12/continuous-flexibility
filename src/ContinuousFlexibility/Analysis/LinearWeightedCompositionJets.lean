module

public import ContinuousFlexibility.Analysis.FlowJetLinearization
public import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Jets of a coefficient composed with a linear map and a linear weight

The fixed linear maps do not cost an input derivative. All derivatives
of the coefficient through the output order enter only linearly. This is
the quantitative operation used by the regularized root vector field.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open scoped BigOperators ContDiff

def linearWeightedCompositionJetConstant (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ((n - i).factorial : ℝ)

theorem one_le_linearWeightedCompositionJetConstant (n : ℕ) :
    1 ≤ linearWeightedCompositionJetConstant n := by
  have h := Finset.single_le_sum
    (f := fun i => (n.choose i : ℝ) * ((n - i).factorial : ℝ))
    (fun i _ => mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    (Finset.mem_range.mpr (Nat.lt_succ_self n))
  simpa only [Nat.choose_self, Nat.sub_self, Nat.factorial_zero,
    Nat.cast_one, one_mul, linearWeightedCompositionJetConstant] using h

/-- Actual jets of a linear-weighted pullback are bounded by a single
input bound through the same order, including order zero. -/
theorem norm_iteratedFDeriv_linearWeightedComposition_le
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {f : Y → ℝ} (hf : ContDiff ℝ ∞ f)
    (A : X →L[ℝ] Y) (l : X →L[ℝ] ℝ) (x : X)
    {L M : ℝ} (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hA : ‖A‖ ≤ 1) (hl : ‖l‖ ≤ L) (hlx : ‖l x‖ ≤ L)
    (n : ℕ) (hbound : ∀ k : ℕ, k ≤ n →
      ‖iteratedFDeriv ℝ k f (A x)‖ ≤ M) :
    ‖iteratedFDeriv ℝ n (fun y => l y * f (A y)) x‖ ≤
      linearWeightedCompositionJetConstant n * L * M := by
  have hlin (i : ℕ) : ‖iteratedFDeriv ℝ i (l : X → ℝ) x‖ ≤ L := by
    cases i with
    | zero => simpa only [norm_iteratedFDeriv_zero] using hlx
    | succ i =>
        exact (flowJet_norm_iteratedFDeriv_clm_le l (Nat.succ_pos i) x).trans hl
  have hcomp (j : ℕ) (hj : j ≤ n) :
      ‖iteratedFDeriv ℝ j (f ∘ A) x‖ ≤ (j.factorial : ℝ) * M := by
    have h := norm_iteratedFDeriv_comp_le hf A.contDiff (by simp) x
      (C := M) (D := (1 : ℝ)) (fun k hk => hbound k (hk.trans hj))
      (fun i hi _ => by
        simpa only [one_pow] using
          (flowJet_norm_iteratedFDeriv_clm_le A hi x).trans hA)
    simpa only [one_pow, mul_one] using h
  calc
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i (l : X → ℝ) x‖ *
          ‖iteratedFDeriv ℝ (n - i) (f ∘ A) x‖ :=
      norm_iteratedFDeriv_mul_le l.contDiff (hf.comp A.contDiff) x (by simp)
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * L *
        (((n - i).factorial : ℝ) * M) := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (hlin i) (Nat.cast_nonneg _))
        (hcomp (n - i) (Nat.sub_le _ _)) (norm_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) hL)
    _ = linearWeightedCompositionJetConstant n * L * M := by
      rw [linearWeightedCompositionJetConstant, Finset.sum_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring

end ContinuousFlexibility.Analysis
