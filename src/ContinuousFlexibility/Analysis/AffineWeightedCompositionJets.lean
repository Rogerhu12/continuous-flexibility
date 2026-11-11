import ContinuousFlexibility.Analysis.LinearWeightedCompositionJets

/-!
# Actual jets of an affine weighted pullback

The argument and prefactor are fixed affine maps. Their constants enter
only the numerical sequence: every derivative of the original scalar
field through the requested order still occurs linearly. This supplies
the field of a scalar flow whose endpoint radius is an external parameter.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open scoped BigOperators ContDiff

set_option backward.isDefEq.respectTransparency false

/-- Translation of the output does not alter a positive derivative of
an affine map. The estimate includes first order and every higher order. -/
theorem flowJet_norm_iteratedFDeriv_affine_le
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (A : X →L[ℝ] Y) (a : Y) {n : ℕ} (hn : 1 ≤ n) (x : X) :
    ‖iteratedFDeriv ℝ n (fun y => a + A y) x‖ ≤ ‖A‖ := by
  cases n with
  | zero => omega
  | succ n =>
      have he : (fun y : X => a + A y) = (fun _ : X => a) + (A : X → Y) := by
        funext y
        exact (Pi.add_apply (fun _ : X => a) (A : X → Y) y).symm
      rw [he, iteratedFDeriv_add_apply contDiffAt_const A.contDiff.contDiffAt,
        iteratedFDeriv_succ_const, Pi.zero_apply, zero_add]
      exact flowJet_norm_iteratedFDeriv_clm_le A (Nat.succ_pos n) x

def affineWeightedCompositionJetConstant (K : ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1),
    (n.choose i : ℝ) * ((n - i).factorial : ℝ) * K ^ (n - i)

theorem one_le_affineWeightedCompositionJetConstant
    {K : ℝ} (hK : 0 ≤ K) (n : ℕ) :
    1 ≤ affineWeightedCompositionJetConstant K n := by
  have hh := Finset.single_le_sum
    (f := fun i => (n.choose i : ℝ) * ((n - i).factorial : ℝ) * K ^ (n - i))
    (fun i _ => mul_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (pow_nonneg hK _))
    (Finset.mem_range.mpr (Nat.lt_succ_self n))
  simpa only [Nat.choose_self, Nat.sub_self, Nat.factorial_zero,
    Nat.cast_one, pow_zero, one_mul, affineWeightedCompositionJetConstant] using hh

theorem norm_iteratedFDeriv_affineWeightedComposition_le
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {f : Y → ℝ} (hf : ContDiff ℝ ∞ f)
    (A : X →L[ℝ] Y) (a : Y) (l : X →L[ℝ] ℝ) (c : ℝ) (x : X)
    {K L M : ℝ} (hK : 1 ≤ K) (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hA : ‖A‖ ≤ K) (hl : ‖l‖ ≤ L) (hlx : ‖c + l x‖ ≤ L)
    (n : ℕ) (hbound : ∀ k : ℕ, k ≤ n →
      ‖iteratedFDeriv ℝ k f (a + A x)‖ ≤ M) :
    ‖iteratedFDeriv ℝ n (fun y => (c + l y) * f (a + A y)) x‖ ≤
      affineWeightedCompositionJetConstant K n * L * M := by
  have hlin (i : ℕ) : ‖iteratedFDeriv ℝ i (fun y => c + l y) x‖ ≤ L := by
    cases i with
    | zero => simpa only [norm_iteratedFDeriv_zero] using hlx
    | succ i =>
        exact (flowJet_norm_iteratedFDeriv_affine_le l c (Nat.succ_pos i) x).trans hl
  have hmap : ContDiff ℝ ∞ (fun y => a + A y) := contDiff_const.add A.contDiff
  have hcomp (j : ℕ) (hj : j ≤ n) :
      ‖iteratedFDeriv ℝ j (f ∘ (fun y => a + A y)) x‖ ≤
        (j.factorial : ℝ) * M * K ^ j := by
    exact norm_iteratedFDeriv_comp_le hf hmap (by simp) x
      (C := M) (D := K) (fun k hk => hbound k (hk.trans hj))
      (fun i hi _ => (flowJet_norm_iteratedFDeriv_affine_le A a hi x).trans
        (hA.trans (by simpa only [pow_one] using pow_le_pow_right₀ hK hi)))
  calc
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i (fun y => c + l y) x‖ *
          ‖iteratedFDeriv ℝ (n - i) (f ∘ (fun y => a + A y)) x‖ :=
      norm_iteratedFDeriv_mul_le (contDiff_const.add l.contDiff) (hf.comp hmap) x (by simp)
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * L *
        (((n - i).factorial : ℝ) * M * K ^ (n - i)) := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (hlin i) (Nat.cast_nonneg _))
        (hcomp (n - i) (Nat.sub_le _ _)) (norm_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) hL)
    _ = affineWeightedCompositionJetConstant K n * L * M := by
      rw [affineWeightedCompositionJetConstant, Finset.sum_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring

end ContinuousFlexibility.Analysis
