import ContinuousFlexibility.Analysis.ScalarInverseJetBounds

/-!
# Algebra of uniform positive-order scalar jets

Composition of circle lifts only uses their positive-order jets.
Their values can be unbounded. These estimates separate that distinction
from the ordinary product estimate, which also controls order zero.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Analysis

open Set
open scoped ContDiff BigOperators

theorem iteratedDeriv_mul_uniform_bound
    {ι : Type*} (f g : ι → ℝ → ℝ)
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) (hg : ∀ i, ContDiff ℝ ∞ (g i))
    (n : ℕ)
    (hfbound : ∀ k : ℕ, k ≤ n → ∃ A : ℝ, 0 ≤ A ∧
      ∀ i x, |iteratedDeriv k (f i) x| ≤ A)
    (hgbound : ∀ k : ℕ, k ≤ n → ∃ B : ℝ, 0 ≤ B ∧
      ∀ i x, |iteratedDeriv k (g i) x| ≤ B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ i x,
      |iteratedDeriv n (fun y => f i y * g i y) x| ≤ K := by
  classical
  have houter (k : Fin (n + 1)) := hfbound k.val (Nat.le_of_lt_succ k.isLt)
  have hinner (k : Fin (n + 1)) := hgbound k.val (Nat.le_of_lt_succ k.isLt)
  choose A hA hAb using houter
  choose B hB hBb using hinner
  let C : ℝ := ∑ k : Fin (n + 1), A k
  let D : ℝ := ∑ k : Fin (n + 1), B k
  have hC : 0 ≤ C := Finset.sum_nonneg (fun k _ => hA k)
  have hD : 0 ≤ D := Finset.sum_nonneg (fun k _ => hB k)
  let K : ℝ := ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * C * D
  refine ⟨K, Finset.sum_nonneg (fun k _ => by positivity), fun i x => ?_⟩
  rw [iteratedDeriv_fun_mul ((hf i).contDiffAt.of_le (by simp))
    ((hg i).contDiffAt.of_le (by simp))]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro k hk
  have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  let j : Fin (n + 1) := ⟨k, Nat.lt_succ_of_le hkn⟩
  let l : Fin (n + 1) := ⟨n - k, Nat.lt_succ_of_le (Nat.sub_le n k)⟩
  have hfirst : |iteratedDeriv k (f i) x| ≤ C :=
    (hAb j i x).trans (Finset.single_le_sum (fun a _ => hA a) (Finset.mem_univ j))
  have hsecond : |iteratedDeriv (n - k) (g i) x| ≤ D :=
    (hBb l i x).trans (Finset.single_le_sum (fun a _ => hB a) (Finset.mem_univ l))
  rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
  exact mul_le_mul (mul_le_mul_of_nonneg_left hfirst (Nat.cast_nonneg _)) hsecond
    (abs_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hC)

/-- Positive-order jets of two lift families control positive-order jets
of their composition, without any zeroth-order value bound. -/
theorem positive_iteratedDeriv_comp_uniform_bound
    {ι : Type*} (f g : ι → ℝ → ℝ)
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) (hg : ∀ i, ContDiff ℝ ∞ (g i))
    (hfbound : ∀ k : ℕ, 1 ≤ k → ∃ A : ℝ, 0 ≤ A ∧
      ∀ i x, |iteratedDeriv k (f i) x| ≤ A)
    (hgbound : ∀ k : ℕ, 1 ≤ k → ∃ B : ℝ, 0 ≤ B ∧
      ∀ i x, |iteratedDeriv k (g i) x| ≤ B) :
    ∀ n : ℕ, 1 ≤ n → ∃ K : ℝ, 0 ≤ K ∧
      ∀ i x, |iteratedDeriv n (fun y => f i (g i y)) x| ≤ K := by
  let q (i : ι) : ℝ → ℝ := fun x => deriv (f i) (g i x)
  have hdf (i : ι) : ContDiff ℝ ∞ (deriv (f i)) :=
    (contDiff_infty_iff_deriv.mp (hf i)).2
  have hdg (i : ι) : ContDiff ℝ ∞ (deriv (g i)) :=
    (contDiff_infty_iff_deriv.mp (hg i)).2
  have hq (i : ι) : ContDiff ℝ ∞ (q i) := (hdf i).comp (hg i)
  have hqb (k : ℕ) : ∃ B : ℝ, 0 ≤ B ∧
      ∀ i x, |iteratedDeriv k (q i) x| ≤ B := by
    apply iteratedDeriv_comp_uniform_bound (fun i => deriv (f i)) g isOpen_univ
      (fun i => (hdf i).contDiffOn) hg (fun _ _ => mem_univ _) k
    · intro j _
      obtain ⟨B, hB, hb⟩ := hfbound (j + 1) (by omega)
      refine ⟨B, hB, fun i x => ?_⟩
      rw [← iteratedDeriv_succ']
      exact hb i (g i x)
    · exact fun j hj _ => hgbound j hj
  intro n hn
  obtain ⟨K, hK, hb⟩ := iteratedDeriv_mul_uniform_bound q (fun i => deriv (g i))
    hq hdg (n - 1) (fun k _ => hqb k) (fun k _ => by
      obtain ⟨B, hB, hb⟩ := hgbound (k + 1) (by omega)
      exact ⟨B, hB, fun i x => by rw [← iteratedDeriv_succ']; exact hb i x⟩)
  refine ⟨K, hK, fun i x => ?_⟩
  have heq : deriv (fun y => f i (g i y)) = fun y => q i y * deriv (g i) y := by
    funext y
    exact deriv_comp y ((hf i).differentiable (by simp) (g i y))
      ((hg i).differentiable (by simp) y)
  have hn' : n = n - 1 + 1 := (Nat.sub_add_cancel hn).symm
  rw [hn', iteratedDeriv_succ', heq]
  exact hb i x

theorem iteratedDeriv_sub_const_of_pos
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (n : ℕ) (hn : 1 ≤ n) (c x : ℝ) :
    iteratedDeriv n (fun y => f y - c) x = iteratedDeriv n f x := by
  rw [iteratedDeriv_fun_sub (hf.contDiffAt.of_le (by simp))
    (contDiffAt_const : ContDiffAt ℝ (n : ℕ∞ω) (fun _ : ℝ => c) x)]
  simp only [iteratedDeriv_const, if_neg (by omega : n ≠ 0), sub_zero]

theorem iteratedDeriv_oddPart_abs_le
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (n : ℕ) {A : ℝ}
    (hA : ∀ x, |iteratedDeriv n f x| ≤ A) (x : ℝ) :
    |iteratedDeriv n (ContinuousFlexibility.Statements.oddPart f) x| ≤ A := by
  have heq : ContinuousFlexibility.Statements.oddPart f =
      fun y => (f y - f (-y)) / 2 := rfl
  rw [heq, iteratedDeriv_div_const,
    iteratedDeriv_fun_sub (hf.contDiffAt.of_le (by simp))
      ((hf.comp contDiff_neg).contDiffAt.of_le (by simp)),
    iteratedDeriv_comp_neg]
  simp only [smul_eq_mul, abs_div, abs_ofNat]
  apply (div_le_div_of_nonneg_right (abs_sub_le _ _) (by norm_num : (0 : ℝ) ≤ 2)).trans
  have hneg : |(-1 : ℝ) ^ n * iteratedDeriv n f (-x)| ≤ A := by
    simpa only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul] using hA (-x)
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
  nlinarith only [hA x, hneg]

theorem iteratedDeriv_evenPart_abs_le
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (n : ℕ) {A : ℝ}
    (hA : ∀ x, |iteratedDeriv n f x| ≤ A) (x : ℝ) :
    |iteratedDeriv n (ContinuousFlexibility.Statements.evenPart f) x| ≤ A := by
  have heq : ContinuousFlexibility.Statements.evenPart f =
      fun y => (f y + f (-y)) / 2 := rfl
  rw [heq, iteratedDeriv_div_const,
    iteratedDeriv_fun_add (hf.contDiffAt.of_le (by simp))
      ((hf.comp contDiff_neg).contDiffAt.of_le (by simp)),
    iteratedDeriv_comp_neg]
  simp only [smul_eq_mul, abs_div, abs_ofNat]
  apply (div_le_div_of_nonneg_right (abs_add_le _ _) (by norm_num : (0 : ℝ) ≤ 2)).trans
  have hneg : |(-1 : ℝ) ^ n * iteratedDeriv n f (-x)| ≤ A := by
    simpa only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul] using hA (-x)
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
  nlinarith only [hA x, hneg]

end ContinuousFlexibility.Analysis

