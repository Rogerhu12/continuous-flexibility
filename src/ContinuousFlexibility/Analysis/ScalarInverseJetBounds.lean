import ContinuousFlexibility.Analysis.N01ReturnChartSmoothness
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Uniform positive-order jets of actual scalar inverses

A family of smooth increasing maps with one common derivative lower
bound and bounded positive-order jets has bounded positive-order inverse
jets. The inverse maps are the specified functions with their two inverse
identities; their smoothness and derivatives are derived.

The proof differentiates the exact identity
`g' = (f' ∘ g)⁻¹`. At each order only lower inverse jets enter.
The reciprocal has bounded jets on the common compact range of `f'`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped ContDiff Topology BigOperators

/-- A finite collection of uniform scalar jet bounds controls the
corresponding derivative of a family of compositions. The inner value
itself need not be bounded. -/
theorem iteratedDeriv_comp_uniform_bound
    {ι : Type*} (f g : ι → ℝ → ℝ) {U : Set ℝ} (hU : IsOpen U)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) U) (hg : ∀ i, ContDiff ℝ ∞ (g i))
    (hmap : ∀ i x, g i x ∈ U) (n : ℕ)
    (hfbound : ∀ k : ℕ, k ≤ n → ∃ A : ℝ, 0 ≤ A ∧
      ∀ i x, |iteratedDeriv k (f i) (g i x)| ≤ A)
    (hgbound : ∀ k : ℕ, 1 ≤ k → k ≤ n → ∃ B : ℝ, 0 ≤ B ∧
      ∀ i x, |iteratedDeriv k (g i) x| ≤ B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ i x,
      |iteratedDeriv n (fun y => f i (g i y)) x| ≤ K := by
  classical
  have houter (k : Fin (n + 1)) := hfbound k.val (Nat.le_of_lt_succ k.isLt)
  choose A hA hAb using houter
  have hinner (k : Fin (n + 1)) :
      ∃ B : ℝ, 0 ≤ B ∧ ∀ i x, 1 ≤ k.val →
        |iteratedDeriv k.val (g i) x| ≤ B := by
    by_cases hk : 1 ≤ k.val
    · obtain ⟨B, hB, hb⟩ := hgbound k.val hk (Nat.le_of_lt_succ k.isLt)
      exact ⟨B, hB, fun i x _ => hb i x⟩
    · exact ⟨0, le_rfl, fun _ _ h => False.elim (hk h)⟩
  choose B hB hBb using hinner
  let C : ℝ := ∑ k : Fin (n + 1), A k
  let D : ℝ := 1 + ∑ k : Fin (n + 1), B k
  have hC : 0 ≤ C := Finset.sum_nonneg (fun k _ => hA k)
  have hD : 1 ≤ D := le_add_of_nonneg_right (Finset.sum_nonneg (fun k _ => hB k))
  refine ⟨(n.factorial : ℝ) * C * D ^ n,
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hC)
      (pow_nonneg (zero_le_one.trans hD) _), fun i x => ?_⟩
  have hout (k : ℕ) (hk : k ≤ n) :
      ‖iteratedFDerivWithin ℝ k (f i) U (g i x)‖ ≤ C := by
    rw [iteratedFDerivWithin_of_isOpen k hU (hmap i x),
      norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
    let j : Fin (n + 1) := ⟨k, Nat.lt_succ_of_le hk⟩
    exact (hAb j i x).trans (Finset.single_le_sum (fun l _ => hA l) (Finset.mem_univ j))
  have hin (k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
      ‖iteratedFDeriv ℝ k (g i) x‖ ≤ D ^ k := by
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
    let j : Fin (n + 1) := ⟨k, Nat.lt_succ_of_le hkn⟩
    have hsum : B j ≤ ∑ l : Fin (n + 1), B l :=
      Finset.single_le_sum (fun l _ => hB l) (Finset.mem_univ j)
    have hb : |iteratedDeriv k (g i) x| ≤ D :=
      (hBb j i x hk).trans (hsum.trans (by dsimp only [D]; linarith))
    have hpow : D ≤ D ^ k := by simpa only [pow_one] using pow_le_pow_right₀ hD hk
    exact hb.trans hpow
  have h := norm_iteratedFDeriv_comp_le'
    (fun y hy => by obtain ⟨x, rfl⟩ := hy; exact hmap i x)
    hU.uniqueDiffOn (hf i) (hg i) (n := n) (by simp) x hout hin
  simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs,
    Function.comp_def] using h

/-- Bounds through one finite order require forward bounds only through
that same order. No bound on the values of either lift is needed. -/
theorem inverse_iteratedDeriv_uniform_bound_finite
    {ι : Type*} (f g : ι → ℝ → ℝ) (hf : ∀ i, ContDiff ℝ ∞ (f i))
    {a : ℝ} (ha : 0 < a) (hlower : ∀ i x, a ≤ deriv (f i) x)
    (hleft : ∀ i x, g i (f i x) = x) (hright : ∀ i x, f i (g i x) = x)
    (N : ℕ)
    (hfbound : ∀ n : ℕ, 1 ≤ n → n ≤ N → ∃ A : ℝ, 0 ≤ A ∧
      ∀ i x, |iteratedDeriv n (f i) x| ≤ A) :
    ∀ n : ℕ, 1 ≤ n → n ≤ N → ∃ K : ℝ, 0 ≤ K ∧
      ∀ i x, |iteratedDeriv n (g i) x| ≤ K := by
  by_cases hN : 1 ≤ N
  swap
  · intro n hn hnN
    omega
  have hpos (i : ι) (x : ℝ) : 0 < deriv (f i) x := ha.trans_le (hlower i x)
  have hg (i : ι) : ContDiff ℝ ∞ (g i) :=
    ContinuousFlexibility.Statements.returnChart_inverse_contDiff
      (f i) (g i) (hf i) (hpos i) (hleft i) (hright i)
  have hdf (i : ι) : ContDiff ℝ ∞ (deriv (f i)) :=
    (contDiff_infty_iff_deriv.mp (hf i)).2
  let q (i : ι) : ℝ → ℝ := fun x => deriv (f i) (g i x)
  have hq (i : ι) : ContDiff ℝ ∞ (q i) := (hdf i).comp (hg i)
  have hqpos (i : ι) (x : ℝ) : q i x ∈ Ioi (0 : ℝ) := hpos i (g i x)
  have hdg (i : ι) : deriv (g i) = fun x => (q i x)⁻¹ := by
    funext x
    exact (ContinuousFlexibility.Statements.returnChart_hasDerivAt_inverse
      (f i) (g i) (hpos i) (hleft i) (hright i) x).deriv
  obtain ⟨A, hA, hAb⟩ := hfbound 1 le_rfl hN
  have hqrange (i : ι) (x : ℝ) : q i x ∈ Icc a A := by
    refine ⟨hlower i (g i x), ?_⟩
    exact (le_abs_self _).trans (by simpa only [iteratedDeriv_one] using hAb i (g i x))
  have hinv : ContDiffOn ℝ ∞ (fun x : ℝ => x⁻¹) (Ioi (0 : ℝ)) :=
    fun x hx => (contDiffAt_inv ℝ (ne_of_gt hx)).contDiffWithinAt
  have hinvbound (k : ℕ) :
      ∃ B : ℝ, 0 ≤ B ∧ ∀ i x, |iteratedDeriv k (fun t : ℝ => t⁻¹) (q i x)| ≤ B := by
    have hc₀ : ContinuousOn (iteratedDerivWithin k (fun t : ℝ => t⁻¹) (Ioi (0 : ℝ)))
        (Ioi (0 : ℝ)) :=
      hinv.continuousOn_iteratedDerivWithin (by simp) isOpen_Ioi.uniqueDiffOn
    have hc : ContinuousOn (iteratedDeriv k (fun t : ℝ => t⁻¹)) (Ioi (0 : ℝ)) :=
      hc₀.congr (fun x hx => (iteratedDerivWithin_of_isOpen isOpen_Ioi hx).symm)
    have hcompact := hc.mono (show Icc a A ⊆ Ioi (0 : ℝ) from fun x hx => ha.trans_le hx.1)
    obtain ⟨B, hb⟩ := isCompact_Icc.exists_bound_of_continuousOn hcompact
    refine ⟨max B 0, le_max_right _ _, fun i x => ?_⟩
    have hnorm : |iteratedDeriv k (fun t : ℝ => t⁻¹) (q i x)| ≤ B := by
      simpa only [Real.norm_eq_abs] using hb (q i x) (hqrange i x)
    exact hnorm.trans (le_max_left _ _)
  have hall (n : ℕ) : n + 1 ≤ N → ∃ K : ℝ, 0 ≤ K ∧
      ∀ i x, |iteratedDeriv (n + 1) (g i) x| ≤ K := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hnN
      have hqb (k : ℕ) (hkn : k ≤ n) :
          ∃ B : ℝ, 0 ≤ B ∧ ∀ i x, |iteratedDeriv k (q i) x| ≤ B := by
        apply iteratedDeriv_comp_uniform_bound (fun i => deriv (f i)) g isOpen_univ
          (fun i => (hdf i).contDiffOn) hg (fun _ _ => mem_univ _) k
        · intro j hjk
          obtain ⟨B, hB, hb⟩ := hfbound (j + 1) (Nat.le_add_left 1 j) (by omega)
          refine ⟨B, hB, fun i x => ?_⟩
          rw [← iteratedDeriv_succ']
          exact hb i (g i x)
        · intro j hj hjk
          obtain ⟨B, hB, hb⟩ := ih (j - 1) (by omega) (by omega)
          refine ⟨B, hB, fun i x => ?_⟩
          simpa only [Nat.sub_add_cancel hj] using hb i x
      obtain ⟨K, hK, hb⟩ := iteratedDeriv_comp_uniform_bound
        (fun _ : ι => fun t : ℝ => t⁻¹) q isOpen_Ioi (fun _ => hinv) hq hqpos n
        (fun k _ => hinvbound k) (fun k _ hkn => hqb k hkn)
      refine ⟨K, hK, fun i x => ?_⟩
      rw [iteratedDeriv_succ', hdg i]
      exact hb i x
  intro n hn hnN
  obtain ⟨K, hK, hb⟩ := hall (n - 1) (by omega)
  exact ⟨K, hK, fun i x => by simpa only [Nat.sub_add_cancel hn] using hb i x⟩

/-- All positive-order inverse jets are uniformly bounded. No bound on
the values of a circle lift or its inverse is required. -/
theorem inverse_iteratedDeriv_uniform_bound
    {ι : Type*} (f g : ι → ℝ → ℝ) (hf : ∀ i, ContDiff ℝ ∞ (f i))
    {a : ℝ} (ha : 0 < a) (hlower : ∀ i x, a ≤ deriv (f i) x)
    (hleft : ∀ i x, g i (f i x) = x) (hright : ∀ i x, f i (g i x) = x)
    (hfbound : ∀ n : ℕ, 1 ≤ n → ∃ A : ℝ, 0 ≤ A ∧
      ∀ i x, |iteratedDeriv n (f i) x| ≤ A) :
    ∀ n : ℕ, 1 ≤ n → ∃ K : ℝ, 0 ≤ K ∧
      ∀ i x, |iteratedDeriv n (g i) x| ≤ K := by
  intro n hn
  exact inverse_iteratedDeriv_uniform_bound_finite f g hf ha hlower hleft hright
    n (fun k hk _ => hfbound k hk) n hn le_rfl

end ContinuousFlexibility.Analysis

