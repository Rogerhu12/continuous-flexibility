import ContinuousFlexibility.Analysis.ReturnCorrectionDisplacementRegularity
import ContinuousFlexibility.Analysis.ScalarJetFamilyBounds

/-!
# Angular jets of a smooth compact parameter integral

All derivative identities are for the actual scalar integral. Joint
smoothness supplies continuity and domination on each compact rectangle,
so repeated differentiation uses the existing interval-integral theorem.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open scoped ContDiff

theorem iteratedDeriv_intervalIntegral_smooth
    {H : ℝ → ℝ → ℝ} (hH : ContDiff ℝ ∞ (fun p : PolarPoint => H p.1 p.2))
    (a b : ℝ) (n : ℕ) (θ : ℝ) :
    iteratedDeriv n (fun x => ∫ t in a..b, H t x) θ =
      ∫ t in a..b, iteratedDeriv n (H t) θ := by
  have hs (t : ℝ) : ContDiff ℝ ∞ (H t) :=
    hH.comp (contDiff_const.prodMk contDiff_id)
  have hc (k : ℕ) : Continuous (fun p : PolarPoint => iteratedDeriv k (H p.1) p.2) :=
    (angularRegular_of_contDiff hH k).iteratedDeriv_continuous
  induction n generalizing θ with
  | zero => simp only [iteratedDeriv_zero]
  | succ n ih =>
    have hd (t : ℝ) : Differentiable ℝ (iteratedDeriv n (H t)) :=
      (hs t).differentiable_iteratedDeriv n (by simp)
    have hdc : Continuous (fun p : PolarPoint => deriv (iteratedDeriv n (H p.1)) p.2) := by
      simpa only [iteratedDeriv_succ] using hc (n + 1)
    have hder := angular_parameter_integral_hasDerivAt (hc n) hd hdc a b θ
    have heq : iteratedDeriv n (fun x => ∫ t in a..b, H t x) =
        fun x => ∫ t in a..b, iteratedDeriv n (H t) x := funext ih
    rw [iteratedDeriv_succ, heq, hder.deriv]
    simp only [iteratedDeriv_succ]

theorem iteratedDeriv_intervalIntegral_abs_le
    {H : ℝ → ℝ → ℝ} (hH : ContDiff ℝ ∞ (fun p : PolarPoint => H p.1 p.2))
    (a b : ℝ) (n : ℕ) {A : ℝ}
    (hA : ∀ t ∈ uIcc a b, ∀ θ, |iteratedDeriv n (H t) θ| ≤ A) (θ : ℝ) :
    |iteratedDeriv n (fun x => ∫ t in a..b, H t x) θ| ≤ A * |b - a| := by
  rw [iteratedDeriv_intervalIntegral_smooth hH]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := b) (f := fun t => iteratedDeriv n (H t) θ)
    (fun t ht => by
      simpa only [Real.norm_eq_abs] using hA t (uIoc_subset_uIcc ht) θ)
  simpa only [Real.norm_eq_abs] using h

/-- The removable divided difference retains uniform angular jet bounds.
Only positive-order jets of the three circle-coordinate maps are needed. -/
theorem dslope_comp_iteratedDeriv_uniform_bound
    {ι : Type*} (G X E : ι → ℝ → ℝ)
    (hG : ∀ i, ContDiff ℝ ∞ (G i))
    (hX : ∀ i, ContDiff ℝ ∞ (X i)) (hE : ∀ i, ContDiff ℝ ∞ (E i))
    (hGb : ∀ k : ℕ, 1 ≤ k → ∃ A : ℝ, 0 ≤ A ∧
      ∀ i θ, |iteratedDeriv k (G i) θ| ≤ A)
    (hXb : ∀ k : ℕ, 1 ≤ k → ∃ A : ℝ, 0 ≤ A ∧
      ∀ i θ, |iteratedDeriv k (X i) θ| ≤ A)
    (hEb : ∀ k : ℕ, 1 ≤ k → ∃ A : ℝ, 0 ≤ A ∧
      ∀ i θ, |iteratedDeriv k (E i) θ| ≤ A)
    (n : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ i θ,
      |iteratedDeriv n (fun x => dslope (G i) (X i x) (X i x + E i x)) θ| ≤ A := by
  let I := ι × {t : ℝ // t ∈ Icc (0 : ℝ) 1}
  let F (j : I) : ℝ → ℝ := fun θ => X j.1 θ + j.2.val * E j.1 θ
  have hF (j : I) : ContDiff ℝ ∞ (F j) :=
    (hX j.1).add (contDiff_const.mul (hE j.1))
  have hFb (k : ℕ) (hk : 1 ≤ k) :
      ∃ A : ℝ, 0 ≤ A ∧ ∀ j θ, |iteratedDeriv k (F j) θ| ≤ A := by
    obtain ⟨A, hA, hAb⟩ := hXb k hk
    obtain ⟨B, hB, hBb⟩ := hEb k hk
    refine ⟨A + B, add_nonneg hA hB, fun j θ => ?_⟩
    have heq : F j = fun x => X j.1 x + j.2.val * E j.1 x := rfl
    rw [heq, iteratedDeriv_fun_add ((hX j.1).contDiffAt.of_le (by simp))
      ((contDiff_const.mul (hE j.1)).contDiffAt.of_le (by simp)),
      iteratedDeriv_const_mul j.2.val ((hE j.1).contDiffAt.of_le (by simp))]
    apply (abs_add_le _ _).trans
    rw [abs_mul, abs_of_nonneg j.2.property.1]
    apply add_le_add (hAb j.1 θ)
    exact (mul_le_mul j.2.property.2 (hBb j.1 θ) (abs_nonneg _) zero_le_one).trans_eq
      (one_mul _)
  have hDG (i : ι) : ContDiff ℝ ∞ (deriv (G i)) :=
    (contDiff_infty_iff_deriv.mp (hG i)).2
  obtain ⟨A, hA, hAb⟩ := iteratedDeriv_comp_uniform_bound
    (fun j : I => deriv (G j.1)) F isOpen_univ
    (fun j => (hDG j.1).contDiffOn) hF (fun _ _ => mem_univ _) n
    (fun k _ => by
      obtain ⟨B, hB, hb⟩ := hGb (k + 1) (by omega)
      refine ⟨B, hB, fun j θ => ?_⟩
      rw [← iteratedDeriv_succ']
      exact hb j.1 (F j θ))
    (fun k hk _ => hFb k hk)
  refine ⟨A, hA, fun i θ => ?_⟩
  let H : ℝ → ℝ → ℝ := fun t x => deriv (G i) (X i x + t * E i x)
  have hH : ContDiff ℝ ∞ (fun p : PolarPoint => H p.1 p.2) :=
    (hDG i).comp (((hX i).comp contDiff_snd).add
      (contDiff_fst.mul ((hE i).comp contDiff_snd)))
  have heq : (fun x => dslope (G i) (X i x) (X i x + E i x)) =
      fun x => ∫ t in (0 : ℝ)..1, H t x :=
    funext (fun x => ContinuousFlexibility.Statements.returnCorrection_dslope_integral
      ((hG i).of_le (by simp)) (X i x) (E i x))
  rw [heq]
  have h := iteratedDeriv_intervalIntegral_abs_le hH 0 1 n
    (fun t ht x => hAb (i, ⟨t, by simpa only [uIcc_of_le zero_le_one] using ht⟩) x) θ
  simpa only [sub_zero, abs_one, mul_one] using h

end ContinuousFlexibility.Analysis

