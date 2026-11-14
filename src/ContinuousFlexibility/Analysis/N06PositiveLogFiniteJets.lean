module

public import ContinuousFlexibility.Analysis.N06NuFiniteDifference
public import ContinuousFlexibility.Analysis.N06RootJetTransportCalculus
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Finite logarithmic jets with a genuine positive normalization

The constant is fixed before the scalar function and its small jet
difference from one. Only the value at the evaluation point needs a
positive lower bound; the whole straight value segment then stays in a
fixed compact subset of the positive real axis.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped ContDiff Topology BigOperators

private theorem n06_log_finite_derivative_bound (M : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k, k ≤ n → ∀ x ∈ Icc (1 / 2 : ℝ) M,
      ‖iteratedFDeriv ℝ k Real.log x‖ ≤ C := by
  classical
  have hchoices (i : Fin (n + 1)) : ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ Icc (1 / 2 : ℝ) M, ‖iteratedFDeriv ℝ i.val Real.log x‖ ≤ C := by
    have hc : ContinuousOn (fun x => ‖iteratedFDeriv ℝ i.val Real.log x‖)
        (Icc (1 / 2 : ℝ) M) := by
      intro x hx
      have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx.1
      have hlog : ContDiffAt ℝ ∞ Real.log x := Real.contDiffAt_log.mpr hxpos.ne'
      exact (hlog.continuousAt_iteratedFDeriv (by simp)).norm.continuousWithinAt
    obtain ⟨C, hC⟩ := (isCompact_Icc.image_of_continuousOn hc).bddAbove
    exact ⟨max C 0, le_max_right _ _, fun x hx =>
      (hC ⟨x, hx, rfl⟩).trans (le_max_left _ _)⟩
  choose c hc hb using hchoices
  refine ⟨∑ i : Fin (n + 1), c i, Finset.sum_nonneg (fun i _ => hc i), ?_⟩
  intro k hk x hx
  let i : Fin (n + 1) := ⟨k, by omega⟩
  exact (hb i x hx).trans
    (Finset.single_le_sum (fun j _ => hc j) (Finset.mem_univ i))

/-- Taking the logarithm preserves a finite jet difference from one.
The upper budget is used only to choose the constant; the output retains
the actual smaller difference `δ`. -/
theorem n06_log_finite_jets_of_one_difference (n : ℕ) {B : ℝ} (hB : 0 ≤ B) :
    ∃ Q : ℝ, 0 ≤ Q ∧ ∀ (f : ℝ → ℝ) (x δ : ℝ),
      ContDiffAt ℝ ∞ f x → (1 / 2 : ℝ) ≤ f x → 0 ≤ δ → δ ≤ B →
      (∀ k, k ≤ n → |iteratedDeriv k (fun t => f t - 1) x| ≤ δ) →
      ∀ k, k ≤ n → |iteratedDeriv k (fun t => Real.log (f t)) x| ≤ Q * δ := by
  classical
  let M : ℝ := B + 1
  have hM : 0 ≤ M := add_nonneg hB zero_le_one
  obtain ⟨C, hC, houter⟩ := n06_log_finite_derivative_bound M (n + 1)
  let Q : ℝ := ∑ i : Fin (n + 1), n06CompositionDifferenceCost i.val C M
  have hcost (i : Fin (n + 1)) : 0 ≤ n06CompositionDifferenceCost i.val C M :=
    n06CompositionDifferenceCost_nonneg i.val hC hM
  refine ⟨Q, Finset.sum_nonneg (fun i _ => hcost i), ?_⟩
  intro f x δ hf hpositive hδ hδB hdifference
  have hone (j : ℕ) : |iteratedDeriv j (fun _ : ℝ => (1 : ℝ)) x| ≤ 1 := by
    simp only [iteratedDeriv_const]
    split_ifs <;> norm_num
  have hdiff (j : ℕ) (hj : j ≤ n) :
      |iteratedDeriv j f x - iteratedDeriv j (fun _ : ℝ => (1 : ℝ)) x| ≤ δ := by
    have he := iteratedDeriv_fun_sub
      (hf.of_le (by simp : (j : ℕ∞ω) ≤ ∞))
      (contDiffAt_const : ContDiffAt ℝ (j : ℕ∞ω) (fun _ : ℝ => (1 : ℝ)) x)
    exact (congrArg abs he).symm.trans_le (hdifference j hj)
  have hF (j : ℕ) (hj : j ≤ n) : |iteratedDeriv j f x| ≤ M := by
    have ht := abs_add_le (iteratedDeriv j f x -
      iteratedDeriv j (fun _ : ℝ => (1 : ℝ)) x)
      (iteratedDeriv j (fun _ : ℝ => (1 : ℝ)) x)
    rw [sub_add_cancel] at ht
    exact ht.trans ((add_le_add (hdiff j hj) (hone j)).trans
      (add_le_add hδB (le_refl (1 : ℝ))))
  have hfx : f x ∈ Icc (1 / 2 : ℝ) M :=
    ⟨hpositive, (le_abs_self _).trans (by simpa only [iteratedDeriv_zero] using hF 0 (Nat.zero_le n))⟩
  have honeMem : (1 : ℝ) ∈ Icc (1 / 2 : ℝ) M := ⟨by norm_num, by dsimp only [M]; linarith⟩
  have hsegment : segment ℝ 1 (f x) ⊆ Icc (1 / 2 : ℝ) M :=
    (convex_Icc _ _).segment_subset honeMem hfx
  have hsmooth : ∀ y ∈ segment ℝ 1 (f x), ContDiffAt ℝ ∞ Real.log y := by
    intro y hy
    exact Real.contDiffAt_log.mpr
      (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) (hsegment hy).1).ne'
  have hdiff₀ : ‖f x - 1‖ ≤ δ := by
    simpa only [iteratedDeriv_zero, Real.norm_eq_abs] using hdifference 0 (Nat.zero_le n)
  intro k hk
  have houterDiff (j : ℕ) (hj : j ≤ k) :
      ‖iteratedFDeriv ℝ j Real.log (f x) - iteratedFDeriv ℝ j Real.log 1‖ ≤ C * δ :=
    (n06_iteratedFDeriv_difference_le_segment j hsmooth
      (fun y hy => houter (j + 1) (by omega) y (hsegment hy))).trans
        (mul_le_mul_of_nonneg_left hdiff₀ hC)
  have h := n06_iteratedFDeriv_comp_difference_le
    (Φ := Real.log) (u := f) (v := fun _ : ℝ => (1 : ℝ)) (x := x) k
    (hsmooth (f x) (right_mem_segment ℝ _ _))
    (hsmooth 1 (left_mem_segment ℝ _ _)) hf contDiffAt_const hC hM hδ
    (fun j hj => houter j (by omega) (f x) hfx) houterDiff
    (fun j hj => by
      simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] using
        hF j (hj.trans hk))
    (fun j _ => by
      simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] using
        (hone j).trans (show (1 : ℝ) ≤ M by dsimp only [M]; linarith))
    (fun j hj => by
      simpa only [n06_norm_iteratedFDeriv_sub_eq_iteratedDeriv, Real.norm_eq_abs] using
        hdiff j (hj.trans hk))
  simp only [n06_norm_iteratedFDeriv_sub_eq_iteratedDeriv, Function.comp_def,
    Real.log_one, iteratedDeriv_fun_const_zero, sub_zero, Real.norm_eq_abs] at h
  let i : Fin (n + 1) := ⟨k, by omega⟩
  have hi : n06CompositionDifferenceCost k C M ≤ Q :=
    Finset.single_le_sum (fun j _ => hcost j) (Finset.mem_univ i)
  exact h.trans (mul_le_mul_of_nonneg_right hi hδ)

/-- The genuine angular slice costs at most its full physical jet.
Smoothness is required only at the evaluated physical point. -/
theorem n06_angularSlice_iteratedDeriv_le
    {f : ℝ × ℝ → ℝ} {r θ : ℝ} (hf : ContDiffAt ℝ ∞ f (r, θ)) (n : ℕ) :
    |iteratedDeriv n (fun t => f (r, t)) θ| ≤ ‖iteratedFDeriv ℝ n f (r, θ)‖ := by
  let L : ℝ →L[ℝ] ℝ × ℝ := ContinuousLinearMap.inr ℝ ℝ ℝ
  let g : ℝ × ℝ → ℝ := fun p => f (p + (r, 0))
  have hpoint : L θ + (r, 0) = (r, θ) := by
    simp only [L, ContinuousLinearMap.inr_apply, Prod.mk_add_mk, zero_add, add_zero]
  have hsource : ContDiffAt ℝ (n : ℕ∞ω) f (L θ + (r, 0)) := by
    rw [hpoint]
    exact hf.of_le (by simp)
  have hg : ContDiffAt ℝ (n : ℕ∞ω) g (L θ) :=
    hsource.comp (L θ) (contDiffAt_id.add contDiffAt_const)
  have he := congrArg
    (fun A : ContinuousMultilinearMap ℝ (fun _ : Fin n => ℝ) ℝ => A (fun _ => 1))
      (n06_iteratedFDeriv_compCLM_at L n hg)
  have hslice : g ∘ L = fun t => f (r, t) := by
    funext t
    simp only [Function.comp_def, g, L, ContinuousLinearMap.inr_apply,
      Prod.mk_add_mk, zero_add, add_zero]
  rw [hslice] at he
  change iteratedDeriv n (fun t => f (r, t)) θ =
    ((iteratedFDeriv ℝ n g (L θ)).compContinuousLinearMap
      (fun _ => L)) (fun _ => 1) at he
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply] at he
  have hshift : iteratedFDeriv ℝ n g (L θ) = iteratedFDeriv ℝ n f (r, θ) := by
    change iteratedFDeriv ℝ n (fun p => f (p + (r, 0))) (L θ) = _
    rw [iteratedFDeriv_comp_add_right, hpoint]
  rw [hshift] at he
  have he' : iteratedDeriv n (fun t => f (r, t)) θ =
      iteratedFDeriv ℝ n f (r, θ) (fun _ => (0, 1)) := by
    simpa only [L, ContinuousLinearMap.inr_apply] using he
  rw [he', ← Real.norm_eq_abs]
  simpa only [Prod.norm_def, norm_zero, norm_one, max_eq_right zero_le_one,
    Finset.prod_const_one, mul_one] using
      (iteratedFDeriv ℝ n f (r, θ)).le_opNorm (fun _ => (0, 1))

end ContinuousFlexibility.Analysis
