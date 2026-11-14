module

public import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# Finite ordinary jets under actual smooth operations

The pointwise notion retains ordinary smoothness of the two actual
functions. Common smooth composition, pairing, and differentiation
preserve the appropriate finite order without a common infinite-order
neighborhood assumption.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open scoped ContDiff BigOperators

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

structure FiniteFullJetMatch (n : ℕ) (x : E) (f g : E → F) : Prop where
  left_smooth : ContDiffAt ℝ ∞ f x
  right_smooth : ContDiffAt ℝ ∞ g x
  jets : ∀ k, k ≤ n → iteratedFDeriv ℝ k f x = iteratedFDeriv ℝ k g x

theorem FiniteFullJetMatch.value {n : ℕ} {x : E} {f g : E → F}
    (h : FiniteFullJetMatch n x f g) : f x = g x := by
  have he := congrArg (fun A : E [×0]→L[ℝ] F => A (fun i => Fin.elim0 i))
    (h.jets 0 (Nat.zero_le n))
  simpa only [iteratedFDeriv_zero_apply] using he

theorem FiniteFullJetMatch.mono {m n : ℕ} {x : E} {f g : E → F}
    (h : FiniteFullJetMatch n x f g) (hmn : m ≤ n) : FiniteFullJetMatch m x f g :=
  ⟨h.left_smooth, h.right_smooth, fun k hk => h.jets k (hk.trans hmn)⟩

theorem finiteFullJetMatch_refl {n : ℕ} {x : E} {f : E → F}
    (hf : ContDiffAt ℝ ∞ f x) : FiniteFullJetMatch n x f f :=
  ⟨hf, hf, fun _ _ => rfl⟩

theorem FiniteFullJetMatch.comp {n : ℕ} {x : E} {f g : E → F} {H : F → G}
    (h : FiniteFullJetMatch n x f g) (hH : ContDiffAt ℝ ∞ H (f x)) :
    FiniteFullJetMatch n x (H ∘ f) (H ∘ g) := by
  have hHg : ContDiffAt ℝ ∞ H (g x) := h.value ▸ hH
  refine ⟨hH.comp x h.left_smooth, hHg.comp x h.right_smooth, ?_⟩
  intro k hk
  rw [iteratedFDeriv_comp hH h.left_smooth (by simp : (k : ℕ∞ω) ≤ ∞),
    iteratedFDeriv_comp hHg h.right_smooth (by simp : (k : ℕ∞ω) ≤ ∞)]
  unfold FormalMultilinearSeries.taylorComp
  apply Finset.sum_congr rfl
  intro c _
  ext v
  simp only [FormalMultilinearSeries.compAlongOrderedFinpartition_apply,
    OrderedFinpartition.applyOrderedFinpartition_apply, ftaylorSeries]
  rw [h.value]
  congr 1
  funext j
  rw [h.jets (c.partSize j) ((c.partSize_le j).trans hk)]

theorem FiniteFullJetMatch.prodMk {n : ℕ} {x : E}
    {f g : E → F} {u v : E → G}
    (h : FiniteFullJetMatch n x f g) (k : FiniteFullJetMatch n x u v) :
    FiniteFullJetMatch n x (fun y => (f y, u y)) (fun y => (g y, v y)) := by
  refine ⟨h.left_smooth.prodMk k.left_smooth, h.right_smooth.prodMk k.right_smooth, ?_⟩
  intro j hj
  rw [iteratedFDeriv_prodMk h.left_smooth k.left_smooth (by simp : (j : ℕ∞ω) ≤ ∞),
    iteratedFDeriv_prodMk h.right_smooth k.right_smooth (by simp : (j : ℕ∞ω) ≤ ∞),
    h.jets j hj, k.jets j hj]

theorem FiniteFullJetMatch.fderiv {n : ℕ} {x : E} {f g : E → F}
    (h : FiniteFullJetMatch (n + 1) x f g) :
    FiniteFullJetMatch n x (fderiv ℝ f) (fderiv ℝ g) := by
  refine ⟨h.left_smooth.fderiv_right (by simp),
    h.right_smooth.fderiv_right (by simp), ?_⟩
  intro k hk
  ext v w
  have he := congrArg (fun A : E [×(k + 1)]→L[ℝ] F => A (Fin.snoc v w))
    (h.jets (k + 1) (Nat.add_le_add_right hk 1))
  simpa only [iteratedFDeriv_succ_apply_right, Fin.init_snoc, Fin.snoc_last] using he

end ContinuousFlexibility.Analysis
