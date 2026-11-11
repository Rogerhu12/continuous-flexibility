import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Finite radial jets under actual smooth operations

Equality of actual derivatives through a finite order is preserved by
smooth composition. The inner curves may be vector-valued. The proof is
a direct consequence of Mathlib's Faà di Bruno formula, whose partition
blocks never use a derivative above the requested order.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

/-- A common smooth outer function preserves equality of the finite
actual jets of two curves, with no extra derivative loss. -/
theorem iteratedDeriv_vcomp_eq_of_finiteJet_eq
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f g : ℝ → E} {H : E → F} {x : ℝ} {n k : ℕ}
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x)
    (hH : ContDiffAt ℝ ∞ H (f x))
    (hjet : ∀ j ≤ n, iteratedDeriv j f x = iteratedDeriv j g x)
    (hk : k ≤ n) :
    iteratedDeriv k (H ∘ f) x = iteratedDeriv k (H ∘ g) x := by
  have h0 : f x = g x := by
    simpa only [iteratedDeriv_zero] using hjet 0 (Nat.zero_le n)
  have hHg : ContDiffAt ℝ ∞ H (g x) := h0 ▸ hH
  rw [iteratedDeriv_vcomp_eq_sum_orderedFinpartition (i := k) hH hf (by simp),
    iteratedDeriv_vcomp_eq_sum_orderedFinpartition (i := k) hHg hg (by simp)]
  apply Finset.sum_congr rfl
  intro c _
  rw [h0]
  congr 1
  funext j
  exact hjet (c.partSize j) ((c.partSize_le j).trans hk)

/-- Multiplication by a common smooth scalar function preserves the same
finite radial jet. -/
theorem iteratedDeriv_mul_left_eq_of_finiteJet_eq
    {f g H : ℝ → ℝ} {x : ℝ} {n k : ℕ}
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x)
    (hH : ContDiffAt ℝ ∞ H x)
    (hjet : ∀ j ≤ n, iteratedDeriv j f x = iteratedDeriv j g x)
    (hk : k ≤ n) :
    iteratedDeriv k (fun r => H r * f r) x =
      iteratedDeriv k (fun r => H r * g r) x := by
  rw [iteratedDeriv_fun_mul
      (hH.of_le (show (k : ℕ∞ω) ≤ ∞ by simp))
      (hf.of_le (show (k : ℕ∞ω) ≤ ∞ by simp)),
    iteratedDeriv_fun_mul
      (hH.of_le (show (k : ℕ∞ω) ≤ ∞ by simp))
      (hg.of_le (show (k : ℕ∞ω) ≤ ∞ by simp))]
  apply Finset.sum_congr rfl
  intro i _
  rw [hjet (k - i) ((Nat.sub_le k i).trans hk)]

end ContinuousFlexibility.Analysis
