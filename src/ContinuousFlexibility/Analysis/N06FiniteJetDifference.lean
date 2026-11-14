module

public import ContinuousFlexibility.Analysis.OneHighCompositionJets
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Differences of actual finite composition jets

These estimates use the actual Fréchet derivatives and the existing ordered
partition chain rule. They retain one explicit factor measuring the input
difference, with constants fixed before the two input functions are chosen.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped ContDiff BigOperators

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem n06_iteratedFDeriv_difference_le_segment
    {Φ : F → G} {x y : F} (n : ℕ) {C : ℝ}
    (hΦ : ∀ z ∈ segment ℝ x y, ContDiffAt ℝ ∞ Φ z)
    (hbound : ∀ z ∈ segment ℝ x y, ‖iteratedFDeriv ℝ (n + 1) Φ z‖ ≤ C) :
    ‖iteratedFDeriv ℝ n Φ y - iteratedFDeriv ℝ n Φ x‖ ≤ C * ‖y - x‖ := by
  apply (convex_segment x y).norm_image_sub_le_of_norm_fderiv_le
    (fun z hz => (hΦ z hz).differentiableAt_iteratedFDeriv (m := n)
      (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top n)))
    (fun z hz => by simpa only [norm_fderiv_iteratedFDeriv] using hbound z hz)
    (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)

def n06CompositionDifferenceCost (n : ℕ) (C M : ℝ) : ℝ :=
  ∑ c : OrderedFinpartition n,
    C * ((c.length : ℝ) * M ^ (c.length - 1) + M ^ c.length)

theorem n06CompositionDifferenceCost_nonneg (n : ℕ) {C M : ℝ}
    (hC : 0 ≤ C) (hM : 0 ≤ M) : 0 ≤ n06CompositionDifferenceCost n C M := by
  exact Finset.sum_nonneg fun c _ => mul_nonneg hC
    (add_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hM _)) (pow_nonneg hM _))

/-- A fixed-order composition is Lipschitz in its actual input jet whenever
the outer jets have the corresponding value and difference bounds. -/
theorem n06_iteratedFDeriv_comp_difference_le
    {Φ : F → G} {u v : E → F} {x : E} (n : ℕ)
    (hΦu : ContDiffAt ℝ ∞ Φ (u x)) (hΦv : ContDiffAt ℝ ∞ Φ (v x))
    (hu : ContDiffAt ℝ ∞ u x) (hv : ContDiffAt ℝ ∞ v x)
    {C M δ : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M) (hδ : 0 ≤ δ)
    (houter : ∀ k, k ≤ n → ‖iteratedFDeriv ℝ k Φ (u x)‖ ≤ C)
    (houterDiff : ∀ k, k ≤ n →
      ‖iteratedFDeriv ℝ k Φ (u x) - iteratedFDeriv ℝ k Φ (v x)‖ ≤ C * δ)
    (hinputU : ∀ k, k ≤ n → ‖iteratedFDeriv ℝ k u x‖ ≤ M)
    (hinputV : ∀ k, k ≤ n → ‖iteratedFDeriv ℝ k v x‖ ≤ M)
    (hinputDiff : ∀ k, k ≤ n →
      ‖iteratedFDeriv ℝ k u x - iteratedFDeriv ℝ k v x‖ ≤ δ) :
    ‖iteratedFDeriv ℝ n (Φ ∘ u) x - iteratedFDeriv ℝ n (Φ ∘ v) x‖ ≤
      n06CompositionDifferenceCost n C M * δ := by
  classical
  have hcompU : iteratedFDeriv ℝ n (Φ ∘ u) x =
      ∑ c : OrderedFinpartition n,
        c.compAlongOrderedFinpartition (iteratedFDeriv ℝ c.length Φ (u x))
          (fun j => iteratedFDeriv ℝ (c.partSize j) u x) :=
    iteratedFDeriv_comp hΦu hu (by simp : (n : ℕ∞ω) ≤ ∞)
  have hcompV : iteratedFDeriv ℝ n (Φ ∘ v) x =
      ∑ c : OrderedFinpartition n,
        c.compAlongOrderedFinpartition (iteratedFDeriv ℝ c.length Φ (v x))
          (fun j => iteratedFDeriv ℝ (c.partSize j) v x) :=
    iteratedFDeriv_comp hΦv hv (by simp : (n : ℕ∞ω) ≤ ∞)
  rw [hcompU, hcompV, ← Finset.sum_sub_distrib,
    n06CompositionDifferenceCost, Finset.sum_mul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro c _
  let U := fun j : Fin c.length => iteratedFDeriv ℝ (c.partSize j) u x
  let V := fun j : Fin c.length => iteratedFDeriv ℝ (c.partSize j) v x
  have hU : ‖U‖ ≤ M := (pi_norm_le_iff_of_nonneg hM).mpr fun j =>
    hinputU (c.partSize j) (c.partSize_le j)
  have hV : ‖V‖ ≤ M := (pi_norm_le_iff_of_nonneg hM).mpr fun j =>
    hinputV (c.partSize j) (c.partSize_le j)
  have hUV : ‖U - V‖ ≤ δ := (pi_norm_le_iff_of_nonneg hδ).mpr fun j =>
    hinputDiff (c.partSize j) (c.partSize_le j)
  have hmax : max ‖U‖ ‖V‖ ≤ M := max_le hU hV
  have hprod : (∏ j, ‖V j‖) ≤ M ^ c.length := by
    calc
      _ ≤ ∏ _j : Fin c.length, M :=
        Finset.prod_le_prod₀ (fun j _ => norm_nonneg _) (fun j _ =>
          hinputV (c.partSize j) (c.partSize_le j))
      _ = M ^ c.length := by simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  apply (c.norm_compAlongOrderedFinpartition_sub_compAlongOrderedFinpartition_le
    (iteratedFDeriv ℝ c.length Φ (u x)) (iteratedFDeriv ℝ c.length Φ (v x)) U V).trans
  calc
    _ ≤ C * (c.length : ℝ) * M ^ (c.length - 1) * δ +
        (C * δ) * M ^ c.length := by
      gcongr <;> first
      | exact houter c.length c.length_le
      | exact hmax
      | exact hUV
      | exact houterDiff c.length c.length_le
      | exact hprod
    _ = C * ((c.length : ℝ) * M ^ (c.length - 1) + M ^ c.length) * δ := by ring

end ContinuousFlexibility.Analysis
