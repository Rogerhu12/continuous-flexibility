import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# Actual derivatives in the Hilbert sum of circle components

A summable bound on component derivatives justifies differentiation in
the original Hilbert sum. The proof differentiates the canonical series
of single-component vectors.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped ENNReal Topology

theorem coupled_hasDerivAt_lp_of_summable_bound
    {ι : Type*} [DecidableEq ι] {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    [∀ i, CompleteSpace (E i)]
    {f df : ℝ → lp E 2} {t₀ δ : ℝ} (hδ : 0 < δ)
    {g : ι → ℝ} (hg : Summable g)
    (hderiv : ∀ i t, t ∈ Ioo (t₀ - δ) (t₀ + δ) →
      HasDerivAt (fun s => f s i) (df t i) t)
    (hbound : ∀ i t, t ∈ Ioo (t₀ - δ) (t₀ + δ) → ‖df t i‖ ≤ g i) :
    HasDerivAt f (df t₀) t₀ := by
  have h₀ : t₀ ∈ Ioo (t₀ - δ) (t₀ + δ) := ⟨by linarith, by linarith⟩
  have hs (t : ℝ) : (∑' i, lp.single 2 i (f t i)) = f t :=
    (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) (f t)).tsum_eq
  have hds : (∑' i, lp.single 2 i (df t₀ i)) = df t₀ :=
    (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) (df t₀)).tsum_eq
  have h := hasDerivAt_tsum_of_isPreconnected
    (t := Ioo (t₀ - δ) (t₀ + δ))
    (g := fun i t => lp.single 2 i (f t i))
    (g' := fun i t => lp.single 2 i (df t i)) (y₀ := t₀)
    hg isOpen_Ioo (convex_Ioo _ _).isPreconnected
    (fun i t ht => by
      simpa only [Function.comp_def, lp.singleContinuousLinearMap_apply] using
        (lp.singleContinuousLinearMap ℝ E 2 i).hasFDerivAt.comp_hasDerivAt t
          (hderiv i t ht))
    (fun i t ht => by
      rw [lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]
      exact hbound i t ht)
    h₀ (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) (f t₀)).summable h₀
  simpa only [hs, hds] using h

end ContinuousFlexibility.Analysis
