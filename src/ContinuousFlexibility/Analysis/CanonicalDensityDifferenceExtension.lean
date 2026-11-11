import ContinuousFlexibility.Analysis.CanonicalDensityExtension

/-!
# Subtracting the two actual canonical endpoint extensions

Current and reference coordinates may use different physical boundary
angles. Once their genuine local extensions are centered at the same
canonical point, the common normal form cancels. Only finite vanishing
orders are needed, and smoothness is retained on the smaller actual ball.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-- The common-center condition is explicit. Each input extension and
its zero jets are supplied by the preceding physical-to-canonical
construction, rather than by values of a totalized boundary inverse. -/
theorem canonicalDensityDifference_extension
    {E Eref ρ ρref : PolarPoint → ℝ} {N : ℝ → ℝ}
    {q : PolarPoint} {δ δref : ℝ} {U : Set PolarPoint} {n : ℕ}
    (hδ : 0 < δ) (hδref : 0 < δref)
    (hE : ContDiffOn ℝ ∞ E (Metric.ball q δ))
    (hEref : ContDiffOn ℝ ∞ Eref (Metric.ball q δref))
    (heq : EqOn E (fun p => ρ p - N p.1) (Metric.ball q δ ∩ U))
    (heqref : EqOn Eref (fun p => ρref p - N p.1) (Metric.ball q δref ∩ U))
    (hzero : ∀ k ≤ n, iteratedDeriv k (fun r => E (r, q.2)) q.1 = 0)
    (hzeroref : ∀ k ≤ n, iteratedDeriv k (fun r => Eref (r, q.2)) q.1 = 0) :
    0 < min δ δref ∧
      ContDiffOn ℝ ∞ (fun p => E p - Eref p) (Metric.ball q (min δ δref)) ∧
      EqOn (fun p => E p - Eref p) (fun p => ρ p - ρref p)
        (Metric.ball q (min δ δref) ∩ U) ∧
      ∀ k ≤ n, iteratedDeriv k (fun r => E (r, q.2) - Eref (r, q.2)) q.1 = 0 := by
  have hball : Metric.ball q (min δ δref) ⊆ Metric.ball q δ :=
    Metric.ball_subset_ball (min_le_left _ _)
  have hballref : Metric.ball q (min δ δref) ⊆ Metric.ball q δref :=
    Metric.ball_subset_ball (min_le_right _ _)
  refine ⟨lt_min hδ hδref, (hE.mono hball).sub (hEref.mono hballref), ?_, ?_⟩
  · intro p hp
    dsimp only
    rw [heq p ⟨hball hp.1, hp.2⟩, heqref p ⟨hballref hp.1, hp.2⟩]
    ring
  · intro k hk
    have hline : ContDiffAt ℝ ∞ (fun r : ℝ => (r, q.2)) q.1 :=
      contDiffAt_id.prodMk contDiffAt_const
    have hEs : ContDiffAt ℝ ∞ (fun r => E (r, q.2)) q.1 :=
      (hE.contDiffAt (Metric.ball_mem_nhds q hδ)).comp q.1 hline
    have hErefs : ContDiffAt ℝ ∞ (fun r => Eref (r, q.2)) q.1 :=
      (hEref.contDiffAt (Metric.ball_mem_nhds q hδref)).comp q.1 hline
    rw [iteratedDeriv_fun_sub
      (hEs.of_le (show (k : ℕ∞ω) ≤ ∞ by simp))
      (hErefs.of_le (show (k : ℕ∞ω) ≤ ∞ by simp)),
      hzero k hk, hzeroref k hk, sub_self]

end ContinuousFlexibility.Analysis

