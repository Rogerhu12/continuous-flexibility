module

public import ContinuousFlexibility.Analysis.RootInverseNormalizedBounds
public import ContinuousFlexibility.Analysis.PointwiseAffineMaterialJets

/-! Unit-cost normalization of the genuine root-coordinate jets. The
closed radial face is recovered from the same smooth jet by continuity. -/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

/-- Only positive physical fibers enter the quantitative hypothesis.
The global smooth function supplies its genuine limiting jets at zero. -/
theorem n04NegativeChart_rootNormalized_csBound
    {g : N04FlowPoint → ℝ} (hg : ContDiff ℝ ∞ g)
    {τ M : ℝ} (hτ : |τ| ≤ 1) (s : ℕ)
    (hraw : ∀ j, j ≤ s → ∀ q : N04FlowPoint,
      q.1 ∈ n04FlowParameterBox → 0 < q.1.1 →
        ‖iteratedFDeriv ℝ j g q‖ ≤ M) :
    CSBound s (Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 ×ˢ (univ : Set ℝ))
      (g ∘ rootFlowNormalizedArgument τ) M := by
  intro j hj q hq
  let L := rootFlowNormalizedArgument τ
  have hL : ‖L‖ ^ j ≤ 1 :=
    pow_le_one₀ (norm_nonneg _) (rootFlowNormalizedArgument_norm hτ)
  have hopen (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) 1) :
      ‖iteratedFDeriv ℝ j (g ∘ L) (r, q.2)‖ ≤ M := by
    have hbox : (L (r, q.2)).1 ∈ n04FlowParameterBox := by
      rw [rootFlowNormalizedArgument_apply]
      refine ⟨⟨by linarith only [hr.1], hr.2.le⟩, ?_⟩
      apply abs_le.mp
      rw [abs_mul]
      exact (mul_le_mul hτ (abs_le.mpr hq.2.1) (abs_nonneg _) zero_le_one).trans_eq
        (one_mul 1)
    have hb := norm_iteratedFDeriv_comp_linear_le_at (x := (r, q.2)) L hg.contDiffAt j
    exact (hb.trans ((mul_le_mul_of_nonneg_left hL (norm_nonneg _)).trans_eq
      (mul_one _))).trans (hraw j hj _ hbox hr.1)
  have hs := hg.comp L.contDiff
  exact le_on_closure hopen
    ((((hs.continuous_iteratedFDeriv (by simp : (j : ℕ∞ω) ≤ ∞)).comp
      (continuous_id.prodMk continuous_const)).norm).continuousOn)
    continuousOn_const (by simpa only [closure_Ioo zero_lt_one.ne] using hq.1)

end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.n04NegativeChart_rootNormalized_csBound'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.n04NegativeChart_rootNormalized_csBound
