import ContinuousFlexibility.Radial.MorseRealizationBasic

/-!
# A fixed seam window for the initial localizer labels

The distance bound for the actual cells separates every localizer of a
bounded label from both endpoints by one positive distance. The actual
seam limits then give a fixed enclosing window. Its choice precedes all
later frequency and retained-length choices.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter Real ContinuousFlexibility.Statements
open scoped Topology

theorem accumulating_initial_localizers_separated {D : ReferenceData} {C : ℕ → ℝ}
    (h : AccumulatingProfileBounds D C) (N : ℕ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ m : ℕ, D.cellIndex m ≤ N → ∀ r : ℝ,
      D.localizer m r ≠ 0 → D.a + δ ≤ r ∧ r ≤ D.b - δ := by
  rcases h with ⟨_, hP, hC, _, _, _, hdist, _⟩
  let δ : ℝ := (C 0)⁻¹ * exp (-((N : ℝ) + 1) ^ 2)
  have hδ : 0 < δ := mul_pos (inv_pos.mpr (hC 0)) (exp_pos _)
  refine ⟨δ, hδ, ?_⟩
  intro m hm r hr
  have hcell : r ∈ D.cells m := hP.2.2.1 m hr
  have hm' : (D.cellIndex m : ℝ) ≤ N := by exact_mod_cast hm
  have hsq : ((D.cellIndex m : ℝ) + 1) ^ 2 ≤ ((N : ℝ) + 1) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (add_le_add hm' le_rfl) 2
  have hcoef : δ ≤
      (C 0)⁻¹ * exp (-((D.cellIndex m : ℝ) + 1) ^ 2) :=
    mul_le_mul_of_nonneg_left (exp_le_exp.mpr (neg_le_neg hsq)) (inv_nonneg.mpr (hC 0).le)
  have hmin := le_min_iff.mp (hcoef.trans (hdist m r hcell).1)
  constructor <;> linarith only [hmin.1, hmin.2]

theorem matchedMorse_seam_tendsto {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ}
    (h : MorseChainRealization T σ D C) (side : Bool) :
    Tendsto (morseChainSeam T side) atTop (𝓝 (if side then D.b else D.a)) := by
  obtain ⟨_, _, _, _, _, _, hlimits, _, _, _⟩ := h
  cases side with
  | false =>
      change Tendsto (fun n => T.radius false n (T.rightX false n)) atTop (𝓝 D.a)
      exact (hlimits false).2
  | true =>
      change Tendsto (fun n => T.radius true n (T.leftX true n)) atTop (𝓝 D.b)
      exact (hlimits true).1

/-- The window is shared by every nonzero actual localizer whose
original label is at most N. No final cell saturation is involved. -/
theorem exists_matchedMorse_initial_localizer_window {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ}
    (h : MorseChainRealization T σ D C) (N : ℕ) :
    ∃ J : ℕ, N ≤ J ∧ T.index ≤ J ∧
      ∀ m : ℕ, D.cellIndex m ≤ N → ∀ r : ℝ, D.localizer m r ≠ 0 →
        r ∈ Icc (morseChainSeam T false J) (morseChainSeam T true J) := by
  obtain ⟨δ, hδ, hsep⟩ := accumulating_initial_localizers_separated h.accumulating N
  have hL : Tendsto (morseChainSeam T false) atTop (𝓝 D.a) := by
    simpa only [Bool.false_eq_true, ite_false] using matchedMorse_seam_tendsto h false
  have hR : Tendsto (morseChainSeam T true) atTop (𝓝 D.b) := by
    simpa only [ite_true] using matchedMorse_seam_tendsto h true
  have hleft : ∀ᶠ J in atTop, morseChainSeam T false J < D.a + δ :=
    hL.eventually (gt_mem_nhds (by linarith only [hδ]))
  have hright : ∀ᶠ J in atTop, D.b - δ < morseChainSeam T true J :=
    hR.eventually (lt_mem_nhds (by linarith only [hδ]))
  obtain ⟨J, hJ, hJL, hJR⟩ :=
    ((eventually_ge_atTop (max N T.index)).and (hleft.and hright)).exists
  refine ⟨J, (le_max_left _ _).trans hJ, (le_max_right _ _).trans hJ, ?_⟩
  intro m hm r hr
  have hs := hsep m hm r hr
  exact ⟨(hJL.trans_le hs.1).le, (hs.2.trans_lt hJR).le⟩

end ContinuousFlexibility.Radial
