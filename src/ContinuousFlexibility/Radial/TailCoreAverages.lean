import ContinuousFlexibility.Radial.TailClosedHighBound

/-!
# Mass averages and admissible Dirichlet walls

A wall is either the tail endpoint or one of its nodes. Every mass cell then
lies wholly before or after the wall. Compact core vectors have nonzero mass
averages in only finitely many cells; this makes their low-mode projections
finite sums of smooth hats.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

def TailAdmissibleCut (T : DeepTailData) (c : ℝ) : Prop :=
  c = T.endpoint ∨ ∃ m : ℕ, c = T.node (m + 1)

theorem tailAdmissibleCut_le_endpoint {T : DeepTailData} (hT : DeepTailHypotheses T)
    {c : ℝ} (hc : TailAdmissibleCut T c) : c ≤ T.endpoint := by
  rcases hc with rfl | ⟨m, rfl⟩
  · exact le_rfl
  · exact (deepTail_node_lt_endpoint hT (m + 1)).le

theorem tailAdmissibleCut_entrance_lt {T : DeepTailData} (hT : DeepTailHypotheses T)
    {c : ℝ} (hc : TailAdmissibleCut T c) : T.entrance < c := by
  rcases hc with rfl | ⟨m, rfl⟩
  · exact hT.1
  · exact deepTail_entrance_lt_succ_node hT m

theorem tailAdmissibleCut_cell_dichotomy {T : DeepTailData}
    (hT : DeepTailHypotheses T) {c : ℝ} (hc : TailAdmissibleCut T c) (n : ℕ) :
    T.node (n + 1) ≤ c ∨ c ≤ T.node n := by
  rcases hc with rfl | ⟨m, rfl⟩
  · exact Or.inl (deepTail_node_lt_endpoint hT (n + 1)).le
  · by_cases hnm : n ≤ m
    · exact Or.inl ((deepTail_node_strictMono hT).monotone (Nat.add_le_add_right hnm 1))
    · exact Or.inr ((deepTail_node_strictMono hT).monotone (Nat.succ_le_of_lt (lt_of_not_ge hnm)))

theorem tail_mass_average_zero_after_cut {T : DeepTailData} {c : ℝ}
    {p : DeepTailL2 T × DeepTailL2 T} (hp : p ∈ TailFormLift T c)
    (n : ℕ) (hn : c ≤ T.node n) :
    (∫ x in tailMassCell T n, p.1 x ∂deepTailMeasure T) = 0 := by
  calc
    _ = ∫ _ in tailMassCell T n, (0 : ℝ) ∂deepTailMeasure T := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae (tailFormLift_ae_zero_outside hp).1,
        ae_restrict_mem (tailMassCell_measurable T n)] with x hz hx
      exact hz (fun hc => (not_lt_of_ge (hn.trans hx.1.le)) hc.2)
    _ = 0 := integral_zero _ _

theorem tailForm_pair_mem (T : DeepTailData) (c : ℝ)
    (u : tailGradientSpace T c) :
    (tailFormBase T c u, tailFormGradient T c u) ∈ TailFormLift T c := by
  have h := (mem_tailGradientSpace T c _).mp u.property
  have he : (tailFormBase T c u, tailFormGradient T c u) =
      WithLp.ofLp (u : GradientHilbert (DeepTailL2 T)) := by
    rw [tailFormBase_apply, tailFormGradient_apply]
    exact Prod.ext (WithLp.ofLp_fst _).symm (WithLp.ofLp_snd _).symm
  rwa [he]

theorem tailForm_mass_average_zero_after_cut {T : DeepTailData} {c : ℝ}
    (u : tailGradientSpace T c) (n : ℕ) (hn : c ≤ T.node n) :
    (∫ x in tailMassCell T n, (tailFormBase T c u) x ∂deepTailMeasure T) = 0 :=
  tail_mass_average_zero_after_cut (tailForm_pair_mem T c u) n hn

/-- Compact containment of the smooth core makes its mass coefficients
eventually zero, including when the original wall is the endpoint. -/
theorem tailGradientCore_mass_averages_eventually_zero {T : DeepTailData}
    (hT : DeepTailHypotheses T) {c : ℝ} (hc : c ≤ T.endpoint)
    {u : tailGradientSpace T c} (hu : u ∈ tailGradientCore T c) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (∫ x in tailMassCell T n, (tailFormBase T c u) x ∂deepTailMeasure T) = 0 := by
  have hcore : (tailFormBase T c u, tailFormGradient T c u) ∈
      TailEnergyCore T T.endpoint := tailEnergyCore_mono T hc hu
  obtain ⟨m, hm⟩ := tailEnergyCore_mem_some_truncation hT hcore
  refine ⟨m + 1, fun n hn => ?_⟩
  exact tail_mass_average_zero_after_cut (subset_closure hm) n
    ((deepTail_node_strictMono hT).monotone hn)

end ContinuousFlexibility.Radial
