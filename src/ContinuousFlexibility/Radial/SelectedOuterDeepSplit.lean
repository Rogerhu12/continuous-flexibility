import ContinuousFlexibility.Radial.R07DeepTailPhysical
import ContinuousFlexibility.Radial.R07DeepTailEntry

/-!
# An actual deep split beyond a fixed selected matching cut

The matching cut stays at the selected join. For each fixed frequency we
may put the auxiliary deep entrance arbitrarily far out. The intervening
closed interval is a compact subset of the actual core, and the remaining
tail has the complete R06 hypotheses and physical identification. One
depth works for both orientations and for every admissible height sequence.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real
open ContinuousFlexibility.Statements

/-- Physical radius of the auxiliary deep entrance, with the left initial
resistance interval included exactly as in the R07 construction. -/
def selectedOuterDeepEntrance (S : SelectedTailData) (right : Bool) (start : ℕ) : ℝ :=
  if right then r07MassNodeRadius S.chain right start
    else morseChainResistanceEnd S.chain right start

/-- Actual data for splitting one selected outer region. In particular the
order and core conditions are conclusions, not additional geometric inputs. -/
structure SelectedOuterDeepSplitData (S : SelectedTailData) (n j start : ℕ)
    (η K : ℝ) (right : Bool) : Prop where
  join_core : S.joinInner right n ∈ radialCore (S.family S.sigma)
  entrance_core : selectedOuterDeepEntrance S right start ∈ radialCore (S.family S.sigma)
  after_entry : if right then S.entry right n < selectedOuterDeepEntrance S right start
    else selectedOuterDeepEntrance S right start < S.entry right n
  after_join : if right then S.joinInner right n < selectedOuterDeepEntrance S right start
    else selectedOuterDeepEntrance S right start < S.joinInner right n
  core_span : uIcc (S.joinInner right n) (selectedOuterDeepEntrance S right start) ⊆
    radialCore (S.family S.sigma)
  tail_subset : radialTailInterval (S.family S.sigma) right
      (selectedOuterDeepEntrance S right start) ⊆
    radialTailInterval (S.family S.sigma) right (S.joinInner right n)
  outward_order :
    r07OutwardSign right * S.joinInner right n <
        r07OutwardSign right * selectedOuterDeepEntrance S right start ∧
      r07OutwardSign right * selectedOuterDeepEntrance S right start <
        r07OutwardSign right * (if right then (S.family S.sigma).b
          else (S.family S.sigma).a)
  entrance_radius : tailPhysicalRadius right
      (r07DeepTailData S.chain (S.family S.sigma) right j start η K).entrance =
    selectedOuterDeepEntrance S right start
  hypotheses : DeepTailHypotheses
    (r07DeepTailData S.chain (S.family S.sigma) right j start η K)
  physical : TailPhysicalRelation (S.family S.sigma)
    (r07DeepTailData S.chain (S.family S.sigma) right j start η K) right j start

/-- A common arbitrarily deep split for the two actual selected outer
regions. The stronger uniform physical conclusion is retained, so the
choice of auxiliary depth does not depend on the selected height sequence.
There is no restriction on whether the active band is the first band. -/
theorem exists_selected_outer_deep_split {S : SelectedTailData}
    (hS : IsSelectedTail S) (G : MorseChainGeometryWitness S.chain)
    (hends : ∀ sigma tau, (S.family sigma).a = (S.family tau).a ∧
      (S.family sigma).b = (S.family tau).b)
    {n j : ℕ} (hj : 2 ≤ j) (heven : Even j)
    (hband : radialFrequencyBand S.chain S.Cstar n j)
    {η K : ℝ} (hη : 0 < η) (hη1 : η < 1) (hK : 1 < K) (minimum : ℕ) :
    ∃ start : ℕ, minimum ≤ start ∧ n + 2 ≤ start ∧ S.chain.index < start ∧
      32 ≤ start ∧
      (∀ sigma, (∀ k, 1 ≤ sigma k ∧ sigma k ≤ 2) → ∀ right : Bool,
        DeepTailHypotheses (r07DeepTailData S.chain (S.family sigma) right j start η K) ∧
          TailPhysicalRelation (S.family sigma)
            (r07DeepTailData S.chain (S.family sigma) right j start η K) right j start) ∧
      ∀ right : Bool, SelectedOuterDeepSplitData S n j start η K right := by
  obtain ⟨start, hmin, hstart, h32, hdeep⟩ :=
    r07_exists_uniform_deepTailPhysical S.chain S.constants S.family
      hS.2.2.2.1 hends hj hη hη1 hK (max minimum (n + 2))
  have htwo : n + 2 ≤ start := (le_max_right minimum (n + 2)).trans hmin
  have hreal : MorseChainRealization S.chain S.sigma (S.family S.sigma) S.constants :=
    (hS.2.2.2.1 S.sigma hS.2.2.1).1
  refine ⟨start, (le_max_left minimum (n + 2)).trans hmin, htwo,
    hstart, h32, hdeep, ?_⟩
  intro right
  let e := selectedOuterDeepEntrance S right start
  have he : e ∈ radialCore (S.family S.sigma) :=
    r07_deepPhysicalEntrance_core hreal right hstart
  rcases hS.2.2.2.2.2 right n j hj heven hband with
    ⟨_, _, hp, _, horder, hentry, _, _, _, _, _, _, _⟩
  have hentry' : S.entry right n = r07CellEntry S.chain right n := hentry
  have hafter : if right then S.entry right n < e else e < S.entry right n := by
    rw [hentry']
    exact r07_deepPhysicalEntrance_after_entry G hreal right hband.1 htwo
  have hjoin : if right then S.joinInner right n < e else e < S.joinInner right n := by
    cases right
    · exact hafter.trans horder.1
    · exact horder.2.trans hafter
  have hspan : uIcc (S.joinInner right n) e ⊆ radialCore (S.family S.sigma) := by
    intro r hr
    cases right
    · rw [uIcc_of_ge hjoin.le] at hr
      exact ⟨he.1.trans_le hr.1, hr.2.trans_lt hp.2⟩
    · rw [uIcc_of_le hjoin.le] at hr
      exact ⟨hp.1.trans_le hr.1, hr.2.trans_lt he.2⟩
  refine {
    join_core := hp
    entrance_core := he
    after_entry := hafter
    after_join := hjoin
    core_span := hspan
    tail_subset := ?_
    outward_order := ?_
    entrance_radius := ?_
    hypotheses := (hdeep S.sigma hS.2.2.1 right).1
    physical := (hdeep S.sigma hS.2.2.1 right).2 }
  · intro r hr
    cases right
    · exact ⟨hr.1, hr.2.trans hjoin⟩
    · exact ⟨hjoin.trans hr.1, hr.2⟩
  · cases right
    · simp only [r07OutwardSign, Bool.false_eq_true, ite_false, neg_one_mul]
      exact ⟨neg_lt_neg hjoin, neg_lt_neg he.1⟩
    · simp only [r07OutwardSign, ite_true, one_mul]
      exact ⟨hjoin, he.2⟩
  · change tailPhysicalRadius right (r07OutwardLog right e) = e
    exact r07_radius_outwardLog right ((r07_realization_geometry hreal).1.trans he.1)

end ContinuousFlexibility.Radial
