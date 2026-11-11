import ContinuousFlexibility.Radial.R07DeepTailChange
import ContinuousFlexibility.Radial.MorseCellMassTravel

/-!
# The actual deep-tail data attached to a realized Morse chain

The outward mass interval at the left endpoint runs from the right turning
point to the left model cut.  Its following resistance interval is the
original interval with the *next* index.  The initial resistance interval is
the original interval with index `start`.  On the right the original order
is already outward and no initial interval is inserted.

All fields below are explicit functions of the given realized chain and its
physical profile.  The geometric and integral lemmas do not assert the
smallness or large-product estimates of `DeepTailHypotheses`.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory Real
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

def r07MassNodeRadius (T : MorseChainData) (right : Bool) (n : ℕ) : ℝ :=
  if right then T.radius right n (T.leftX right n) else morseChainMassEnd T right n

def r07MassExitRadius (T : MorseChainData) (right : Bool) (n : ℕ) : ℝ :=
  if right then morseChainMassEnd T right n else T.radius right n (T.leftX right n)

/-- The chain in the outward logarithmic coordinate.  A left starting index
strictly beyond the original index retains the complete initial resistance
interval, including the preceding join. -/
def r07DeepTailData (T : MorseChainData) (D : ReferenceData) (right : Bool)
    (j start : ℕ) (η K : ℝ) : DeepTailData where
  entrance := r07OutwardLog right
    (if right then r07MassNodeRadius T right start else morseChainResistanceEnd T right start)
  endpoint := r07OutwardLog right (if right then D.b else D.a)
  p := r07PhysicalDensity D right j
  node := fun n => r07OutwardLog right (r07MassNodeRadius T right (start + n))
  massEnd := fun n => r07OutwardLog right (r07MassExitRadius T right (start + n))
  Λ := (j : ℝ) ^ 2 * ((j : ℝ) ^ 2 - 1)
  η := η
  K := K

theorem r07_realization_accumulating {T : MorseChainData} {D : ReferenceData}
    {σ C : ℕ → ℝ} (h : MorseChainRealization T σ D C) : IsAccumulatingProfile D := by
  rcases h with ⟨_, _, _, _, _, _, _, _, _, hC⟩
  exact ⟨C, hC⟩

theorem r07_realization_geometry {T : MorseChainData} {D : ReferenceData}
    {σ C : ℕ → ℝ} (h : MorseChainRealization T σ D C) : RadialProfileGeometry D := by
  obtain ⟨_, hC⟩ := r07_realization_accumulating h
  exact hC.1

theorem r07_chain_radius_mem_core {T : MorseChainData} {D : ReferenceData}
    {σ C : ℕ → ℝ} (h : MorseChainRealization T σ D C)
    (right : Bool) {n : ℕ} (hn : T.index ≤ n) {x : ℝ}
    (hx : x ∈ Icc (T.leftX right n) (T.rightX right n)) :
    T.radius right n x ∈ radialCore D :=
  h.2.2.2.2.1 right n hn ⟨x, hx, rfl⟩

theorem r07_chain_model_cuts {T : MorseChainData} {D : ReferenceData}
    {σ C : ℕ → ℝ} (h : MorseChainRealization T σ D C)
    (right : Bool) {n : ℕ} (hn : T.index ≤ n) :
    T.radius right n (T.leftX right n) < morseChainMassEnd T right n ∧
      morseChainMassEnd T right n < T.radius right n (T.rightX right n) := by
  have hG := h.2.1 right n hn
  have hL : T.leftX right n < morseChainRightTurn T n := hG.2.2.2.1
  have hR : morseChainRightTurn T n < T.rightX right n := hG.2.2.2.2.1
  have hr := h.2.2.1 right n hn
  have hmono : StrictMonoOn (T.radius right n) (Icc (T.leftX right n) (T.rightX right n)) :=
    morseCell_strictMonoOn hr.1 (fun x hx => (hr.2.2 x hx).1)
  exact ⟨hmono ⟨le_rfl, hL.le.trans hR.le⟩ ⟨hL.le, hR.le⟩ hL,
    hmono ⟨hL.le, hR.le⟩ ⟨hL.le.trans hR.le, le_rfl⟩ hR⟩

theorem r07_chain_mass_cuts_core {T : MorseChainData} {D : ReferenceData}
    {σ C : ℕ → ℝ} (h : MorseChainRealization T σ D C)
    (right : Bool) {n : ℕ} (hn : T.index ≤ n) :
    T.radius right n (T.leftX right n) ∈ radialCore D ∧
      morseChainMassEnd T right n ∈ radialCore D ∧
      T.radius right n (T.rightX right n) ∈ radialCore D := by
  have hG := h.2.1 right n hn
  have hL : T.leftX right n < morseChainRightTurn T n := hG.2.2.2.1
  have hR : morseChainRightTurn T n < T.rightX right n := hG.2.2.2.2.1
  exact ⟨r07_chain_radius_mem_core h right hn ⟨le_rfl, hL.le.trans hR.le⟩,
    r07_chain_radius_mem_core h right hn ⟨hL.le, hR.le⟩,
    r07_chain_radius_mem_core h right hn ⟨hL.le.trans hR.le, le_rfl⟩⟩

theorem r07_chain_mass_nodes_core {T : MorseChainData} {D : ReferenceData}
    {σ C : ℕ → ℝ} (h : MorseChainRealization T σ D C)
    (right : Bool) {n : ℕ} (hn : T.index ≤ n) :
    r07MassNodeRadius T right n ∈ radialCore D ∧
      r07MassExitRadius T right n ∈ radialCore D := by
  have hc := r07_chain_mass_cuts_core h right hn
  cases right
  · exact ⟨hc.2.1, hc.1⟩
  · exact ⟨hc.1, hc.2.1⟩

/-- The right resistance interval ends at the next mass entrance.  On the
left, the interval with index `n+1` ends at the preceding mass exit. -/
theorem r07_chain_resistance_ends {T : MorseChainData} {D : ReferenceData}
    {σ C : ℕ → ℝ} (h : MorseChainRealization T σ D C) {n : ℕ} (hn : T.index ≤ n) :
    morseChainResistanceEnd T true n = T.radius true (n + 1) (T.leftX true (n + 1)) ∧
      morseChainResistanceEnd T false (n + 1) = T.radius false n (T.leftX false n) := by
  have hright := (h.2.2.2.1 true n hn).2.2.1
  have hleft := (h.2.2.2.1 false n hn).2.2.1
  constructor
  · simpa only [morseChainResistanceEnd, if_true] using hright
  · simpa only [morseChainResistanceEnd, Bool.false_eq_true, if_false,
      if_pos (hn.trans_lt (Nat.lt_succ_self n)), Nat.add_sub_cancel] using hleft

theorem r07_chain_resistanceEnd_core {T : MorseChainData} {D : ReferenceData}
    {σ C : ℕ → ℝ} (h : MorseChainRealization T σ D C)
    (right : Bool) {n : ℕ} (hn : T.index < n) :
    morseChainResistanceEnd T right n ∈ radialCore D := by
  cases right
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    rw [(r07_chain_resistance_ends h (by omega : T.index ≤ m)).2]
    exact (r07_chain_mass_cuts_core h false (by omega : T.index ≤ m)).1
  · rw [(r07_chain_resistance_ends h hn.le).1]
    exact (r07_chain_mass_cuts_core h true (hn.le.trans (Nat.le_succ n))).1

theorem r07_radius_mem_log_interval {right : Bool} {a b x : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hx : x ∈ uIcc (r07OutwardLog right a) (r07OutwardLog right b)) :
    tailPhysicalRadius right x ∈ uIcc a b := by
  have hR : Monotone (tailPhysicalRadius right) ∨ Antitone (tailPhysicalRadius right) := by
    cases right
    · exact Or.inr (fun u v huv => exp_le_exp.mpr (neg_le_neg huv))
    · exact Or.inl (fun u v huv => exp_le_exp.mpr huv)
  have hmem := hR.elim (fun h => h.mapsTo_uIcc hx) (fun h => h.mapsTo_uIcc hx)
  simpa only [r07_radius_outwardLog right ha, r07_radius_outwardLog right hb] using hmem

theorem r07_deepTail_entrance_core {T : MorseChainData} {D : ReferenceData}
    {σ C : ℕ → ℝ} (h : MorseChainRealization T σ D C)
    (right : Bool) (j : ℕ) {start : ℕ} (hstart : T.index < start) (η K : ℝ) :
    tailPhysicalRadius right (r07DeepTailData T D right j start η K).entrance ∈ radialCore D := by
  have ha := (r07_realization_geometry h).1
  have hc : (if right then r07MassNodeRadius T right start
      else morseChainResistanceEnd T right start) ∈ radialCore D := by
    cases right
    · exact r07_chain_resistanceEnd_core h false hstart
    · exact (r07_chain_mass_nodes_core h true hstart.le).1
  simpa only [r07DeepTailData, r07_radius_outwardLog right (ha.trans hc.1)] using hc

theorem r07_physical_radius_core_of_Ico {D : ReferenceData} {right : Bool} {entrance x : ℝ}
    (hD : RadialProfileGeometry D)
    (he : tailPhysicalRadius right entrance ∈ radialCore D)
    (hx : x ∈ Ico entrance (r07OutwardLog right (if right then D.b else D.a))) :
    tailPhysicalRadius right x ∈ radialCore D := by
  rcases eq_or_lt_of_le hx.1 with hxe | hxe
  · simpa only [hxe] using he
  · have ht := (r07_radius_mem_tail_iff hD.1 (hD.1.trans hD.2.1) right entrance x).mpr
      ⟨hxe, hx.2⟩
    cases right
    · exact ⟨ht.1, ht.2.trans he.2⟩
    · exact ⟨he.1.trans ht.1, ht.2⟩

/-- The smoothness and positivity clauses of the concrete `DeepTailData`
follow directly from the realized profile. -/
theorem r07_deepTail_density_properties {T : MorseChainData} {D : ReferenceData}
    {σ C : ℕ → ℝ} (h : MorseChainRealization T σ D C)
    (right : Bool) (j : ℕ) {start : ℕ} (hstart : T.index < start) (η K : ℝ) :
    let Q := r07DeepTailData T D right j start η K
    ContDiffOn ℝ ∞ Q.p (Ico Q.entrance Q.endpoint) ∧
      ∀ x ∈ Ico Q.entrance Q.endpoint, 0 < Q.p x := by
  have hD := r07_realization_geometry h
  have he : 0 < (if right then D.b else D.a) := by
    cases right
    · exact hD.1
    · exact hD.1.trans hD.2.1
  refine ⟨(r07_contDiff_physicalDensity right j he hD.2.2.1.1).contDiffOn, ?_⟩
  intro x hx
  apply r07_physicalDensity_pos he
  exact hD.2.2.2.2.1 _ (r07_physical_radius_core_of_Ico hD
    (r07_deepTail_entrance_core h right j hstart η K) hx)

theorem r07_deepTail_lambda_pos {T : MorseChainData} {D : ReferenceData} {right : Bool}
    {j start : ℕ} {η K : ℝ} (hj : 2 ≤ j) :
    0 < (r07DeepTailData T D right j start η K).Λ := by
  have hj' : (2 : ℝ) ≤ j := by exact_mod_cast hj
  change 0 < (j : ℝ) ^ 2 * ((j : ℝ) ^ 2 - 1)
  exact mul_pos (sq_pos_of_pos (by linarith)) (by nlinarith)

theorem r07_chain_join_order {T : MorseChainData} {D : ReferenceData}
    {σ C : ℕ → ℝ} (h : MorseChainRealization T σ D C)
    (right : Bool) {n : ℕ} (hn : T.index ≤ n) :
    (if right then T.radius right n (T.rightX right n)
      else T.radius right (n + 1) (T.rightX right (n + 1))) <
    (if right then T.radius right (n + 1) (T.leftX right (n + 1))
      else T.radius right n (T.leftX right n)) := by
  have hJ := h.2.2.2.1 right n hn
  have ho := hJ.1
  rwa [hJ.2.1, hJ.2.2.1] at ho

theorem r07_chain_massEnd_lt_resistanceEnd {T : MorseChainData} {D : ReferenceData}
    {σ C : ℕ → ℝ} (h : MorseChainRealization T σ D C)
    (right : Bool) {n : ℕ} (hn : T.index < n) :
    morseChainMassEnd T right n < morseChainResistanceEnd T right n := by
  cases right
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    rw [(r07_chain_resistance_ends h (by omega : T.index ≤ m)).2]
    exact (r07_chain_model_cuts h false hn.le).2.trans
      (r07_chain_join_order h false (by omega : T.index ≤ m))
  · rw [(r07_chain_resistance_ends h hn.le).1]
    exact (r07_chain_model_cuts h true hn.le).2.trans (r07_chain_join_order h true hn.le)

theorem r07_deepTail_interval_order {T : MorseChainData} {D : ReferenceData}
    {σ C : ℕ → ℝ} (h : MorseChainRealization T σ D C)
    (right : Bool) (j : ℕ) {start : ℕ} (hstart : T.index < start) (η K : ℝ) (n : ℕ) :
    let Q := r07DeepTailData T D right j start η K
    Q.node n < Q.massEnd n ∧ Q.massEnd n < Q.node (n + 1) := by
  have hn : T.index < start + n := hstart.trans_le (Nat.le_add_right start n)
  have hnext : T.index < start + n + 1 := hn.trans (Nat.lt_succ_self _)
  have hc := r07_chain_mass_cuts_core h right hn.le
  have ha := (r07_realization_geometry h).1
  have hlo := r07_chain_model_cuts h right hn.le
  cases right
  · have hg := r07_chain_massEnd_lt_resistanceEnd h false hnext
    rw [(r07_chain_resistance_ends h hn.le).2] at hg
    have hncore := (r07_chain_mass_cuts_core h false hnext.le).2.1
    refine ⟨neg_lt_neg (log_lt_log (ha.trans hc.1.1) hlo.1), ?_⟩
    have hlt := neg_lt_neg (log_lt_log (ha.trans hncore.1) hg)
    simpa only [r07DeepTailData, r07MassNodeRadius, r07MassExitRadius, r07OutwardLog,
      Bool.false_eq_true, if_false, Nat.add_assoc] using hlt
  · refine ⟨log_lt_log (ha.trans hc.1.1) hlo.1, ?_⟩
    have hg := r07_chain_massEnd_lt_resistanceEnd h true hn
    rw [(r07_chain_resistance_ends h hn.le).1] at hg
    have hlt := log_lt_log (ha.trans hc.2.1.1) hg
    simpa only [r07DeepTailData, r07MassNodeRadius, r07MassExitRadius, r07OutwardLog,
      if_true, Nat.add_assoc] using hlt

theorem r07_deepTail_initial_order {T : MorseChainData} {D : ReferenceData}
    {σ C : ℕ → ℝ} (h : MorseChainRealization T σ D C)
    (right : Bool) (j : ℕ) {start : ℕ} (hstart : T.index < start) (η K : ℝ) :
    let Q := r07DeepTailData T D right j start η K
    if right then Q.entrance = Q.node 0 else Q.entrance < Q.node 0 := by
  have ha := (r07_realization_geometry h).1
  cases right
  · have hc := (r07_chain_mass_cuts_core h false hstart.le).2.1
    have hg := r07_chain_massEnd_lt_resistanceEnd h false hstart
    have hlt := neg_lt_neg (log_lt_log (ha.trans hc.1) hg)
    simpa only [r07DeepTailData, r07MassNodeRadius, r07OutwardLog,
      Bool.false_eq_true, if_false, Nat.add_zero] using hlt
  · simp only [r07DeepTailData, r07MassNodeRadius, r07OutwardLog, if_true, Nat.add_zero]

theorem r07_outwardLog_lt_endpoint {D : ReferenceData} (hD : RadialProfileGeometry D)
    (right : Bool) {r : ℝ} (hr : r ∈ radialCore D) :
    r07OutwardLog right r < r07OutwardLog right (if right then D.b else D.a) := by
  cases right
  · exact neg_lt_neg (log_lt_log hD.1 hr.1)
  · exact log_lt_log (hD.1.trans hr.1) hr.2

theorem r07_deepTail_entrance_lt_endpoint {T : MorseChainData} {D : ReferenceData}
    {σ C : ℕ → ℝ} (h : MorseChainRealization T σ D C)
    (right : Bool) (j : ℕ) {start : ℕ} (hstart : T.index < start) (η K : ℝ) :
    (r07DeepTailData T D right j start η K).entrance <
      (r07DeepTailData T D right j start η K).endpoint := by
  have hlt := r07_outwardLog_lt_endpoint (r07_realization_geometry h) right
    (r07_deepTail_entrance_core h right j hstart η K)
  simpa only [r07DeepTailData, r07_outwardLog_radius] using hlt

theorem r07_deepTail_nodes_tendsto {T : MorseChainData} {D : ReferenceData}
    {σ C : ℕ → ℝ} (h : MorseChainRealization T σ D C)
    (right : Bool) (j : ℕ) {start : ℕ} (hstart : T.index < start) (η K : ℝ) :
    Tendsto (r07DeepTailData T D right j start η K).node atTop
      (𝓝 (r07DeepTailData T D right j start η K).endpoint) := by
  have hshift : Tendsto (fun n : ℕ => start + n) atTop atTop := by
    simpa only [Nat.add_comm] using tendsto_add_atTop_nat start
  have hl := (h.2.2.2.2.2.2.1 right).1.comp hshift
  have hr := (h.2.2.2.2.2.2.1 right).2.comp hshift
  have ht : Tendsto (fun n => morseChainMassEnd T right (start + n)) atTop
      (𝓝 (if right then D.b else D.a)) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le hl hr
      (fun n => (r07_chain_model_cuts h right
        (hstart.le.trans (Nat.le_add_right start n))).1.le)
      (fun n => (r07_chain_model_cuts h right
        (hstart.le.trans (Nat.le_add_right start n))).2.le)
  have hD := r07_realization_geometry h
  cases right
  · exact (ht.log hD.1.ne').neg
  · exact hl.log (hD.1.trans hD.2.1).ne'

end ContinuousFlexibility.Radial
