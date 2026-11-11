import ContinuousFlexibility.Radial.OuterTailResistanceBounds

/-!
# The actual initial resistance has a uniform coefficient envelope

The left initial interval may include the preceding glue. Its actual
physical localization uses the first label or its predecessor, both of
which are controlled by the first coefficient weight. On the right the
initial interval has zero length.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set MeasureTheory
open ContinuousFlexibility.Statements

theorem outer_tail_initial_cell_label {D : ReferenceData} {T : DeepTailData}
    {right : Bool} {j start : ℕ}
    (hphysical : TailPhysicalRelation D T right j start)
    {x : ℝ} (hx : x ∈ Ioo T.entrance (T.node 0)) :
    ∃ m : ℕ, tailPhysicalRadius right x ∈ D.cells m ∧ D.cellIndex m ≤ start := by
  have hloc := hphysical.2.2.2.1
  cases right with
  | true =>
      change T.entrance = T.node 0 ∧ _ at hloc
      exact False.elim (not_lt_of_ge (hloc.1 ▸ hx.1.le) hx.2)
  | false =>
      change _ ∧ ((T.entrance < T.node 0 ∧
        ∀ x ∈ Ico T.entrance (T.node 0), TailPhysicalCellAt D false start x) ∨
        (0 < start ∧ ∃ capStart : ℝ,
          T.entrance < capStart ∧ capStart < T.node 0 ∧
          (∀ x ∈ Ico T.entrance capStart, TailPhysicalCellAt D false (start - 1) x) ∧
          ∀ x ∈ Ico capStart (T.node 0), TailPhysicalCellAt D false start x)) at hloc
      rcases hloc.2 with hfirst | ⟨_, cap, _, _, hbefore, hafter⟩
      · obtain ⟨m, hm, hxcell⟩ := hfirst.2 x ⟨hx.1.le, hx.2⟩
        exact ⟨m, hxcell, hm.le⟩
      · by_cases hc : x < cap
        · obtain ⟨m, hm, hxcell⟩ := hbefore x ⟨hx.1.le, hc⟩
          exact ⟨m, hxcell, hm.le.trans (Nat.sub_le _ _)⟩
        · obtain ⟨m, hm, hxcell⟩ := hafter x ⟨le_of_not_gt hc, hx.2⟩
          exact ⟨m, hxcell, hm.le⟩

theorem outer_tail_initial_resistance_le
    {D : ReferenceData} {T : DeepTailData} {C : ℕ → ℝ}
    (hC : AccumulatingProfileBounds D C) (hT : DeepTailHypotheses T)
    {right : Bool} {j start : ℕ} (hj : 2 ≤ j)
    (hphysical : TailPhysicalRelation D T right j start)
    (hclose : T.endpoint - T.entrance ≤ (2 * (j : ℝ) ^ 2)⁻¹) :
    tailInitialResistance T ≤ exp 1 * D.b * (C 0 * radialE start ^ (C 0)) := by
  have hC0 : 0 < C 0 := hC.2.2.1 0
  have hb : 0 < D.b := hC.1.1.trans hC.1.2.1
  have hnode := deepTail_node_lt_endpoint hT 0
  have hlen := outer_tail_length_le_one hj hclose
  apply outer_tail_short_interval_resistance hT hT.2.1
    (fun x hx => ⟨hx.1, hx.2.trans_lt hnode⟩)
    (by linarith only [hnode, hlen])
    (mul_nonneg (mul_nonneg (exp_pos 1).le hb.le)
      (mul_nonneg hC0.le
        (rpow_nonneg (show 0 ≤ radialE start from (exp_pos _).le) _)))
  intro x hx
  obtain ⟨m, hm, hi⟩ := outer_tail_initial_cell_label hphysical hx
  have hxT : x ∈ Ioo T.entrance T.endpoint := ⟨hx.1, hx.2.trans hnode⟩
  apply (outer_tail_reciprocal_density_cell_bound hC hj hphysical hclose hxT hm).trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (exp_pos 1).le hb.le)
  apply mul_le_mul_of_nonneg_left _ hC0.le
  rw [outer_radialE_rpow, outer_radialE_rpow]
  exact exp_le_exp.mpr (mul_le_mul_of_nonneg_left (radialQ_monotone hi) hC0.le)

theorem exists_outer_tail_initialResistance_envelope_uniform
    {C : ℕ → ℝ} (hC0 : 0 < C 0) {b : ℝ} (hb : 0 < b) :
    ∃ L : ℝ, 0 < L ∧ ∀ (D : ReferenceData), AccumulatingProfileBounds D C → D.b = b →
      ∀ (T : DeepTailData), DeepTailHypotheses T →
      ∀ (right : Bool) (j start : ℕ), 2 ≤ j → 1 ≤ start →
      TailPhysicalRelation D T right j start →
      T.endpoint - T.entrance ≤ (2 * (j : ℝ) ^ 2)⁻¹ →
        tailInitialResistance T ≤ radialE start ^ L := by
  let B := exp 1 * b * C 0
  have hB : 0 < B := by dsimp only [B]; positivity
  refine ⟨B + C 0, add_pos hB hC0, ?_⟩
  intro D hC hDb T hT right j start hj hstart hphysical hclose
  have hR := outer_tail_initial_resistance_le hC hT hj hphysical hclose
  rw [hDb] at hR
  calc
    _ ≤ exp 1 * b * (C 0 * radialE start ^ (C 0)) := hR
    _ = B * radialE start ^ (C 0) := by dsimp only [B]; ring
    _ ≤ radialE start ^ B * radialE start ^ (C 0) :=
      mul_le_mul_of_nonneg_right (outer_prefactor_le_envelope hstart hB.le)
        (rpow_nonneg (show 0 ≤ radialE start from (exp_pos _).le) _)
    _ = _ := (rpow_add (show 0 < radialE start from exp_pos _) B (C 0)).symm

theorem exists_outer_tail_initialResistance_envelope
    {D : ReferenceData} {C : ℕ → ℝ} (hC : AccumulatingProfileBounds D C) :
    ∃ L : ℝ, 0 < L ∧ ∀ (T : DeepTailData), DeepTailHypotheses T →
      ∀ (right : Bool) (j start : ℕ), 2 ≤ j → 1 ≤ start →
      TailPhysicalRelation D T right j start →
      T.endpoint - T.entrance ≤ (2 * (j : ℝ) ^ 2)⁻¹ →
        tailInitialResistance T ≤ radialE start ^ L := by
  obtain ⟨L, hL, hbound⟩ := exists_outer_tail_initialResistance_envelope_uniform
    (hC.2.2.1 0) (hC.1.1.trans hC.1.2.1)
  exact ⟨L, hL, hbound D hC rfl⟩

end ContinuousFlexibility.Radial
