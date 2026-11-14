module

public import ContinuousFlexibility.Radial.OuterDeepGeometry

/-!
# Physical cell labels of the actual Morse deep tail

The original chain's block-cover property supplies the physical labels.
On the left the outward edge crosses the next retained right endpoint:
its mass and glue have the current label, and its terminal cap has the
next label. The initial left edge has exactly the same two-label split.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set
open ContinuousFlexibility.Statements

private theorem morseRealized_block_cover {M : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ} (h : MorseChainRealization M σ D C)
    (right : Bool) (n : ℕ) (hn : M.index ≤ n) {x : ℝ}
    (hx : tailPhysicalRadius right x ∈ morseChainBlock M right n) :
    TailPhysicalCellAt D right n x := by
  rcases h with ⟨_, _, _, _, _, _, _, _, hcover, _⟩
  exact hcover right n hn _ hx

private theorem morseRealized_right_label {M : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ} (h : MorseChainRealization M σ D C)
    (n : ℕ) (hn : M.index ≤ n) {x : ℝ}
    (hx : x ∈ Icc (log (M.radius true n (M.leftX true n)))
      (log (M.radius true (n + 1) (M.leftX true (n + 1))))) :
    TailPhysicalCellAt D true n x := by
  have hm := morseRealized_mass_geometry h true n hn
  have hm' := morseRealized_mass_geometry h true (n + 1) (hn.trans (Nat.le_succ n))
  have hl := exp_le_exp.mpr hx.1
  have hr := exp_le_exp.mpr hx.2
  rw [exp_log (h.geometry.1.trans hm.1.1)] at hl
  rw [exp_log (h.geometry.1.trans hm'.1.1)] at hr
  apply morseRealized_block_cover h true n hn
  change exp x ∈ uIcc (M.radius true n (M.leftX true n))
    (M.radius true (n + 1) (M.leftX true (n + 1)))
  exact ⟨(min_le_left _ _).trans hl, hr.trans (le_max_right _ _)⟩

private theorem morseRealized_left_label {M : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ} (h : MorseChainRealization M σ D C)
    (n : ℕ) (hn : M.index ≤ n) {x : ℝ}
    (hx : x ∈ Icc (-log (M.radius false n (M.rightX false n)))
      (-log (M.radius false (n + 1) (M.rightX false (n + 1))))) :
    TailPhysicalCellAt D false n x := by
  have hm := morseRealized_mass_geometry h false n hn
  have hm' := morseRealized_mass_geometry h false (n + 1) (hn.trans (Nat.le_succ n))
  have hl := exp_le_exp.mpr (show log (M.radius false (n + 1) (M.rightX false (n + 1))) ≤ -x by
    linarith only [hx.2])
  have hr := exp_le_exp.mpr (show -x ≤ log (M.radius false n (M.rightX false n)) by
    linarith only [hx.1])
  rw [exp_log (h.geometry.1.trans hm'.2.2.1.1)] at hl
  rw [exp_log (h.geometry.1.trans hm.2.2.1.1)] at hr
  apply morseRealized_block_cover h false n hn
  change exp (-x) ∈ uIcc (M.radius false n (M.rightX false n))
    (M.radius false (n + 1) (M.rightX false (n + 1)))
  exact ⟨(min_le_right _ _).trans hl, hr.trans (le_max_left _ _)⟩

/-- The four consecutive pieces seen in the outward left logarithmic
coordinate: retained cap, mass, glue, next retained cap. -/
theorem morseRealized_left_log_order {M : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ} (h : MorseChainRealization M σ D C)
    (n : ℕ) (hn : M.index ≤ n) :
    -log (M.radius false n (M.rightX false n)) < -log (morseChainMassEnd M false n) ∧
      -log (morseChainMassEnd M false n) < -log (M.radius false n (M.leftX false n)) ∧
      -log (M.radius false n (M.leftX false n)) <
        -log (M.radius false (n + 1) (M.rightX false (n + 1))) ∧
      -log (M.radius false (n + 1) (M.rightX false (n + 1))) <
        -log (morseChainMassEnd M false (n + 1)) := by
  have hm := morseRealized_mass_geometry h false n hn
  have hm' := morseRealized_mass_geometry h false (n + 1) (hn.trans (Nat.le_succ n))
  have hj := h.join_data false n hn
  have hjord : M.radius false (n + 1) (M.rightX false (n + 1)) <
      M.radius false n (M.leftX false n) := by
    simpa only [hj.2.1, hj.2.2.1, Bool.false_eq_true, ite_false] using hj.1
  exact ⟨neg_lt_neg (log_lt_log (h.geometry.1.trans hm.2.1.1) hm.2.2.2.2),
    neg_lt_neg (log_lt_log (h.geometry.1.trans hm.1.1) hm.2.2.2.1),
    neg_lt_neg (log_lt_log (h.geometry.1.trans hm'.2.2.1.1) hjord),
    neg_lt_neg (log_lt_log (h.geometry.1.trans hm'.2.1.1) hm'.2.2.2.2)⟩

/-- All actual outward edges have the physical labels prescribed in
the frozen R06 interface, with the correct left cap shift. -/
theorem morsePhysicalDeepTail_localization {M : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ} (h : MorseChainRealization M σ D C)
    (right : Bool) (j n : ℕ) (hn : M.index ≤ n) (η K : ℝ) :
    TailPhysicalLocalization D
      (morsePhysicalDeepTail M D right j (n + 1)
        (morseOuterDeepEntrance M right n) η K) right (n + 1) := by
  cases right with
  | true =>
      refine ⟨(morsePhysicalDeepTail_right_entrance h j n hn η K).symm, ?_⟩
      intro k x hx
      apply morseRealized_right_label h (n + 1 + k)
        (hn.trans (by omega))
      change log (M.radius true (n + 1 + k) (M.leftX true (n + 1 + k))) < x ∧
        x < log (M.radius true (n + 1 + (k + 1)) (M.leftX true (n + 1 + (k + 1)))) at hx
      change log (M.radius true (n + 1 + k) (M.leftX true (n + 1 + k))) ≤ x ∧
        x ≤ log (M.radius true (n + 1 + k + 1) (M.leftX true (n + 1 + k + 1)))
      simpa only [Nat.add_assoc] using And.intro hx.1.le hx.2.le
  | false =>
      constructor
      · intro k
        let m := n + 1 + k
        have hm : M.index ≤ m := hn.trans (by dsimp only [m]; omega)
        have ho := morseRealized_left_log_order h m hm
        have ho' := morseRealized_left_log_order h (m + 1) (hm.trans (Nat.le_succ m))
        refine ⟨-log (M.radius false (m + 1) (M.rightX false (m + 1))), ?_, ?_, ?_⟩
        · exact ho.2.2.1
        · simpa only [m, Nat.add_assoc, morsePhysicalDeepTail, tailPhysicalLog,
            Bool.false_eq_true, ite_false] using ho.2.2.2
        · intro x hx
          change -log (morseChainMassEnd M false (n + 1 + k)) < x ∧
            x < -log (morseChainMassEnd M false (n + 1 + (k + 1))) at hx
          have hxl : -log (morseChainMassEnd M false m) < x := hx.1
          have hxr : x < -log (morseChainMassEnd M false (m + 1)) := by
            simpa only [m, Nat.add_assoc] using hx.2
          by_cases hb : x < -log (M.radius false (m + 1) (M.rightX false (m + 1)))
          · simp only [if_pos hb]
            exact morseRealized_left_label h m hm ⟨(ho.1.trans hxl).le, hb.le⟩
          · simp only [if_neg hb]
            exact morseRealized_left_label h (m + 1) (hm.trans (Nat.le_succ m))
              ⟨le_of_not_gt hb, (hxr.trans (ho'.2.1.trans ho'.2.2.1)).le⟩
      · right
        have ho := morseRealized_left_log_order h n hn
        have ho' := morseRealized_left_log_order h (n + 1) (hn.trans (Nat.le_succ n))
        refine ⟨Nat.zero_lt_succ n,
          -log (M.radius false (n + 1) (M.rightX false (n + 1))), ?_, ?_, ?_, ?_⟩
        · exact ho.2.2.1
        · simpa only [morsePhysicalDeepTail, tailPhysicalLog, Bool.false_eq_true,
            ite_false, Nat.add_zero] using ho.2.2.2
        · intro x hx
          change -log (M.radius false n (M.leftX false n)) ≤ x ∧
            x < -log (M.radius false (n + 1) (M.rightX false (n + 1))) at hx
          have hlabel := morseRealized_left_label h n hn
            ⟨((ho.1.trans ho.2.1).le.trans hx.1), hx.2.le⟩
          simpa only [Nat.add_sub_cancel] using hlabel
        · intro x hx
          change -log (M.radius false (n + 1) (M.rightX false (n + 1))) ≤ x ∧
            x < -log (morseChainMassEnd M false (n + 1 + 0)) at hx
          rw [Nat.add_zero] at hx
          exact morseRealized_left_label h (n + 1) (hn.trans (Nat.le_succ n))
            ⟨hx.1, (hx.2.trans (ho'.2.1.trans ho'.2.2.1)).le⟩

end ContinuousFlexibility.Radial
