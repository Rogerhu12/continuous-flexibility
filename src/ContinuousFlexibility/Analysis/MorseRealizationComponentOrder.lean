module

public import ContinuousFlexibility.Radial.MorseModelReturn

/-!
# Ordering of the actual retained Morse components

The strict order of the realized joins separates successive model
intervals. It also places every closed turning interval in the original
outward tail, without assuming a stronger construction witness.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set
open ContinuousFlexibility.Statements

/-- The two families of actual turning components are strictly ordered,
and every closed component remains in its original retained tail. -/
theorem morseRealization_turning_component_order
    {T : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ}
    (hreal : MorseChainRealization T σ D C) :
    StrictAnti (fun k : ℕ => T.radius false (T.index + k)
      (morseLeftTurn (morseChainA T (T.index + k)) (morseChainB T (T.index + k)))) ∧
    StrictMono (fun k : ℕ => T.radius true (T.index + k)
      (morseLeftTurn (morseChainA T (T.index + k)) (morseChainB T (T.index + k)))) ∧
    ∀ side : Bool, ∀ n : ℕ, T.index ≤ n →
      Icc (T.radius side n (morseLeftTurn (morseChainA T n) (morseChainB T n)))
          (T.radius side n (morseRightTurn (morseChainA T n) (morseChainB T n))) ⊆
        radialTailInterval D side (morseChainSeam T side T.index) := by
  let L (side : Bool) (k : ℕ) :=
    T.radius side (T.index + k) (T.leftX side (T.index + k))
  let U (side : Bool) (k : ℕ) :=
    T.radius side (T.index + k) (T.rightX side (T.index + k))
  let a (side : Bool) (k : ℕ) := T.radius side (T.index + k)
    (morseLeftTurn (morseChainA T (T.index + k)) (morseChainB T (T.index + k)))
  let b (side : Bool) (k : ℕ) := T.radius side (T.index + k)
    (morseRightTurn (morseChainA T (T.index + k)) (morseChainB T (T.index + k)))
  have hbounds (side : Bool) (k : ℕ) :
      L side k < a side k ∧ a side k < b side k ∧ b side k < U side k := by
    have hn : T.index ≤ T.index + k := Nat.le_add_right _ _
    obtain ⟨hl, hab, hr⟩ := morseRealization_turns_retained hreal side hn
    have hlr := (hl.trans hab).trans hr
    have hmono := hreal.radius_strictMonoOn side (T.index + k) hn
    have hmL := left_mem_Icc.mpr hlr.le
    have hmR := right_mem_Icc.mpr hlr.le
    have hma : morseLeftTurn (morseChainA T (T.index + k))
        (morseChainB T (T.index + k)) ∈
          Icc (T.leftX side (T.index + k)) (T.rightX side (T.index + k)) :=
      ⟨hl.le, (hab.trans hr).le⟩
    have hmb : morseRightTurn (morseChainA T (T.index + k))
        (morseChainB T (T.index + k)) ∈
          Icc (T.leftX side (T.index + k)) (T.rightX side (T.index + k)) :=
      ⟨(hl.trans hab).le, hr.le⟩
    exact ⟨hmono hmL hma hl, hmono hma hmb hab, hmono hmb hmR hr⟩
  have hjoinL (k : ℕ) : U false (k + 1) < L false k := by
    have hj := hreal.join_data false (T.index + k) (Nat.le_add_right _ _)
    have h := hj.1
    rw [hj.2.1, hj.2.2.1] at h
    simpa only [L, U, Bool.false_eq_true, ↓reduceIte, Nat.add_assoc] using h
  have hjoinR (k : ℕ) : U true k < L true (k + 1) := by
    have hj := hreal.join_data true (T.index + k) (Nat.le_add_right _ _)
    have h := hj.1
    rw [hj.2.1, hj.2.2.1] at h
    simpa only [L, U, ↓reduceIte, Nat.add_assoc] using h
  have haL : StrictAnti (a false) := by
    apply strictAnti_nat_of_succ_lt
    intro k
    exact (((hbounds false (k + 1)).2.1.trans (hbounds false (k + 1)).2.2).trans
      (hjoinL k)).trans (hbounds false k).1
  have haR : StrictMono (a true) := by
    apply strictMono_nat_of_lt_succ
    intro k
    exact (((hbounds true k).2.1.trans (hbounds true k).2.2).trans
      (hjoinR k)).trans (hbounds true (k + 1)).1
  have hUL : Antitone (U false) := by
    apply antitone_nat_of_succ_le
    intro k
    exact ((hjoinL k).trans
      (((hbounds false k).1.trans (hbounds false k).2.1).trans (hbounds false k).2.2)).le
  have hLR : Monotone (L true) := by
    apply monotone_nat_of_le_succ
    intro k
    exact ((((hbounds true k).1.trans (hbounds true k).2.1).trans
      (hbounds true k).2.2).trans (hjoinR k)).le
  refine ⟨haL, haR, ?_⟩
  intro side n hn r hr
  have hn' : T.index + (n - T.index) = n := Nat.add_sub_of_le hn
  have hr' : r ∈ Icc (a side (n - T.index)) (b side (n - T.index)) := by
    simpa only [a, b, hn'] using hr
  obtain ⟨hl, hab, hu⟩ := morseRealization_turns_retained hreal side hn
  have haCore := hreal.radius_mem_core side n hn _ ⟨hl.le, (hab.trans hu).le⟩
  have hbCore := hreal.radius_mem_core side n hn _ ⟨(hl.trans hab).le, hu.le⟩
  cases side with
  | false =>
    refine ⟨haCore.1.trans_le hr.1, ?_⟩
    have h := (hr'.2.trans_lt (hbounds false (n - T.index)).2.2).trans_le
      (hUL (Nat.zero_le (n - T.index)))
    simpa only [U, Nat.add_zero, morseChainSeam, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    refine ⟨?_, hr.2.trans_lt hbCore.2⟩
    have h := (hLR (Nat.zero_le (n - T.index))).trans_lt
      ((hbounds true (n - T.index)).1.trans_le hr'.1)
    simpa only [L, Nat.add_zero, morseChainSeam, ↓reduceIte] using h

end ContinuousFlexibility.Radial
