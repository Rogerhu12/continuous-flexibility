module

public import ContinuousFlexibility.Radial.InnerModelChainGeometry
public import ContinuousFlexibility.Radial.InnerMorseTailGap

/-!
# The actual finite inner chain of central and Morse cut models

The model order is the left tail in decreasing cell index, the central
model, and the right tail in increasing cell index. The two outer points
are the outer endpoints of the last retained cells. Thus the terminal
pieces are cap remnants, rather than whole additional joins.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set ContinuousFlexibility.Statements

/-- Every two different retained cells are ordered in physical radius.
The same statement treats both orientations of the tail index. -/
theorem innerMorseChain_models_separated {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ} (h : MorseChainRealization T σ D C)
    (side : Bool) {m n : ℕ} (hm : T.index ≤ m) (hmn : m < n) :
    innerMorseChainCut T side (if side then m else n) 1 <
      innerMorseChainCut T side (if side then n else m) 0 := by
  have hmn' : m + 1 ≤ n := hmn
  clear hmn
  induction n, hmn' using Nat.le_induction with
  | base =>
    have hg := innerMorseTailGap_geometry h side hm
    simpa only [innerMorseTailGapLeft, innerMorseTailGapRight,
      innerMorseTailDeparture, innerMorseTailArrival] using
      hg.1.trans (hg.2.1.trans hg.2.2.1)
  | succ n hmn ih =>
    have hn : T.index ≤ n := hm.trans (by omega)
    have hg := innerMorseTailGap_geometry h side hn
    have hstep : innerMorseChainCut T side (if side then n else n + 1) 1 <
        innerMorseChainCut T side (if side then n + 1 else n) 0 := by
      simpa only [innerMorseTailGapLeft, innerMorseTailGapRight,
        innerMorseTailDeparture, innerMorseTailArrival] using
        hg.1.trans (hg.2.1.trans hg.2.2.1)
    have hi := (innerMorseChainCut_geometry h side hn).2.1
    cases side with
    | false =>
      simp only [Bool.false_eq_true, ite_false] at ih hstep ⊢
      exact hstep.trans (hi.trans ih)
    | true =>
      simp only [ite_true] at ih hstep ⊢
      exact ih.trans (hi.trans hstep)

private theorem innerMorseLeftCut_le_base {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ} (h : MorseChainRealization T σ D C)
    {N m : ℕ} (hN : T.index ≤ N) (hm : N ≤ m) :
    innerMorseChainCut T false m 1 ≤ innerMorseChainCut T false N 1 := by
  rcases hm.eq_or_lt with rfl | hm
  · exact le_rfl
  · have hs := innerMorseChain_models_separated h false hN hm
    simp only [Bool.false_eq_true, ite_false] at hs
    exact (hs.trans (innerMorseChainCut_geometry h false hN).2.1).le

private theorem innerMorseBase_le_rightCut {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ} (h : MorseChainRealization T σ D C)
    {N m : ℕ} (hN : T.index ≤ N) (hm : N ≤ m) :
    innerMorseChainCut T true N 0 ≤ innerMorseChainCut T true m 0 := by
  rcases hm.eq_or_lt with rfl | hm
  · exact le_rfl
  · have hs := innerMorseChain_models_separated h true hN hm
    simp only [ite_true] at hs
    exact ((innerMorseChainCut_geometry h true hN).2.1.trans hs).le

def innerMorseInnerModelCuts (T : MorseChainData) (N K : ℕ) (center : Fin 2 → ℝ)
    (p : Fin (2 * K + 1)) (i : Fin 2) : ℝ :=
  if p.val < K then innerMorseChainCut T false (N + (K - 1 - p.val)) i
  else if p.val = K then center i
  else innerMorseChainCut T true (N + (p.val - K - 1)) i

def innerMorseInnerCenter (K : ℕ) : Fin (2 * K + 1) := ⟨K, by omega⟩

def innerMorseInnerTailSlot (K : ℕ) (side : Bool) (p : Fin K) : Fin (2 * K + 1) :=
  if side then ⟨K + 1 + p.val, by omega⟩ else ⟨p.val, by omega⟩

def innerMorseInnerTailIndex (N K : ℕ) (side : Bool) (p : Fin K) : ℕ :=
  if side then N + p.val else N + (K - 1 - p.val)

theorem innerMorseInnerTailIndex_bounds (N K : ℕ) (side : Bool) (p : Fin K) :
    N ≤ innerMorseInnerTailIndex N K side p ∧ innerMorseInnerTailIndex N K side p < N + K := by
  cases side <;> simp only [innerMorseInnerTailIndex, Bool.false_eq_true, ite_false, ite_true] <;> omega

theorem innerMorseInnerTailSlot_ne_center (K : ℕ) (side : Bool) (p : Fin K) :
    innerMorseInnerTailSlot K side p ≠ innerMorseInnerCenter K := by
  intro he
  have hv := congrArg Fin.val he
  cases side <;> simp only [innerMorseInnerTailSlot, innerMorseInnerCenter,
    Bool.false_eq_true, ite_false, ite_true] at hv <;> omega

theorem innerMorseInnerTailPiece_ne_center (K : ℕ) (side : Bool) (p : Fin K) :
    innerModelChainPiece (innerMorseInnerTailSlot K side p) ≠
      innerModelChainPiece (innerMorseInnerCenter K) :=
  fun he => innerMorseInnerTailSlot_ne_center K side p (innerModelChainPiece_injective he)

theorem innerMorseInnerModelCuts_center (T : MorseChainData) (N K : ℕ)
    (center : Fin 2 → ℝ) (i : Fin 2) :
    innerMorseInnerModelCuts T N K center (innerMorseInnerCenter K) i = center i := by
  simp only [innerMorseInnerModelCuts, innerMorseInnerCenter, lt_self_iff_false,
    ite_false, ite_true]

theorem innerMorseInnerModelCuts_tail (T : MorseChainData) (N K : ℕ)
    (center : Fin 2 → ℝ) (side : Bool) (p : Fin K) (i : Fin 2) :
    innerMorseInnerModelCuts T N K center (innerMorseInnerTailSlot K side p) i =
      innerMorseChainCut T side (innerMorseInnerTailIndex N K side p) i := by
  cases side with
  | false =>
    simp only [innerMorseInnerTailSlot, innerMorseInnerTailIndex, Bool.false_eq_true,
      ite_false, innerMorseInnerModelCuts, p.isLt, ite_true]
  | true =>
    have hlt : ¬K + 1 + p.val < K := by omega
    have hne : K + 1 + p.val ≠ K := by omega
    have heq : K + 1 + p.val - K - 1 = p.val := by omega
    simp only [innerMorseInnerTailSlot, innerMorseInnerTailIndex, ite_true,
      innerMorseInnerModelCuts, hlt, hne, ite_false, heq]

theorem innerMorseInnerModelCuts_order {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ} (h : MorseChainRealization T σ D C)
    {N K : ℕ} (hN : T.index ≤ N) {center : Fin 2 → ℝ}
    (hc : center 0 < center 1) :
    ∀ p, innerMorseInnerModelCuts T N K center p 0 <
      innerMorseInnerModelCuts T N K center p 1 := by
  intro p
  unfold innerMorseInnerModelCuts
  split_ifs
  · exact (innerMorseChainCut_geometry h false (hN.trans (Nat.le_add_right _ _))).2.1
  · exact hc
  · exact (innerMorseChainCut_geometry h true (hN.trans (Nat.le_add_right _ _))).2.1

/-- Separation of all enumerated model pairs is derived from the
realized tail ordering and the two raw central connector endpoints. -/
theorem innerMorseInnerModelCuts_separated {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ} (h : MorseChainRealization T σ D C)
    {N K : ℕ} (hN : T.index ≤ N) {center : Fin 2 → ℝ}
    (hc : center 0 < center 1)
    (hcl : innerMorseChainCut T false N 1 < center 0)
    (hcr : center 1 < innerMorseChainCut T true N 0) :
    ∀ p q, p < q → innerMorseInnerModelCuts T N K center p 1 <
      innerMorseInnerModelCuts T N K center q 0 := by
  intro p q hpq
  have hpq' : p.val < q.val := hpq
  by_cases hp : p.val < K
  · by_cases hq : q.val < K
    · have hidx : N + (K - 1 - q.val) < N + (K - 1 - p.val) := by omega
      have hsep := innerMorseChain_models_separated h false
        (hN.trans (Nat.le_add_right _ _)) hidx
      simpa only [innerMorseInnerModelCuts, hp, hq, ite_true, Bool.false_eq_true,
        ite_false] using hsep
    · have hl := (innerMorseLeftCut_le_base h hN
        (Nat.le_add_right N (K - 1 - p.val))).trans_lt hcl
      by_cases hq0 : q.val = K
      · simpa only [innerMorseInnerModelCuts, hp, hq, hq0, lt_self_iff_false,
          ite_true, ite_false] using hl
      · have hr := hcr.trans_le (innerMorseBase_le_rightCut h hN
          (Nat.le_add_right N (q.val - K - 1)))
        simpa only [innerMorseInnerModelCuts, hp, hq, hq0, ite_true, ite_false] using
          hl.trans (hc.trans hr)
  · have hq : ¬q.val < K := by omega
    have hq0 : q.val ≠ K := by omega
    by_cases hp0 : p.val = K
    · have hr := hcr.trans_le (innerMorseBase_le_rightCut h hN
        (Nat.le_add_right N (q.val - K - 1)))
      simpa only [innerMorseInnerModelCuts, hp, hq, hp0, hq0, lt_self_iff_false,
        ite_true, ite_false] using hr
    · have hidx : N + (p.val - K - 1) < N + (q.val - K - 1) := by omega
      have hsep := innerMorseChain_models_separated h true
        (hN.trans (Nat.le_add_right _ _)) hidx
      simpa only [innerMorseInnerModelCuts, hp, hq, hp0, hq0, ite_true, ite_false] using hsep

/-- The outer point is the original retained endpoint of cell n-1,
where n=N+K. It is the entrance of the next join in the outward direction. -/
def innerMorseInnerOuterPoint (T : MorseChainData) (N K : ℕ) (side : Bool) : ℝ :=
  T.radius side (N + (K - 1))
    (if side then T.rightX side (N + (K - 1)) else T.leftX side (N + (K - 1)))

theorem innerMorseInnerOuterPoint_mem_core {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ} (h : MorseChainRealization T σ D C)
    {N K : ℕ} (hN : T.index ≤ N) (side : Bool) :
    innerMorseInnerOuterPoint T N K side ∈ radialCore D := by
  have hm : T.index ≤ N + (K - 1) := hN.trans (Nat.le_add_right _ _)
  obtain ⟨_, _, _, hl, hr, _, _⟩ := h.retained_data side (N + (K - 1)) hm
  apply h.radius_mem_core side (N + (K - 1)) hm
  cases side with
  | false => exact left_mem_Icc.mpr (hl.trans hr).le
  | true => exact right_mem_Icc.mpr (hl.trans hr).le

theorem innerMorseInnerOuterPoint_eq_joinEntrance {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ} (h : MorseChainRealization T σ D C)
    {N K : ℕ} (hN : T.index ≤ N) (side : Bool) :
    innerMorseInnerOuterPoint T N K side =
      if side then T.joinLeft side (N + (K - 1)) else T.joinRight side (N + (K - 1)) := by
  have hm : T.index ≤ N + (K - 1) := hN.trans (Nat.le_add_right _ _)
  have hj := h.join_data side (N + (K - 1)) hm
  cases side with
  | false =>
    simpa only [innerMorseInnerOuterPoint, Bool.false_eq_true, ite_false] using hj.2.2.1.symm
  | true => simpa only [innerMorseInnerOuterPoint, ite_true] using hj.2.1.symm

theorem innerMorseInner_outer_bounds {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ} (h : MorseChainRealization T σ D C)
    {N K : ℕ} (hN : T.index ≤ N) (hK : 0 < K) {center : Fin 2 → ℝ}
    (hc : center 0 < center 1)
    (hcl : innerMorseChainCut T false N 1 < center 0)
    (hcr : center 1 < innerMorseChainCut T true N 0) :
    innerMorseInnerOuterPoint T N K false < innerMorseInnerOuterPoint T N K true ∧
      (∀ p, innerMorseInnerOuterPoint T N K false < innerMorseInnerModelCuts T N K center p 0) ∧
      ∀ p, innerMorseInnerModelCuts T N K center p 1 < innerMorseInnerOuterPoint T N K true := by
  have hm : T.index ≤ N + (K - 1) := hN.trans (Nat.le_add_right _ _)
  have hmodel := innerMorseInnerModelCuts_order (K := K) h hN hc
  have hsep := innerMorseInnerModelCuts_separated (K := K) h hN hc hcl hcr
  have hfirst : innerMorseInnerOuterPoint T N K false <
      innerMorseInnerModelCuts T N K center 0 0 := by
    simpa only [innerMorseInnerOuterPoint, Bool.false_eq_true, ite_false,
      innerMorseInnerModelCuts, Fin.val_zero, hK, ite_true, Nat.sub_zero] using
      (innerMorseChainCut_geometry h false hm).1
  have hlast : innerMorseInnerModelCuts T N K center (Fin.last (2 * K)) 1 <
      innerMorseInnerOuterPoint T N K true := by
    have hlt : ¬2 * K < K := by omega
    have hne : 2 * K ≠ K := by omega
    have hidx : 2 * K - K - 1 = K - 1 := by omega
    simpa only [innerMorseInnerOuterPoint, ite_true, innerMorseInnerModelCuts,
      Fin.val_last, hlt, hne, ite_false, hidx] using
      (innerMorseChainCut_geometry h true hm).2.2.1
  have hleft (p : Fin (2 * K + 1)) : innerMorseInnerOuterPoint T N K false <
      innerMorseInnerModelCuts T N K center p 0 := by
    by_cases hp : p = 0
    · simpa only [hp] using hfirst
    · exact hfirst.trans ((hmodel 0).trans (hsep 0 p
        (lt_of_le_of_ne (Fin.zero_le p) (Ne.symm hp))))
  have hright (p : Fin (2 * K + 1)) : innerMorseInnerModelCuts T N K center p 1 <
      innerMorseInnerOuterPoint T N K true := by
    by_cases hp : p = Fin.last (2 * K)
    · simpa only [hp] using hlast
    · exact (hsep p (Fin.last (2 * K)) (lt_of_le_of_ne (Fin.le_last p) hp)).trans
        ((hmodel (Fin.last (2 * K))).trans hlast)
  exact ⟨(hleft 0).trans ((hmodel 0).trans (hright 0)), hleft, hright⟩

/-- The actual chain for K>0. Its only central inputs are the two raw
cut positions and their ordering relative to the fixed tail entrances.
All tail cuts and both terminal points are the explicit original ones. -/
def innerMorseInnerChainGeometry {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ} (h : MorseChainRealization T σ D C)
    {N K : ℕ} (hN : T.index ≤ N) (hK : 0 < K) (center : Fin 2 → ℝ)
    (hc : center 0 < center 1)
    (hcl : innerMorseChainCut T false N 1 < center 0)
    (hcr : center 1 < innerMorseChainCut T true N 0) :
    InnerRadialChainGeometry D (2 * (2 * K + 1)) := by
  have ho := innerMorseInner_outer_bounds h hN hK hc hcl hcr
  exact innerRadialChainOfModels D h.geometry (innerMorseInnerModelCuts T N K center)
    (innerMorseInnerOuterPoint T N K false) (innerMorseInnerOuterPoint T N K true)
    (innerMorseInnerOuterPoint_mem_core h hN false) (innerMorseInnerOuterPoint_mem_core h hN true)
    ho.1 (innerMorseInnerModelCuts_order h hN hc)
    (innerMorseInnerModelCuts_separated h hN hc hcl hcr) ho.2.1 ho.2.2

section ExplicitPieces

variable {T : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ}
  (h : MorseChainRealization T σ D C) {N K : ℕ} (hN : T.index ≤ N) (hK : 0 < K)
  (center : Fin 2 → ℝ) (hc : center 0 < center 1)
  (hcl : innerMorseChainCut T false N 1 < center 0)
  (hcr : center 1 < innerMorseChainCut T true N 0)

theorem innerMorseInnerChainGeometry_left (p : Fin (2 * K + 1)) :
    (innerMorseInnerChainGeometry h hN hK center hc hcl hcr).left (innerModelChainPiece p) =
      innerMorseInnerModelCuts T N K center p 0 :=
  innerModelChainCuts_model_left (innerMorseInnerModelCuts T N K center)
    (innerMorseInnerOuterPoint T N K false) (innerMorseInnerOuterPoint T N K true) p

theorem innerMorseInnerChainGeometry_right (p : Fin (2 * K + 1)) :
    (innerMorseInnerChainGeometry h hN hK center hc hcl hcr).right (innerModelChainPiece p) =
      innerMorseInnerModelCuts T N K center p 1 :=
  innerModelChainCuts_model_right (innerMorseInnerModelCuts T N K center)
    (innerMorseInnerOuterPoint T N K false) (innerMorseInnerOuterPoint T N K true) p

theorem innerMorseInnerChainGeometry_center :
    (innerMorseInnerChainGeometry h hN hK center hc hcl hcr).left
        (innerModelChainPiece (innerMorseInnerCenter K)) = center 0 ∧
      (innerMorseInnerChainGeometry h hN hK center hc hcl hcr).right
        (innerModelChainPiece (innerMorseInnerCenter K)) = center 1 := by
  rw [innerMorseInnerChainGeometry_left, innerMorseInnerChainGeometry_right,
    innerMorseInnerModelCuts_center, innerMorseInnerModelCuts_center]
  exact ⟨rfl, rfl⟩

theorem innerMorseInnerChainGeometry_tail (side : Bool) (p : Fin K) :
    (innerMorseInnerChainGeometry h hN hK center hc hcl hcr).left
        (innerModelChainPiece (innerMorseInnerTailSlot K side p)) =
          innerMorseChainCut T side (innerMorseInnerTailIndex N K side p) 0 ∧
      (innerMorseInnerChainGeometry h hN hK center hc hcl hcr).right
        (innerModelChainPiece (innerMorseInnerTailSlot K side p)) =
          innerMorseChainCut T side (innerMorseInnerTailIndex N K side p) 1 := by
  rw [innerMorseInnerChainGeometry_left, innerMorseInnerChainGeometry_right,
    innerMorseInnerModelCuts_tail, innerMorseInnerModelCuts_tail]
  exact ⟨rfl, rfl⟩

end ExplicitPieces

/-- First-band geometry has only the central model and the two raw
middle/head intervals. No nonexistent join with index N-1 is used. -/
def innerCentralOnlyChainGeometry (D : ReferenceData) (hD : RadialProfileGeometry D)
    (center : Fin 2 → ℝ) (L R : ℝ) (hL : L ∈ radialCore D) (hR : R ∈ radialCore D)
    (hleft : L < center 0) (hc : center 0 < center 1) (hright : center 1 < R) :
    InnerRadialChainGeometry D 2 :=
  innerRadialChainOfModels D hD (fun _ : Fin 1 => center) L R hL hR
    (hleft.trans (hc.trans hright)) (fun _ => hc)
    (fun p q hpq => False.elim (by
      have he : p = q := Subsingleton.elim _ _
      rw [he] at hpq
      exact (lt_irrefl q) hpq))
    (fun _ => hleft) (fun _ => hright)

end ContinuousFlexibility.Radial
