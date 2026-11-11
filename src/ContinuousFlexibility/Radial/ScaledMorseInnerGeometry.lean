import ContinuousFlexibility.Radial.InnerMorseInnerChain

/-!
# The finite inner geometry with independent left and right radius scales

Only the old selected profile is a Morse-chain realization. The new
profile supplies its actual core and positivity. Every old cut and
terminal point is rescaled on its own side, while the central cut pair
is specified in the new physical radius.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set ContinuousFlexibility.Statements

def scaledMorseInnerModelCuts (T : MorseChainData) (κ : Bool → ℝ)
    (N K : ℕ) (center : Fin 2 → ℝ) (p : Fin (2 * K + 1)) (i : Fin 2) : ℝ :=
  if p.val < K then κ false * innerMorseChainCut T false (N + (K - 1 - p.val)) i
  else if p.val = K then center i
  else κ true * innerMorseChainCut T true (N + (p.val - K - 1)) i

def scaledMorseInnerOuterPoint (T : MorseChainData) (κ : Bool → ℝ)
    (N K : ℕ) (side : Bool) : ℝ := κ side * innerMorseInnerOuterPoint T N K side

theorem scaledMorseInnerModelCuts_center (T : MorseChainData) (κ : Bool → ℝ) (N K : ℕ)
    (center : Fin 2 → ℝ) (i : Fin 2) :
    scaledMorseInnerModelCuts T κ N K center (innerMorseInnerCenter K) i = center i := by
  simp only [scaledMorseInnerModelCuts, innerMorseInnerCenter, lt_self_iff_false,
    ite_false, ite_true]

theorem scaledMorseInnerModelCuts_tail (T : MorseChainData) (κ : Bool → ℝ) (N K : ℕ)
    (center : Fin 2 → ℝ) (side : Bool) (p : Fin K) (i : Fin 2) :
    scaledMorseInnerModelCuts T κ N K center (innerMorseInnerTailSlot K side p) i =
      κ side * innerMorseChainCut T side (innerMorseInnerTailIndex N K side p) i := by
  cases side with
  | false =>
    simp only [innerMorseInnerTailSlot, innerMorseInnerTailIndex, Bool.false_eq_true,
      ite_false, scaledMorseInnerModelCuts, p.isLt, ite_true]
  | true =>
    have hlt : ¬K + 1 + p.val < K := by omega
    have hne : K + 1 + p.val ≠ K := by omega
    have heq : K + 1 + p.val - K - 1 = p.val := by omega
    simp only [innerMorseInnerTailSlot, innerMorseInnerTailIndex, ite_true,
      scaledMorseInnerModelCuts, hlt, hne, ite_false, heq]

section OrderedCuts

variable {T : MorseChainData} {σ : ℕ → ℝ} {old : ReferenceData} {cost : ℕ → ℝ}
  (h : MorseChainRealization T σ old cost) (κ : Bool → ℝ) (hκ : ∀ side, 0 < κ side)
  {N K : ℕ} (hN : T.index ≤ N) {center : Fin 2 → ℝ}
  (hc : center 0 < center 1)
  (hcl : κ false * innerMorseChainCut T false N 1 < center 0)
  (hcr : center 1 < κ true * innerMorseChainCut T true N 0)

include h hκ hN in
private theorem scaledMorseLeftCut_le_base {m : ℕ} (hm : N ≤ m) :
    κ false * innerMorseChainCut T false m 1 ≤ κ false * innerMorseChainCut T false N 1 := by
  apply mul_le_mul_of_nonneg_left _ (hκ false).le
  rcases hm.eq_or_lt with rfl | hm
  · exact le_rfl
  · have hs := innerMorseChain_models_separated h false hN hm
    simp only [Bool.false_eq_true, ite_false] at hs
    exact (hs.trans (innerMorseChainCut_geometry h false hN).2.1).le

include h hκ hN in
private theorem scaledMorseBase_le_rightCut {m : ℕ} (hm : N ≤ m) :
    κ true * innerMorseChainCut T true N 0 ≤ κ true * innerMorseChainCut T true m 0 := by
  apply mul_le_mul_of_nonneg_left _ (hκ true).le
  rcases hm.eq_or_lt with rfl | hm
  · exact le_rfl
  · have hs := innerMorseChain_models_separated h true hN hm
    simp only [ite_true] at hs
    exact ((innerMorseChainCut_geometry h true hN).2.1.trans hs).le

include h hκ hN hc in
theorem scaledMorseInnerModelCuts_order :
    ∀ p, scaledMorseInnerModelCuts T κ N K center p 0 <
      scaledMorseInnerModelCuts T κ N K center p 1 := by
  intro p
  unfold scaledMorseInnerModelCuts
  split_ifs
  · exact mul_lt_mul_of_pos_left
      (innerMorseChainCut_geometry h false (hN.trans (Nat.le_add_right _ _))).2.1 (hκ false)
  · exact hc
  · exact mul_lt_mul_of_pos_left
      (innerMorseChainCut_geometry h true (hN.trans (Nat.le_add_right _ _))).2.1 (hκ true)

include h hκ hN hc hcl hcr in
theorem scaledMorseInnerModelCuts_separated :
    ∀ p q, p < q → scaledMorseInnerModelCuts T κ N K center p 1 <
      scaledMorseInnerModelCuts T κ N K center q 0 := by
  intro p q hpq
  have hpq' : p.val < q.val := hpq
  by_cases hp : p.val < K
  · by_cases hq : q.val < K
    · have hidx : N + (K - 1 - q.val) < N + (K - 1 - p.val) := by omega
      have hs := mul_lt_mul_of_pos_left (innerMorseChain_models_separated h false
        (hN.trans (Nat.le_add_right _ _)) hidx) (hκ false)
      simpa only [scaledMorseInnerModelCuts, hp, hq, ite_true, Bool.false_eq_true,
        ite_false] using hs
    · have hl := (scaledMorseLeftCut_le_base h κ hκ hN
        (Nat.le_add_right N (K - 1 - p.val))).trans_lt hcl
      by_cases hq0 : q.val = K
      · simpa only [scaledMorseInnerModelCuts, hp, hq, hq0, lt_self_iff_false,
          ite_true, ite_false] using hl
      · have hr := hcr.trans_le (scaledMorseBase_le_rightCut h κ hκ hN
          (Nat.le_add_right N (q.val - K - 1)))
        simpa only [scaledMorseInnerModelCuts, hp, hq, hq0, ite_true, ite_false] using
          hl.trans (hc.trans hr)
  · have hq : ¬q.val < K := by omega
    have hq0 : q.val ≠ K := by omega
    by_cases hp0 : p.val = K
    · have hr := hcr.trans_le (scaledMorseBase_le_rightCut h κ hκ hN
        (Nat.le_add_right N (q.val - K - 1)))
      simpa only [scaledMorseInnerModelCuts, hp, hq, hp0, hq0, lt_self_iff_false,
        ite_true, ite_false] using hr
    · have hidx : N + (p.val - K - 1) < N + (q.val - K - 1) := by omega
      have hs := mul_lt_mul_of_pos_left (innerMorseChain_models_separated h true
        (hN.trans (Nat.le_add_right _ _)) hidx) (hκ true)
      simpa only [scaledMorseInnerModelCuts, hp, hq, hp0, hq0, ite_true, ite_false] using hs

include h hκ hN hc hcl hcr in
theorem scaledMorseInner_outer_bounds (hK : 0 < K) :
    scaledMorseInnerOuterPoint T κ N K false < scaledMorseInnerOuterPoint T κ N K true ∧
      (∀ p, scaledMorseInnerOuterPoint T κ N K false <
        scaledMorseInnerModelCuts T κ N K center p 0) ∧
      ∀ p, scaledMorseInnerModelCuts T κ N K center p 1 <
        scaledMorseInnerOuterPoint T κ N K true := by
  have hm : T.index ≤ N + (K - 1) := hN.trans (Nat.le_add_right _ _)
  have hmodel := scaledMorseInnerModelCuts_order (K := K) h κ hκ hN hc
  have hsep := scaledMorseInnerModelCuts_separated (K := K) h κ hκ hN hc hcl hcr
  have hfirst : scaledMorseInnerOuterPoint T κ N K false <
      scaledMorseInnerModelCuts T κ N K center 0 0 := by
    simpa only [scaledMorseInnerOuterPoint, innerMorseInnerOuterPoint,
      Bool.false_eq_true, ite_false, scaledMorseInnerModelCuts, Fin.val_zero,
      hK, ite_true, Nat.sub_zero] using
      mul_lt_mul_of_pos_left (innerMorseChainCut_geometry h false hm).1 (hκ false)
  have hlast : scaledMorseInnerModelCuts T κ N K center (Fin.last (2 * K)) 1 <
      scaledMorseInnerOuterPoint T κ N K true := by
    have hlt : ¬2 * K < K := by omega
    have hne : 2 * K ≠ K := by omega
    have hidx : 2 * K - K - 1 = K - 1 := by omega
    simpa only [scaledMorseInnerOuterPoint, innerMorseInnerOuterPoint, ite_true,
      scaledMorseInnerModelCuts, Fin.val_last, hlt, hne, ite_false, hidx] using
      mul_lt_mul_of_pos_left (innerMorseChainCut_geometry h true hm).2.2.1 (hκ true)
  have hleft (p : Fin (2 * K + 1)) : scaledMorseInnerOuterPoint T κ N K false <
      scaledMorseInnerModelCuts T κ N K center p 0 := by
    by_cases hp : p = 0
    · simpa only [hp] using hfirst
    · exact hfirst.trans ((hmodel 0).trans (hsep 0 p
        (lt_of_le_of_ne (Fin.zero_le p) (Ne.symm hp))))
  have hright (p : Fin (2 * K + 1)) : scaledMorseInnerModelCuts T κ N K center p 1 <
      scaledMorseInnerOuterPoint T κ N K true := by
    by_cases hp : p = Fin.last (2 * K)
    · simpa only [hp] using hlast
    · exact (hsep p (Fin.last (2 * K)) (lt_of_le_of_ne (Fin.le_last p) hp)).trans
        ((hmodel (Fin.last (2 * K))).trans hlast)
  exact ⟨(hleft 0).trans ((hmodel 0).trans (hright 0)), hleft, hright⟩

variable (D : ReferenceData) (hD : RadialProfileGeometry D) (hK : 0 < K)
  (hLcore : scaledMorseInnerOuterPoint T κ N K false ∈ radialCore D)
  (hRcore : scaledMorseInnerOuterPoint T κ N K true ∈ radialCore D)

def scaledMorseInnerChainGeometry : InnerRadialChainGeometry D (2 * (2 * K + 1)) := by
  have ho := scaledMorseInner_outer_bounds h κ hκ hN hc hcl hcr hK
  exact innerRadialChainOfModels D hD (scaledMorseInnerModelCuts T κ N K center)
    (scaledMorseInnerOuterPoint T κ N K false) (scaledMorseInnerOuterPoint T κ N K true)
    hLcore hRcore ho.1 (scaledMorseInnerModelCuts_order h κ hκ hN hc)
    (scaledMorseInnerModelCuts_separated h κ hκ hN hc hcl hcr) ho.2.1 ho.2.2

local notation "G" => scaledMorseInnerChainGeometry h κ hκ hN hc hcl hcr D hD hK hLcore hRcore

theorem scaledMorseInnerChainGeometry_left (p : Fin (2 * K + 1)) :
    G.left (innerModelChainPiece p) = scaledMorseInnerModelCuts T κ N K center p 0 :=
  innerModelChainCuts_model_left (scaledMorseInnerModelCuts T κ N K center)
    (scaledMorseInnerOuterPoint T κ N K false) (scaledMorseInnerOuterPoint T κ N K true) p

theorem scaledMorseInnerChainGeometry_right (p : Fin (2 * K + 1)) :
    G.right (innerModelChainPiece p) = scaledMorseInnerModelCuts T κ N K center p 1 :=
  innerModelChainCuts_model_right (scaledMorseInnerModelCuts T κ N K center)
    (scaledMorseInnerOuterPoint T κ N K false) (scaledMorseInnerOuterPoint T κ N K true) p

theorem scaledMorseInnerChainGeometry_model (p : Fin (2 * K + 1)) :
    G.left (innerModelChainPiece p) = scaledMorseInnerModelCuts T κ N K center p 0 ∧
      G.right (innerModelChainPiece p) = scaledMorseInnerModelCuts T κ N K center p 1 :=
  ⟨scaledMorseInnerChainGeometry_left h κ hκ hN hc hcl hcr D hD hK hLcore hRcore p,
    scaledMorseInnerChainGeometry_right h κ hκ hN hc hcl hcr D hD hK hLcore hRcore p⟩

theorem scaledMorseInnerChainGeometry_center :
    G.left (innerModelChainPiece (innerMorseInnerCenter K)) = center 0 ∧
      G.right (innerModelChainPiece (innerMorseInnerCenter K)) = center 1 := by
  rw [scaledMorseInnerChainGeometry_left, scaledMorseInnerChainGeometry_right,
    scaledMorseInnerModelCuts_center, scaledMorseInnerModelCuts_center]
  exact ⟨rfl, rfl⟩

theorem scaledMorseInnerChainGeometry_tail (side : Bool) (p : Fin K) :
    G.left (innerModelChainPiece (innerMorseInnerTailSlot K side p)) =
        κ side * innerMorseChainCut T side (innerMorseInnerTailIndex N K side p) 0 ∧
      G.right (innerModelChainPiece (innerMorseInnerTailSlot K side p)) =
        κ side * innerMorseChainCut T side (innerMorseInnerTailIndex N K side p) 1 := by
  rw [scaledMorseInnerChainGeometry_left, scaledMorseInnerChainGeometry_right,
    scaledMorseInnerModelCuts_tail, scaledMorseInnerModelCuts_tail]
  exact ⟨rfl, rfl⟩

end OrderedCuts

end ContinuousFlexibility.Radial
