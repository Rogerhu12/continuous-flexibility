import ContinuousFlexibility.Radial.InnerSelectedPhysicalGeometry

/-!
# Every finite chain in the selected physical reference

The model array has the original left-tail order, the central cut model
and the original right-tail order. Each tail uses its own physical scale.
The two exterior cuts are defined by the same selected joins at N+K,
including the actual first join when K=0.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set ContinuousFlexibility.Statements

namespace InnerSelectedPhysicalGeometry

variable {S : SelectedTailData} {D : ReferenceData} {X₀ : ℝ}
  (P : InnerSelectedPhysicalGeometry S D X₀)

def centerCuts (_P : InnerSelectedPhysicalGeometry S D X₀) (i : Fin 2) : ℝ :=
  if i = 0 then centralRadius (-X₀) else centralRadius X₀

@[simp] theorem centerCuts_zero : P.centerCuts 0 = centralRadius (-X₀) := by
  simp only [centerCuts, ite_true]

@[simp] theorem centerCuts_one : P.centerCuts 1 = centralRadius X₀ := by
  simp only [centerCuts, show (1 : Fin 2) ≠ 0 by decide, ite_false]

def modelCuts (K : ℕ) (p : Fin (2 * K + 1)) (i : Fin 2) : ℝ :=
  if p.val < K then
    P.radiusScale false * innerMorseChainCut S.chain false (S.chain.index + (K - 1 - p.val)) i
  else if p.val = K then P.centerCuts i
  else
    P.radiusScale true * innerMorseChainCut S.chain true (S.chain.index + (p.val - K - 1)) i

def outerPoint (K : ℕ) (side : Bool) : ℝ :=
  P.radiusScale side * S.joinInner side (S.chain.index + K)

theorem outerPoint_zero (side : Bool) :
    P.outerPoint 0 side = P.radiusScale side * S.joinInner side S.chain.index := by
  simp only [outerPoint, Nat.add_zero]

theorem outerPoint_pos {K : ℕ} (hK : 0 < K) (side : Bool) :
    P.outerPoint K side =
      P.radiusScale side * innerMorseInnerOuterPoint S.chain S.chain.index K side := by
  rw [outerPoint, P.laterJoin side K hK]

theorem outerPoint_core (K : ℕ) (side : Bool) : P.outerPoint K side ∈ radialCore D := by
  by_cases hK : K = 0
  · subst K
    rw [P.outerPoint_zero]
    exact P.firstJoin_core side
  · rw [P.outerPoint_pos (Nat.pos_of_ne_zero hK)]
    have hm : S.chain.index ≤ S.chain.index + (K - 1) := Nat.le_add_right _ _
    have hd := P.realization.retained_data side _ hm
    have hab := (hd.2.2.2.1.trans hd.2.2.2.2.1).le
    apply P.retained_core side hm
    cases side with
    | false => exact left_mem_Icc.mpr hab
    | true => exact right_mem_Icc.mpr hab

theorem modelCuts_center (K : ℕ) (i : Fin 2) :
    P.modelCuts K (innerMorseInnerCenter K) i = P.centerCuts i := by
  simp only [modelCuts, innerMorseInnerCenter, lt_self_iff_false, ite_false, ite_true]

theorem modelCuts_tail (K : ℕ) (side : Bool) (p : Fin K) (i : Fin 2) :
    P.modelCuts K (innerMorseInnerTailSlot K side p) i =
      P.radiusScale side *
        innerMorseChainCut S.chain side (innerMorseInnerTailIndex S.chain.index K side p) i := by
  cases side with
  | false =>
    simp only [innerMorseInnerTailSlot, innerMorseInnerTailIndex, Bool.false_eq_true,
      ite_false, modelCuts, p.isLt, ite_true]
  | true =>
    have hlt : ¬K + 1 + p.val < K := by omega
    have hne : K + 1 + p.val ≠ K := by omega
    have heq : K + 1 + p.val - K - 1 = p.val := by omega
    simp only [innerMorseInnerTailSlot, innerMorseInnerTailIndex, ite_true,
      modelCuts, hlt, hne, ite_false, heq]

theorem modelCuts_order (K : ℕ) (p : Fin (2 * K + 1)) :
    P.modelCuts K p 0 < P.modelCuts K p 1 := by
  rcases innerMorseInnerModel_cases K p with rfl | ⟨side, q, rfl⟩
  · rw [P.modelCuts_center, P.modelCuts_center, P.centerCuts_zero, P.centerCuts_one]
    exact P.center_order
  · rw [P.modelCuts_tail, P.modelCuts_tail]
    exact mul_lt_mul_of_pos_left
      (innerMorseChainCut_geometry P.realization side
        (innerMorseInnerTailIndex_bounds S.chain.index K side q).1).2.1
      (P.radiusScale_pos side)

private theorem firstCut_order (side : Bool) {m : ℕ} (hm : S.chain.index ≤ m) :
    if side then
      P.radiusScale side * innerMorseChainCut S.chain side S.chain.index 0 ≤
        P.radiusScale side * innerMorseChainCut S.chain side m 0
    else
      P.radiusScale side * innerMorseChainCut S.chain side m 1 ≤
        P.radiusScale side * innerMorseChainCut S.chain side S.chain.index 1 := by
  rcases hm.eq_or_lt with rfl | hm
  · cases side <;> exact le_rfl
  · have hs := innerMorseChain_models_separated P.realization side le_rfl hm
    have hc := (innerMorseChainCut_geometry P.realization side le_rfl).2.1
    cases side with
    | false =>
      exact mul_le_mul_of_nonneg_left (hs.trans hc).le (P.radiusScale_pos false).le
    | true =>
      exact mul_le_mul_of_nonneg_left (hc.trans hs).le (P.radiusScale_pos true).le

theorem modelCuts_separated (K : ℕ) (p q : Fin (2 * K + 1)) (hpq : p < q) :
    P.modelCuts K p 1 < P.modelCuts K q 0 := by
  have hpq' : p.val < q.val := hpq
  have hc : P.centerCuts 0 < P.centerCuts 1 := P.center_order
  have hcl : P.radiusScale false * innerMorseChainCut S.chain false S.chain.index 1 <
      P.centerCuts 0 := P.middle_order false
  have hcr : P.centerCuts 1 <
      P.radiusScale true * innerMorseChainCut S.chain true S.chain.index 0 :=
    P.middle_order true
  by_cases hp : p.val < K
  · by_cases hq : q.val < K
    · have hidx : S.chain.index + (K - 1 - q.val) <
          S.chain.index + (K - 1 - p.val) := by omega
      have hs := mul_lt_mul_of_pos_left
        (innerMorseChain_models_separated P.realization false (Nat.le_add_right _ _) hidx)
        (P.radiusScale_pos false)
      simpa only [modelCuts, hp, hq, ite_true, Bool.false_eq_true, ite_false] using hs
    · have hl := (P.firstCut_order false (Nat.le_add_right S.chain.index (K - 1 - p.val))).trans_lt hcl
      by_cases hq0 : q.val = K
      · simpa only [modelCuts, hp, hq, hq0, lt_self_iff_false, ite_true, ite_false] using hl
      · have hr := hcr.trans_le
          (P.firstCut_order true (Nat.le_add_right S.chain.index (q.val - K - 1)))
        simpa only [modelCuts, hp, hq, hq0, ite_true, ite_false] using hl.trans (hc.trans hr)
  · have hq : ¬q.val < K := by omega
    have hq0 : q.val ≠ K := by omega
    by_cases hp0 : p.val = K
    · have hr := hcr.trans_le
        (P.firstCut_order true (Nat.le_add_right S.chain.index (q.val - K - 1)))
      simpa only [modelCuts, hp, hq, hp0, hq0, lt_self_iff_false, ite_true, ite_false] using hr
    · have hidx : S.chain.index + (p.val - K - 1) <
          S.chain.index + (q.val - K - 1) := by omega
      have hs := mul_lt_mul_of_pos_left
        (innerMorseChain_models_separated P.realization true (Nat.le_add_right _ _) hidx)
        (P.radiusScale_pos true)
      simpa only [modelCuts, hp, hq, hp0, hq0, ite_true, ite_false] using hs

theorem outer_bounds (K : ℕ) :
    P.outerPoint K false < P.outerPoint K true ∧
      (∀ p, P.outerPoint K false < P.modelCuts K p 0) ∧
      ∀ p, P.modelCuts K p 1 < P.outerPoint K true := by
  have hm : S.chain.index ≤ S.chain.index + (K - 1) := Nat.le_add_right _ _
  have hfirst : P.outerPoint K false < P.modelCuts K 0 0 := by
    by_cases hK : K = 0
    · subst K
      simpa only [outerPoint, Nat.add_zero, modelCuts, Fin.val_zero,
        lt_self_iff_false, ite_false, ite_true, centerCuts_zero] using P.center_left
    · have hKpos := Nat.pos_of_ne_zero hK
      rw [P.outerPoint_pos hKpos]
      simpa only [innerMorseInnerOuterPoint, Bool.false_eq_true, ite_false,
        modelCuts, Fin.val_zero, hKpos, ite_true, Nat.sub_zero] using
        mul_lt_mul_of_pos_left (innerMorseChainCut_geometry P.realization false hm).1
          (P.radiusScale_pos false)
  have hlast : P.modelCuts K (Fin.last (2 * K)) 1 < P.outerPoint K true := by
    by_cases hK : K = 0
    · subst K
      simpa only [outerPoint, Nat.add_zero, modelCuts, Fin.val_last, Nat.mul_zero,
        lt_self_iff_false, ite_false, ite_true, centerCuts_one] using P.center_right
    · have hKpos := Nat.pos_of_ne_zero hK
      have hlt : ¬2 * K < K := by omega
      have hne : 2 * K ≠ K := by omega
      have hidx : 2 * K - K - 1 = K - 1 := by omega
      rw [P.outerPoint_pos hKpos]
      simpa only [innerMorseInnerOuterPoint, ite_true, modelCuts,
        Fin.val_last, hlt, hne, ite_false, hidx] using
        mul_lt_mul_of_pos_left (innerMorseChainCut_geometry P.realization true hm).2.2.1
          (P.radiusScale_pos true)
  have hleft (p : Fin (2 * K + 1)) : P.outerPoint K false < P.modelCuts K p 0 := by
    by_cases hp : p = 0
    · simpa only [hp] using hfirst
    · exact hfirst.trans ((P.modelCuts_order K 0).trans
        (P.modelCuts_separated K 0 p (lt_of_le_of_ne (Fin.zero_le p) (Ne.symm hp))))
  have hright (p : Fin (2 * K + 1)) : P.modelCuts K p 1 < P.outerPoint K true := by
    by_cases hp : p = Fin.last (2 * K)
    · simpa only [hp] using hlast
    · exact (P.modelCuts_separated K p (Fin.last (2 * K))
        (lt_of_le_of_ne (Fin.le_last p) hp)).trans
        ((P.modelCuts_order K (Fin.last (2 * K))).trans hlast)
  exact ⟨(hleft 0).trans ((P.modelCuts_order K 0).trans (hright 0)), hleft, hright⟩

/-- The one actual finite chain, defined for every K including zero. -/
def chain (K : ℕ) : InnerRadialChainGeometry D (2 * (2 * K + 1)) :=
  innerRadialChainOfModels D P.geometry (P.modelCuts K)
    (P.outerPoint K false) (P.outerPoint K true)
    (P.outerPoint_core K false) (P.outerPoint_core K true)
    (P.outer_bounds K).1 (P.modelCuts_order K) (P.modelCuts_separated K)
    (P.outer_bounds K).2.1 (P.outer_bounds K).2.2

theorem model_left (K : ℕ) (p : Fin (2 * K + 1)) :
    (P.chain K).left (innerModelChainPiece p) = P.modelCuts K p 0 :=
  innerModelChainCuts_model_left (P.modelCuts K) (P.outerPoint K false) (P.outerPoint K true) p

theorem model_right (K : ℕ) (p : Fin (2 * K + 1)) :
    (P.chain K).right (innerModelChainPiece p) = P.modelCuts K p 1 :=
  innerModelChainCuts_model_right (P.modelCuts K) (P.outerPoint K false) (P.outerPoint K true) p

theorem center_left_cut (K : ℕ) :
    (P.chain K).left (innerModelChainPiece (innerMorseInnerCenter K)) = centralRadius (-X₀) := by
  rw [P.model_left, P.modelCuts_center, P.centerCuts_zero]

theorem center_right_cut (K : ℕ) :
    (P.chain K).right (innerModelChainPiece (innerMorseInnerCenter K)) = centralRadius X₀ := by
  rw [P.model_right, P.modelCuts_center, P.centerCuts_one]

theorem tail_left (K : ℕ) (side : Bool) (p : Fin K) :
    (P.chain K).left (innerModelChainPiece (innerMorseInnerTailSlot K side p)) =
      P.radiusScale side *
        innerMorseChainCut S.chain side (innerMorseInnerTailIndex S.chain.index K side p) 0 := by
  rw [P.model_left, P.modelCuts_tail]

theorem tail_right (K : ℕ) (side : Bool) (p : Fin K) :
    (P.chain K).right (innerModelChainPiece (innerMorseInnerTailSlot K side p)) =
      P.radiusScale side *
        innerMorseChainCut S.chain side (innerMorseInnerTailIndex S.chain.index K side p) 1 := by
  rw [P.model_right, P.modelCuts_tail]

theorem outer_left (K : ℕ) :
    (P.chain K).left 0 =
      P.radiusScale false * S.joinInner false (S.chain.index + K) := by
  change innerModelChainCuts (P.modelCuts K) (P.outerPoint K false) (P.outerPoint K true)
    (0 : Fin (2 * (2 * K + 1) + 1)).castSucc = _
  rw [Fin.castSucc_zero, innerModelChainCuts_first]
  rfl

theorem outer_right (K : ℕ) :
    (P.chain K).right (Fin.last (2 * (2 * K + 1))) =
      P.radiusScale true * S.joinInner true (S.chain.index + K) := by
  change innerModelChainCuts (P.modelCuts K) (P.outerPoint K false) (P.outerPoint K true)
    (Fin.last (2 * (2 * K + 1))).succ = _
  rw [Fin.succ_last, innerModelChainCuts_last]
  rfl

theorem gap_left (K : ℕ) (g : Fin (2 * K + 2)) :
    (P.chain K).left (innerModelChainGap g) =
      if hg : 0 < g.val then P.modelCuts K ⟨g.val - 1, by omega⟩ 1
      else P.outerPoint K false :=
  innerModelChainCuts_gap_left (P.modelCuts K) (P.outerPoint K false) (P.outerPoint K true) g

theorem gap_right (K : ℕ) (g : Fin (2 * K + 2)) :
    (P.chain K).right (innerModelChainGap g) =
      if hg : g.val < 2 * K + 1 then P.modelCuts K ⟨g.val, hg⟩ 0
      else P.outerPoint K true :=
  innerModelChainCuts_gap_right (P.modelCuts K) (P.outerPoint K false) (P.outerPoint K true) g

end InnerSelectedPhysicalGeometry

end ContinuousFlexibility.Radial
