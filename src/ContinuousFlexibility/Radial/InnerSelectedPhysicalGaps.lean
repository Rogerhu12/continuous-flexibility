module

public import ContinuousFlexibility.Radial.InnerSelectedPhysicalChain
public import ContinuousFlexibility.Radial.InnerSelectedPhysicalSlope

/-!
# Uniform gaps on every selected physical inner chain

The complete gap list is identified with its actual physical endpoints.
At K=0 its two gaps are subintervals of the same fixed full middle
connectors. For later bands the other pieces are exactly scaled terminal
caps or scaled cap-join-cap intervals. One previously chosen geometric
constant therefore controls every gap, before selecting a frequency.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set ContinuousFlexibility.Statements

namespace InnerSelectedPhysicalGeometry

variable {S : SelectedTailData} {D : ReferenceData} {X₀ : ℝ}
  (P : InnerSelectedPhysicalGeometry S D X₀)

theorem gap_terminal {K : ℕ} (hK : 0 < K) (side : Bool) :
    (P.chain K).left (innerModelChainGap (innerMorseTerminalGapSlot K side)) =
      P.radiusScale side * S.chain.radius side (S.chain.index + (K - 1))
        (innerMorseOuterCapStart (morseChainA S.chain (S.chain.index + (K - 1)))
          (morseChainB S.chain (S.chain.index + (K - 1))) side) ∧
    (P.chain K).right (innerModelChainGap (innerMorseTerminalGapSlot K side)) =
      P.radiusScale side * S.chain.radius side (S.chain.index + (K - 1))
        (innerMorseOuterCapEnd (morseChainA S.chain (S.chain.index + (K - 1)))
          (morseChainB S.chain (S.chain.index + (K - 1))) side) := by
  have hm : S.chain.index ≤ S.chain.index + (K - 1) := Nat.le_add_right _ _
  obtain ⟨hl, hr⟩ := innerMorseChain_retained_endpoints P.realization side hm
  rw [P.gap_left, P.gap_right]
  cases side with
  | false =>
    constructor <;> simp only [innerMorseTerminalGapSlot, Bool.false_eq_true, ite_false,
      Fin.val_zero, lt_self_iff_false, dite_false, Nat.zero_lt_succ, dite_true,
      modelCuts, hK, ite_true, Nat.sub_zero, P.outerPoint_pos hK,
      innerMorseInnerOuterPoint, innerMorseOuterCapStart, innerMorseOuterCapEnd,
      innerMorseChainCut_zero, hl]
  | true =>
    have hlt : ¬2 * K < K := by omega
    have hne : 2 * K ≠ K := by omega
    have hidx : 2 * K - K - 1 = K - 1 := by omega
    constructor <;> simp only [innerMorseTerminalGapSlot, ite_true, Fin.val_last,
      Nat.zero_lt_succ, lt_self_iff_false, dite_true, dite_false, Nat.add_one_sub_one,
      modelCuts, hlt, hne, ite_false, hidx, P.outerPoint_pos hK,
      innerMorseInnerOuterPoint, innerMorseOuterCapStart, innerMorseOuterCapEnd,
      innerMorseChainCut_one, hr]

theorem gap_middle {K : ℕ} (hK : 0 < K) (side : Bool) :
    (P.chain K).left (innerModelChainGap (innerMorseMiddleGapSlot K side)) =
      P.middleLeft side ∧
    (P.chain K).right (innerModelChainGap (innerMorseMiddleGapSlot K side)) =
      P.middleRight side := by
  have hg0 : 0 < (innerMorseMiddleGapSlot K side).val := by
    cases side <;> simp only [innerMorseMiddleGapSlot, Bool.false_eq_true, ite_false, ite_true] <;>
      omega
  have hgm : (innerMorseMiddleGapSlot K side).val < 2 * K + 1 := by
    cases side <;> simp only [innerMorseMiddleGapSlot, Bool.false_eq_true, ite_false, ite_true] <;>
      omega
  rw [P.gap_left, P.gap_right, dif_pos hg0, dif_pos hgm]
  cases side with
  | false =>
    have hprev : K - 1 < K := by omega
    constructor <;> simp only [innerMorseMiddleGapSlot, Bool.false_eq_true, ite_false,
      middleLeft, middleRight, modelCuts, hprev, ite_true, Nat.sub_self, Nat.add_zero,
      lt_self_iff_false, centerCuts_zero]
  | true =>
    have hnext : ¬K + 1 < K := by omega
    have hnextne : K + 1 ≠ K := by omega
    constructor <;> simp only [innerMorseMiddleGapSlot, ite_true, middleLeft, middleRight,
      modelCuts, Nat.add_one_sub_one, lt_self_iff_false, ite_false, hnext, hnextne,
      Nat.add_sub_cancel_left, Nat.sub_self, Nat.add_zero, centerCuts_one]

theorem gap_tail {K : ℕ} (side : Bool) (p : Fin (K - 1)) :
    (P.chain K).left (innerModelChainGap (innerMorseTailGapSlot K side p)) =
      P.radiusScale side * innerMorseTailGapLeft S.chain side
        (innerMorseTailGapCell S.chain.index K side p) ∧
    (P.chain K).right (innerModelChainGap (innerMorseTailGapSlot K side p)) =
      P.radiusScale side * innerMorseTailGapRight S.chain side
        (innerMorseTailGapCell S.chain.index K side p) := by
  have hg0 : 0 < (innerMorseTailGapSlot K side p).val := by
    cases side <;> simp only [innerMorseTailGapSlot, Bool.false_eq_true, ite_false, ite_true] <;>
      omega
  have hgm : (innerMorseTailGapSlot K side p).val < 2 * K + 1 := by
    cases side <;> simp only [innerMorseTailGapSlot, Bool.false_eq_true, ite_false, ite_true] <;>
      omega
  rw [P.gap_left, P.gap_right, dif_pos hg0, dif_pos hgm]
  cases side with
  | false =>
    have hp0 : p.val < K := by omega
    have hp1 : p.val + 1 < K := by omega
    have hidx0 : S.chain.index + (K - 1 - p.val) =
        S.chain.index + (K - 2 - p.val) + 1 := by omega
    have hidx1 : K - 1 - (p.val + 1) = K - 2 - p.val := by omega
    constructor <;> simp only [innerMorseTailGapSlot, innerMorseTailGapCell,
      Bool.false_eq_true, ite_false, innerMorseTailGapLeft, innerMorseTailGapRight,
      innerMorseTailDeparture, innerMorseTailArrival, modelCuts, Nat.add_one_sub_one,
      hp0, hp1, ite_true, hidx0, hidx1]
  | true =>
    have hp0 : ¬K + 2 + p.val - 1 < K := by omega
    have hp1 : ¬K + 2 + p.val < K := by omega
    have hne0 : K + 2 + p.val - 1 ≠ K := by omega
    have hne1 : K + 2 + p.val ≠ K := by omega
    have hidx0 : K + 2 + p.val - 1 - K - 1 = p.val := by omega
    have hidx1 : S.chain.index + (K + 2 + p.val - K - 1) =
        S.chain.index + p.val + 1 := by omega
    constructor <;> simp only [innerMorseTailGapSlot, innerMorseTailGapCell, ite_true,
      innerMorseTailGapLeft, innerMorseTailGapRight, innerMorseTailDeparture,
      innerMorseTailArrival, modelCuts, hp0, hp1, hne0, hne1, ite_false, hidx0, hidx1]

theorem gap_zero (g : Fin 2) :
    (P.chain 0).left (innerModelChainGap g) =
      (if g = 0 then P.outerPoint 0 false else centralRadius X₀) ∧
    (P.chain 0).right (innerModelChainGap g) =
      (if g = 0 then centralRadius (-X₀) else P.outerPoint 0 true) := by
  rw [P.gap_left, P.gap_right]
  rcases (show g = 0 ∨ g = 1 by omega) with rfl | rfl
  <;> constructor
  <;> simp only [Fin.val_zero, Fin.val_one, Nat.mul_zero, Nat.zero_add, Nat.add_zero,
    Nat.sub_self, Nat.sub_zero, lt_self_iff_false, Nat.zero_lt_succ,
    show (1 : Fin 2) ≠ 0 by decide, ite_true, ite_false, dite_true, dite_false,
    modelCuts, centerCuts_zero, centerCuts_one]

/-- Both first-band gaps lie in the fixed full middle connectors; the
selected first joins, not free head points, are their outer endpoints. -/
theorem gap_zero_subset (g : Fin 2) :
    ∃ side : Bool, Icc
      ((P.chain 0).left (innerModelChainGap g))
      ((P.chain 0).right (innerModelChainGap g)) ⊆
        Icc (P.middleLeft side) (P.middleRight side) := by
  rcases (show g = 0 ∨ g = 1 by omega) with rfl | rfl
  · refine ⟨false, ?_⟩
    intro r hr
    rw [(P.gap_zero 0).1, (P.gap_zero 0).2] at hr
    simp only [ite_true, P.outerPoint_zero] at hr
    exact ⟨(P.firstJoin_cut false).le.trans hr.1, hr.2⟩
  · refine ⟨true, ?_⟩
    intro r hr
    rw [(P.gap_zero 1).1, (P.gap_zero 1).2] at hr
    simp only [show (1 : Fin 2) ≠ 0 by decide, ite_false, P.outerPoint_zero] at hr
    exact ⟨hr.1, hr.2.trans (P.firstJoin_cut true).le⟩

/-- The same constant controls every closed physical gap, uniformly in
the number of retained cells and before selecting any frequency. -/
theorem gapSlope_lower (K : ℕ) (g : Fin (2 * K + 2)) :
    ∀ r ∈ Icc ((P.chain K).left (innerModelChainGap g))
      ((P.chain K).right (innerModelChainGap g)),
      P.gapSlope ≤ r * deriv D.w r / D.w r := by
  intro r hr
  cases K with
  | zero =>
    obtain ⟨side, hsub⟩ := P.gap_zero_subset g
    exact (P.gapSlope_le_middle side).trans (P.middleSlope_lower side r (hsub hr))
  | succ K =>
    rcases innerMorseInnerGap_cases (Nat.succ_pos K) g with
      ⟨side, rfl⟩ | ⟨side, rfl⟩ | ⟨side, p, rfl⟩
    · have he := P.gap_terminal (Nat.succ_pos K) side
      rw [he.1, he.2] at hr
      exact P.gapSlope_le_tail.trans
        (P.outerCap_slope side
          (Nat.le_add_right S.chain.index ((K + 1) - 1)) side r hr)
    · have he := P.gap_middle (Nat.succ_pos K) side
      rw [he.1, he.2] at hr
      exact (P.gapSlope_le_middle side).trans (P.middleSlope_lower side r hr)
    · have he := P.gap_tail (K := K + 1) side p
      rw [he.1, he.2] at hr
      have hm : S.chain.index ≤ innerMorseTailGapCell S.chain.index (K + 1) side p := by
        cases side <;>
          simp only [innerMorseTailGapCell, Bool.false_eq_true, ite_false, ite_true] <;> omega
      exact P.gapSlope_le_tail.trans (P.tailGap_slope side hm r hr)

/-- Actual positive-gap columns on the same all-band chain. Their ODE,
boundary values and common slope are all consequences of the raw data. -/
def gapChart (K : ℕ) (j : ℝ) (hj : 0 < j) (g : Fin (2 * K + 2)) :
    InnerRadialGapChart D (P.chain K) j
      (innerModelChainPiece (innerMorseInnerCenter K)) (innerModelChainGap g) :=
  innerRadialGapChartOfProfile D P.geometry (P.chain K) j
    (innerModelChainPiece (innerMorseInnerCenter K)) (innerModelChainGap g)
    (innerModelChainGap_ne_model g (innerMorseInnerCenter K))
    hj P.gapSlope_pos (P.gapSlope_lower K g)

end InnerSelectedPhysicalGeometry

end ContinuousFlexibility.Radial
