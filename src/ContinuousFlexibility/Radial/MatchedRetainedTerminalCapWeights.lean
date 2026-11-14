module

public import ContinuousFlexibility.Radial.MatchedMorsePieceWeights
public import ContinuousFlexibility.Radial.MatchedMorseNearWeights
public import ContinuousFlexibility.Radial.InnerPhysicalSourceBridge
public import ContinuousFlexibility.Radial.RetainedMorseInnerGeometry
public import ContinuousFlexibility.Radial.SelectedLaterCapData
public import ContinuousFlexibility.Radial.TerminalMorseCutoffGeometry

/-!
# The original finite-chain weight on the complete terminal cap

A complete cap meets the terminal gap and the adjacent outermost model.
Both pieces carry the preceding cell index. The estimate below includes
both pieces and retains the signed action at the actual transition index.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory ContinuousFlexibility.Statements

theorem matchedMorse_terminal_pieceIndex (N K : ℕ) (hK : 0 < K)
    (p : Fin (2 * (2 * K + 1) + 1))
    (hp : p.val ≤ 1 ∨ 4 * K + 1 ≤ p.val) :
    innerMorseInnerPieceIndex N K p = N + (K - 1) := by
  rcases innerModelChainPiece_or_gap p with ⟨q, rfl⟩ | ⟨g, rfl⟩
  · rw [innerMorseInnerPieceIndex_model]
    change 2 * q.val + 1 ≤ 1 ∨ 4 * K + 1 ≤ 2 * q.val + 1 at hp
    unfold innerMorseInnerModelIndex
    split_ifs <;> omega
  · rw [innerMorseInnerPieceIndex_gap]
    change 2 * g.val ≤ 1 ∨ 4 * K + 1 ≤ 2 * g.val at hp
    unfold innerMorseInnerGapIndex
    split_ifs <;> omega

/-- This neighborhood is the union of the actual terminal gap and the
adjacent actual model. No constancy on the whole cap is required. -/
theorem matchedMorse_terminal_neighborhood_weight_bound {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (N K : ℕ) (hK : 0 < K) (hN : 4096 ≤ N)
    (G : InnerRadialChainGeometry D (2 * (2 * K + 1)))
    (l r : Fin (2 * (2 * K + 1) + 1) → ℝ) (side : Bool) {cap : Set ℝ}
    (hcap : cap ⊆ if side then
      Icc (G.left (innerModelChainPiece (Fin.last (2 * K))))
        (G.right (Fin.last (2 * (2 * K + 1))))
      else Icc (G.left 0) (G.right (innerModelChainPiece (0 : Fin (2 * K + 1)))))
    {σ : ℝ} (hσ : |σ| ≤ 1) :
    ∀ᵐ x ∂radialHilbertMeasure D, x ∈ cap →
      |(innerMorseInnerWeight N K 0 1 G l r x) ^ σ| ≤
        exp (radialS N) * exp (41414 * radialQ (N + K) + σ * radialS (N + K)) := by
  filter_upwards [innerRadialChainRegion_ae hD G, matching_ae_ne hD (G.left 0),
    matching_ae_ne hD (G.right (Fin.last (2 * (2 * K + 1))))] with x hx hL hR hxc
  have hc := hcap hxc
  have hwhole : x ∈ Ioo (G.left 0) (G.right (Fin.last (2 * (2 * K + 1)))) := by
    cases side
    · simp only [Bool.false_eq_true, ite_false] at hc
      have hr : G.right (innerModelChainPiece (0 : Fin (2 * K + 1))) ≤
          G.right (Fin.last (2 * (2 * K + 1))) :=
        G.increasing.monotone (by
          apply Fin.le_iff_val_le_val.mpr
          simp only [Fin.val_succ, Fin.val_last, innerModelChainPiece, Fin.val_zero]
          omega)
      exact ⟨lt_of_le_of_ne hc.1 hL.symm, lt_of_le_of_ne (hc.2.trans hr) hR⟩
    · simp only [ite_true] at hc
      have hl : G.left 0 ≤ G.left (innerModelChainPiece (Fin.last (2 * K))) :=
        G.increasing.monotone (by
          apply Fin.le_iff_val_le_val.mpr
          simp only [Fin.val_castSucc, Fin.val_zero]
          exact Nat.zero_le _)
      exact ⟨lt_of_le_of_ne (hl.trans hc.1) hL.symm, lt_of_le_of_ne hc.2 hR⟩
  obtain ⟨p, hp⟩ := Set.mem_iUnion.mp (hx.mpr hwhole)
  have hext : p.val ≤ 1 ∨ 4 * K + 1 ≤ p.val := by
    cases side
    · simp only [Bool.false_eq_true, ite_false] at hc
      left
      by_contra hn
      have hle : G.right (innerModelChainPiece (0 : Fin (2 * K + 1))) ≤ G.left p :=
        G.increasing.monotone (by
          apply Fin.le_iff_val_le_val.mpr
          simp only [Fin.val_succ, Fin.val_castSucc, innerModelChainPiece, Fin.val_zero]
          omega)
      exact (not_lt_of_ge (hc.2.trans hle)) hp.1
    · simp only [ite_true] at hc
      right
      by_contra hn
      have hle : G.right p ≤ G.left (innerModelChainPiece (Fin.last (2 * K))) :=
        G.increasing.monotone (by
          apply Fin.le_iff_val_le_val.mpr
          simp only [Fin.val_succ, Fin.val_castSucc, innerModelChainPiece, Fin.val_last]
          omega)
      exact (not_lt_of_ge (hle.trans hc.1)) hp.2
  have hb := (matchedMorse_actual_piece_exp_bounds N K hK hN G l r hσ p hp).1
  rw [matchedMorse_terminal_pieceIndex N K hK p hext] at hb
  have hn := matchedMorse_piece_exp_near (n := N + K) (m := N + (K - 1))
    (b := (38 : ℝ)) (by omega) (by omega) (by omega) (by norm_num) hσ
  norm_num only at hn
  exact hb.trans (mul_le_mul_of_nonneg_left hn (exp_pos _).le)

theorem matchedMorse_cap_inner_end_bound {T : MorseChainData} {τ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ} (h : MorseChainRealization T τ D C)
    (side : Bool) {m : ℕ} (hm : T.index ≤ m) :
    if side then innerMorseChainCut T side m 0 ≤
      T.radius side m (morseRightTurn (morseChainA T m) (morseChainB T m))
    else T.radius side m morseShortLeftCapCut ≤ innerMorseChainCut T side m 1 := by
  obtain ⟨hB, hAB, _, _, _, _, _⟩ := h.retained_data side m hm
  obtain ⟨hl, hr⟩ := innerMorseChain_retained_endpoints h side hm
  have hA := (mul_pos (by norm_num : (0 : ℝ) < 4) hB).trans hAB
  have hshort := morseCellLeftCut_lt_shortLeftCapCut
  have hturn := (morseShortLeftCapCut_lt_leftTurn hB hAB).trans (morseTurn_order hB hAB)
  have hlong := morseRightCapLength_pos hA (by norm_num : (0 : ℝ) < 1 / 100)
  have hcuts := innerMorseBuffer_cut_order hB hAB
  have hmono := (h.radius_strictMonoOn side m hm).monotoneOn
  have hmem (x : ℝ) (hx : x ∈ Icc morseCellLeftCut
      (morseRightCapEnd (morseChainA T m) (morseChainB T m) (1 / 100))) :
      x ∈ Icc (T.leftX side m) (T.rightX side m) := by simpa only [hl, hr] using hx
  cases side
  · simp only [Bool.false_eq_true, ite_false, innerMorseChainCut_one]
    apply hmono
    · apply hmem
      exact ⟨hshort.le, hturn.le.trans (le_add_of_nonneg_right hlong.le)⟩
    · exact hmem _ ⟨(hcuts.1.trans hcuts.2.1).le, hcuts.2.2.le⟩
    · dsimp only [innerMorseBufferRightCut]
      linarith only [hturn, hlong]
  · simp only [ite_true, innerMorseChainCut_zero]
    apply hmono
    · exact hmem _ ⟨hcuts.1.le, (hcuts.2.1.trans hcuts.2.2).le⟩
    · exact hmem _ ⟨(hshort.trans hturn).le, le_add_of_nonneg_right hlong.le⟩
    · dsimp only [innerMorseBufferLeftCut]
      linarith only [hshort, hturn]

namespace SeedRetainedPair

variable {S : SelectedTailData} {K : SeedCentralCutoff} {q length T : ℝ}
  (P : SeedRetainedPair S K q length) {Γ : ConnectedReferenceGeometry}
  (hD : RadialProfileGeometry Γ.reference) (hw : Γ.reference.w = P.pair.profile)
  (hS : IsSelectedTail S) (G₀ : MorseChainGeometryWitness S.chain)
  (hfirst : radialFrequencyBand S.chain S.Cstar S.chain.index 2)
  (hq : 0 < q) (hT : 0 < T)
  (hleft : Γ.centralLeft = exp K.left) (hright : Γ.centralRight = exp K.right)
  (hTL : Γ.centralLeft < centralRadius (-T)) (hTR : centralRadius T < Γ.centralRight)
  (k : ℕ) (hk : 0 < k)

local notation "H" => P.retainedMorseInnerGeometry hD hw hS G₀ hfirst hq hT
  hleft hright hTL hTR k hk

/-- The complete physical cap lies in the last two pieces, not merely
in the terminal gap. This is the same radius chart used by the cutoff. -/
theorem retainedMorse_terminal_cap_subset (side : Bool) :
    let m := S.chain.index + (k - 1)
    let A := morseChainA S.chain m
    let B := morseChainB S.chain m
    let r := G₀.normal (k - 1)
    let s := P.sideRadius side * G₀.factor side (k - 1)
    Icc (terminalMorseLayerRadius side A B s r 0)
        (terminalMorseLayerRadius side A B s r (terminalMorseLayerLength side A)) ⊆
      if side then Icc ((H).left (innerModelChainPiece (Fin.last (2 * k))))
        ((H).right (Fin.last (2 * (2 * k + 1))))
      else Icc ((H).left 0) ((H).right (innerModelChainPiece (0 : Fin (2 * k + 1)))) := by
  let m := S.chain.index + (k - 1)
  have hreal := (hS.2.2.2.1 S.sigma hS.2.2.1).1
  have hinner := matchedMorse_cap_inner_end_bound hreal side
    (show S.chain.index ≤ m from Nat.le_add_right _ _)
  have hrad (x : ℝ) :
      (P.sideRadius side * G₀.factor side (k - 1)) * G₀.normal (k - 1) x =
        P.sideRadius side * S.chain.radius side m x := by
    rw [G₀.radius_eq side (k - 1)]
    ring
  have hcap := terminalMorseCap_endpoints side (morseChainA S.chain m)
    (morseChainB S.chain m) (P.sideRadius side * G₀.factor side (k - 1))
    (G₀.normal (k - 1))
  rw [hrad, hrad] at hcap
  have hterminal := P.retainedMorseInnerGeometry_terminal hD hw hS G₀ hfirst hq hT
    hleft hright hTL hTR k hk side
  cases side with
  | false =>
    have htail := P.retainedMorseInnerGeometry_tail hD hw hS G₀ hfirst hq hT
      hleft hright hTL hTR k hk false (⟨0, hk⟩ : Fin k)
    have hslot : innerMorseInnerTailSlot k false (⟨0, hk⟩ : Fin k) = 0 := by
      apply Fin.ext
      simp only [innerMorseInnerTailSlot, Bool.false_eq_true, ite_false, Fin.val_zero]
    have hgap : innerModelChainGap (innerMorseTerminalGapSlot k false) = 0 := by
      apply Fin.ext
      simp only [innerModelChainGap, innerMorseTerminalGapSlot, Bool.false_eq_true,
        ite_false, Fin.val_zero, mul_zero]
    simp only [innerMorseInnerTailIndex, Bool.false_eq_true, ite_false, Nat.sub_zero,
      hslot] at htail
    simp only [hgap, innerMorseOuterCapStart, innerMorseOuterCapEnd,
      Bool.false_eq_true, ite_false] at hterminal
    simp only [Bool.false_eq_true, ite_false] at hcap hinner ⊢
    apply Icc_subset_Icc
    · exact (hterminal.1.trans hcap.1.symm).le
    · exact hcap.2.le.trans
        ((mul_le_mul_of_nonneg_left hinner (P.sideRadius_pos false).le).trans_eq htail.2.symm)
  | true =>
    let p : Fin k := ⟨k - 1, by omega⟩
    have htail := P.retainedMorseInnerGeometry_tail hD hw hS G₀ hfirst hq hT
      hleft hright hTL hTR k hk true p
    have hslot : innerMorseInnerTailSlot k true p = Fin.last (2 * k) := by
      apply Fin.ext
      simp only [innerMorseInnerTailSlot, ite_true, Fin.val_last]
      dsimp only [p]
      omega
    have hgap : innerModelChainGap (innerMorseTerminalGapSlot k true) =
        Fin.last (2 * (2 * k + 1)) := by
      apply Fin.ext
      simp only [innerModelChainGap, innerMorseTerminalGapSlot, ite_true, Fin.val_last]
    simp only [innerMorseInnerTailIndex, ite_true, hslot] at htail
    change (H).left (innerModelChainPiece (Fin.last (2 * k))) =
      P.sideRadius true * innerMorseChainCut S.chain true m 0 ∧ _ at htail
    simp only [hgap, innerMorseOuterCapStart, innerMorseOuterCapEnd, ite_true] at hterminal
    simp only [ite_true] at hcap hinner ⊢
    apply Icc_subset_Icc
    · exact htail.1.le.trans
        ((mul_le_mul_of_nonneg_left hinner (P.sideRadius_pos true).le).trans_eq hcap.1.symm)
    · exact (hcap.2.trans hterminal.2.symm).le

theorem retainedMorse_terminal_cap_weight_bound
    (hAcc : IsAccumulatingProfile Γ.reference) (hN : 4096 ≤ S.chain.index)
    (l r : Fin (2 * (2 * k + 1) + 1) → ℝ) (side : Bool)
    {σ : ℝ} (hσ : |σ| ≤ 1) :
    let m := S.chain.index + (k - 1)
    let A := morseChainA S.chain m
    let B := morseChainB S.chain m
    let radius := G₀.normal (k - 1)
    let s := P.sideRadius side * G₀.factor side (k - 1)
    ∀ᵐ x ∂radialHilbertMeasure Γ.reference,
      x ∈ Icc (terminalMorseLayerRadius side A B s radius 0)
        (terminalMorseLayerRadius side A B s radius (terminalMorseLayerLength side A)) →
      |(innerMorseInnerWeight S.chain.index k 0 1 H l r x) ^ σ| ≤
        exp (radialS S.chain.index) *
          exp (41414 * radialQ (S.chain.index + k) + σ * radialS (S.chain.index + k)) :=
  matchedMorse_terminal_neighborhood_weight_bound hAcc S.chain.index k hk hN H l r side
    (P.retainedMorse_terminal_cap_subset hD hw hS G₀ hfirst hq hT
      hleft hright hTL hTR k hk side) hσ

end SeedRetainedPair

end ContinuousFlexibility.Radial
