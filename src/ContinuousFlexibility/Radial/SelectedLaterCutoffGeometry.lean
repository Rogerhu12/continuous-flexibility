import ContinuousFlexibility.Radial.SelectedLaterCutoffBounds
import ContinuousFlexibility.Radial.FirstConeLayerSeparation
import ContinuousFlexibility.Radial.TerminalPhysicalCutoffGeometry

/-!
# The later terminal cutoffs on the same retained reference

The complete physical caps have the selected matching joins as their
outer endpoints. Their inner endpoints lie beyond the initial entries,
so the two cutoffs and the fixed central column have disjoint closed
supports. All equations use the retained pair's own radius dilations.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

theorem SeedRetainedPair.later_cap_endpoints {S : SelectedTailData}
    {K : SeedCentralCutoff} {q length : ℝ} (P : SeedRetainedPair S K q length)
    (G : MorseChainGeometryWitness S.chain) (side : Bool) {n : ℕ}
    (hn : S.chain.index < n)
    (hcut : S.cut side n = r07PreviousCellCut S.chain side (n - 1))
    (hjoin : S.joinInner side n = r07PreviousCellJoin S.chain side (n - 1)) :
    let A := morseChainA S.chain (n - 1)
    let B := morseChainB S.chain (n - 1)
    let r := G.normal (n - 1 - S.chain.index)
    let s := P.sideRadius side * G.factor side (n - 1 - S.chain.index)
    terminalMorseLayerRadius side A B s r 0 =
        (if side then P.sideRadius side * S.cut side n
          else P.sideRadius side * S.joinInner side n) ∧
      terminalMorseLayerRadius side A B s r (terminalMorseLayerLength side A) =
        (if side then P.sideRadius side * S.joinInner side n
          else P.sideRadius side * S.cut side n) := by
  have hm : S.chain.index ≤ n - 1 := by omega
  have he := G.scaled_previousCap_endpoints (P.sideRadius side) side hm
  rw [← hcut, ← hjoin] at he
  have hc := terminalMorseCap_endpoints side (morseChainA S.chain (n - 1))
    (morseChainB S.chain (n - 1))
    (P.sideRadius side * G.factor side (n - 1 - S.chain.index))
    (G.normal (n - 1 - S.chain.index))
  cases side
  · exact ⟨hc.1.trans he.2, hc.2.trans he.1⟩
  · exact ⟨hc.1.trans he.1, hc.2.trans he.2⟩

theorem SeedRetainedPair.later_matching_cap_order {S : SelectedTailData}
    {K : SeedCentralCutoff} {q length : ℝ} (P : SeedRetainedPair S K q length)
    (hS : IsSelectedTail S) (G : MorseChainGeometryWitness S.chain)
    (hentry : S.entry = r07CellEntry S.chain)
    (hfirst : radialFrequencyBand S.chain S.Cstar S.chain.index 2)
    (hq : 0 < q) {Γ : ConnectedReferenceGeometry}
    (hleft : Γ.centralLeft = exp K.left) (hright : Γ.centralRight = exp K.right)
    {n j : ℕ} (hn : S.chain.index < n) (hj : 2 ≤ j) (heven : Even j)
    (hband : radialFrequencyBand S.chain S.Cstar n j)
    (hcut : ∀ side, S.cut side n = r07PreviousCellCut S.chain side (n - 1)) :
    let cut := fun side => P.sideRadius side * S.joinInner side n
    let wall := fun side => P.sideRadius side * S.cut side n
    cut false < wall false ∧ wall false < Γ.centralLeft ∧
      Γ.centralLeft < Γ.centralRight ∧ Γ.centralRight < wall true ∧ wall true < cut true := by
  have horder (side : Bool) := (hS.2.2.2.2.2 side n j hj heven hband).2.2.2.2.1
  have hbase (side : Bool) :=
    (hS.2.2.2.2.2 side S.chain.index 2 le_rfl (by decide) hfirst).2.2.2.2.1
  have hret (side : Bool) := (selected_later_cut_join_entry_retained hS G hentry side
    hn hj heven hband (hcut side)).1
  obtain ⟨hLC, hCI, hIL, hLR, hRI, hIC, hCJ⟩ :=
    P.first_matching_order hS hfirst hq hleft hright
  refine ⟨mul_lt_mul_of_pos_left (horder false).2 (P.sideRadius_pos false), ?_,
    hLR, ?_, mul_lt_mul_of_pos_left (horder true).1 (P.sideRadius_pos true)⟩
  · exact (mul_lt_mul_of_pos_left ((hret false).2.trans (hbase false).1)
      (P.sideRadius_pos false)).trans (hLC.trans (hCI.trans hIL))
  · exact (hRI.trans (hIC.trans hCJ)).trans
      (mul_lt_mul_of_pos_left ((hbase true).2.trans (hret true).1) (P.sideRadius_pos true))

theorem SeedRetainedPair.later_cutoff_geometry {S : SelectedTailData}
    {K : SeedCentralCutoff} {q length : ℝ} (P : SeedRetainedPair S K q length)
    (hS : IsSelectedTail S) (G : MorseChainGeometryWitness S.chain)
    (hentry : S.entry = r07CellEntry S.chain)
    (hfirst : radialFrequencyBand S.chain S.Cstar S.chain.index 2)
    (hC : 1000 ≤ S.Cstar) (hq : 0 < q) {Γ : ConnectedReferenceGeometry} (hΓ : Γ.Realizes)
    (hw : Γ.reference.w = P.pair.profile)
    (hleft : Γ.centralLeft = exp K.left) (hright : Γ.centralRight = exp K.right)
    {n j : ℕ} (hn : S.chain.index < n) (hj : 2 ≤ j) (heven : Even j)
    (hband : radialFrequencyBand S.chain S.Cstar n j)
    (hcut : ∀ side, S.cut side n = r07PreviousCellCut S.chain side (n - 1))
    (hjoin : ∀ side, S.joinInner side n = r07PreviousCellJoin S.chain side (n - 1))
    (hu : ∀ side, ContDiff ℝ ∞ (S.incoming side j)) :
    let cut := fun side => P.sideRadius side * S.joinInner side n
    let χ := P.laterTerminalCutoff G n
    let U := fun side => radialRadiusScale (P.sideRadius side) 1 (S.incoming side j)
    let A := morseChainA S.chain (n - 1)
    let R := fun side => terminalMorseLayerRadius side A (morseChainB S.chain (n - 1))
      (P.sideRadius side * G.factor side (n - 1 - S.chain.index))
      (G.normal (n - 1 - S.chain.index))
    cut false < cut true ∧
      (∀ side, ContDiff ℝ ∞ (χ side)) ∧
      (∀ side, tsupport (deriv (χ side)) ⊆ Ioo (cut false) (cut true)) ∧
      Disjoint (tsupport (χ false)) (tsupport (χ true)) ∧
      (∀ side, Disjoint (tsupport (referenceColumn Γ.reference)) (tsupport (χ side))) ∧
      (∀ side, χ side =ᶠ[𝓝 (cut side)] fun _ => (1 : ℝ)) ∧
      (∀ side r, r ∈ Ioo (cut false) (cut true) → r ∈ Function.support (χ side) →
        radialJacobi ((j : ℝ) ^ 2) Γ.reference.w (U side) r = 0) ∧
      (∀ side, cut false ≤ R side 0 ∧
        R side (terminalMorseLayerLength side A) ≤ cut true) ∧
      ∀ side, Icc (R side 0) (R side (terminalMorseLayerLength side A)) ⊆
        Icc (cut false) (cut true) := by
  let A := morseChainA S.chain (n - 1)
  let B := morseChainB S.chain (n - 1)
  let r := G.normal (n - 1 - S.chain.index)
  let s := fun side => P.sideRadius side * G.factor side (n - 1 - S.chain.index)
  let R := fun side => terminalMorseLayerRadius side A B (s side) r
  let L := fun side => terminalMorseLayerLength side A
  let a := fun side => terminalMorseLayerLeft side A B (s side) r
  let b := fun side => terminalMorseLayerRight side A B (s side) r
  let cut := fun side => P.sideRadius side * S.joinInner side n
  let wall := fun side => P.sideRadius side * S.cut side n
  let χ := P.laterTerminalCutoff G n
  have hm : S.chain.index ≤ n - 1 := by omega
  have hk : S.chain.index + (n - 1 - S.chain.index) = n - 1 := Nat.add_sub_of_le hm
  have hr : IsNormalizedMorseCell A B r := by simpa only [hk] using G.model (n - 1 - S.chain.index)
  obtain ⟨hB, hAB, _, _, _⟩ := G.cell_terminal_parameters hm
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  have hs (side : Bool) : 0 < s side := mul_pos (P.sideRadius_pos side)
    (G.factorLo_pos.trans_le (G.factor_bounds side (n - 1 - S.chain.index)).1)
  have hends (side : Bool) : R side 0 = (if side then wall side else cut side) ∧
      R side (L side) = (if side then cut side else wall side) :=
    P.later_cap_endpoints G side hn (hcut side) (hjoin side)
  obtain ⟨hLC, hCL, hLR, hRC, hCJ⟩ :=
    P.later_matching_cap_order hS G hentry hfirst hq hleft hright hn hj heven hband hcut
  have hwall : wall false < wall true := hCL.trans (hLR.trans hRC)
  have hcuts : cut false < cut true := hLC.trans (hwall.trans hCJ)
  have hbounds (side : Bool) : cut false ≤ R side 0 ∧ R side (L side) ≤ cut true := by
    rw [(hends side).1, (hends side).2]
    cases side
    · exact ⟨le_rfl, (hwall.trans hCJ).le⟩
    · exact ⟨(hLC.trans hwall).le, le_rfl⟩
  have hab (side : Bool) : a side < b side := terminalMorseLayer_order side hB hAB (hs side) hr
  have hinside (side : Bool) : R side 0 < a side ∧ b side < R side (L side) := by
    have hL : 0 < L side := terminalMorseLayerLength_pos side hA
    have hmono := terminalMorseLayerRadius_strictMono side hB hAB (hs side) hr
    exact ⟨hmono ⟨le_rfl, hL.le⟩ ⟨by linarith only [hL], by linarith only [hL]⟩
      (by linarith only [hL]),
      hmono ⟨by linarith only [hL], by linarith only [hL]⟩ ⟨hL.le, le_rfl⟩
      (by linarith only [hL])⟩
  have hbL : b false < wall false := (hinside false).2.trans_eq (hends false).2
  have haR : wall true < a true := (hends true).1 ▸ (hinside true).1
  have hsep : b false < a true := hbL.trans (hwall.trans haR)
  have hcolumn : tsupport (referenceColumn Γ.reference) ⊆ Ioo (b false) (a true) := by
    intro x hx
    have hc := connectedReference_column_in_central hΓ hx
    exact ⟨hbL.trans (hCL.trans hc.1), hc.2.trans (hRC.trans haR)⟩
  have hcol := terminalPhysicalCutoffs_column_disjoint (hab false) (hab true) hcolumn
  refine ⟨hcuts, fun side => terminalMorsePhysicalCutoff_smooth side _ _ _ _, ?_,
    terminalPhysicalCutoffs_disjoint (hab false) hsep (hab true), ?_, ?_, ?_,
    hbounds, fun side => Icc_subset_Icc (hbounds side).1 (hbounds side).2⟩
  · intro side x hx
    have hd := terminalMorsePhysicalCutoff_derivative_inside_cap side hB hAB (hs side) hr hx
    exact ⟨(hbounds side).1.trans_lt hd.1, hd.2.trans_le (hbounds side).2⟩
  · intro side
    cases side
    · exact hcol.1
    · exact hcol.2
  · intro side
    have hg := terminalMorsePhysicalCutoff_join_germ side hB hAB (hs side) hr
    change χ side =ᶠ[𝓝 (if side then R side (L side) else R side 0)] fun _ => (1 : ℝ) at hg
    have he : (if side then R side (L side) else R side 0) = cut side := by
      cases side
      · exact (hends false).1
      · exact (hends true).2
    simpa only [he] using hg
  · intro side x hx hχ
    apply (P.reference_later_incoming_data hw hS G hentry hfirst hC side
      hn hj heven hband (hcut side) (hjoin side) (hu side)).2.2.2.2.1 x
    have ht := terminalPhysicalCutoff_support side (hab side) hχ
    have ho := (hS.2.2.2.2.2 side n j hj heven hband).2.2.2.2.1
    cases side
    · have he : P.sideRadius false * S.entry false n < cut false :=
        mul_lt_mul_of_pos_left ho.1 (P.sideRadius_pos false)
      rw [uIcc_of_ge (he.trans hLC).le]
      exact ⟨(he.trans hx.1).le, ht.le.trans hbL.le⟩
    · have he : cut true < P.sideRadius true * S.entry true n :=
        mul_lt_mul_of_pos_left ho.2 (P.sideRadius_pos true)
      rw [uIcc_of_le (hCJ.trans he).le]
      exact ⟨haR.le.trans ht.le, (hx.2.trans he).le⟩

end ContinuousFlexibility.Radial
