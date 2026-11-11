import ContinuousFlexibility.Radial.SelectedFirstCutoffBounds
import ContinuousFlexibility.Radial.FirstConeLayerSeparation
import ContinuousFlexibility.Radial.TerminalPhysicalCutoffGeometry

/-!
# The actual first-band cutoffs between the two matching joins

The chosen layers lie inside the retained cones. Their full supports are
separated from one another and from the fixed central column, while each
cutoff equals one near its own unchanged matching join. The actual
incoming solutions satisfy their equation wherever these cutoffs enter
the inner interval.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

def SeedRetainedPair.firstTerminalLayer {S : SelectedTailData} {K : SeedCentralCutoff}
    {q length : ℝ} (P : SeedRetainedPair S K q length) (H : ℝ) (right : Bool) : ℝ :=
  terminalConeLayerLeft right (P.sideRadius right * S.cut right S.chain.index) H

def SeedRetainedPair.firstTerminalCutoff {S : SelectedTailData} {K : SeedCentralCutoff}
    {q length : ℝ} (P : SeedRetainedPair S K q length) (H : ℝ) (right : Bool) : ℝ → ℝ :=
  terminalPhysicalCutoff right (P.firstTerminalLayer H right) (2 * P.firstTerminalLayer H right)

theorem SeedRetainedPair.first_cutoff_geometry {S : SelectedTailData}
    {K : SeedCentralCutoff} {q length H : ℝ} (P : SeedRetainedPair S K q length)
    (hS : IsSelectedTail S) (hband : radialFrequencyBand S.chain S.Cstar S.chain.index 2)
    (hq : 0 < q) {Γ : ConnectedReferenceGeometry} (hΓ : Γ.Realizes)
    (hleft : Γ.centralLeft = exp K.left) (hright : Γ.centralRight = exp K.right)
    (hH : log 2 < H) (hL : H < length) {j : ℕ}
    (U : ∀ right, SeedPhysicalFirstIncoming P Γ.reference right j) :
    let cut := fun right => P.sideRadius right * S.joinInner right S.chain.index
    let χ := P.firstTerminalCutoff H
    (∀ right, ContDiff ℝ ∞ (χ right)) ∧
      (∀ right, tsupport (deriv (χ right)) ⊆ Ioo (cut false) (cut true)) ∧
      Disjoint (tsupport (χ false)) (tsupport (χ true)) ∧
      (∀ right, Disjoint (tsupport (referenceColumn Γ.reference)) (tsupport (χ right))) ∧
      (∀ right, χ right =ᶠ[𝓝 (cut right)] fun _ => (1 : ℝ)) ∧
      ∀ right r, r ∈ Ioo (cut false) (cut true) → r ∈ Function.support (χ right) →
        radialJacobi ((j : ℝ) ^ 2) Γ.reference.w (U right).solution r = 0 := by
  let a := P.firstTerminalLayer H
  let χ := P.firstTerminalCutoff H
  let cut := fun right => P.sideRadius right * S.joinInner right S.chain.index
  let oldCut := fun right => P.sideRadius right * S.cut right S.chain.index
  let inner := fun right => P.sideRadius right * (P.side right).inner
  have hD₀ : RadialProfileGeometry (S.family S.sigma) :=
    MorseChainRealization.geometry (hS.2.2.2.1 S.sigma hS.2.2.1).1
  have hc (right : Bool) : 0 < oldCut right :=
    mul_pos (P.sideRadius_pos right)
      (hD₀.1.trans (hS.2.2.2.2.2 right S.chain.index 2 le_rfl (by decide) hband).1.1)
  have hi (right : Bool) : 0 < inner right :=
    mul_pos (P.sideRadius_pos right) (P.side right).inner_pos
  have ha (right : Bool) : 0 < a right := terminalConeLayerLeft_pos right (hc right) H
  have hab (right : Bool) : a right < 2 * a right := by linarith only [ha right]
  have hinside (right : Bool) :
      if right then inner right < a right ∧ 2 * a right < oldCut right
      else oldCut right < a right ∧ 2 * a right < inner right :=
    terminalConeLayer_inside right (hc right) (hi right) hH hL (P.first_physical_cone_length right)
  have hLlayer : oldCut false < a false ∧ 2 * a false < inner false := hinside false
  have hRlayer : inner true < a true ∧ 2 * a true < oldCut true := hinside true
  obtain ⟨hLC, hCI, hIL, hLR, hRI, hIC, hCJ⟩ :=
    P.first_matching_order hS hband hq hleft hright
  have hmid : inner false < inner true := hIL.trans (hLR.trans hRI)
  have hl : cut false < a false := hLC.trans hLlayer.1
  have hjoinR : 2 * a true < cut true := hRlayer.2.trans hCJ
  have hsep : 2 * a false < a true := hLlayer.2.trans (hmid.trans hRlayer.1)
  have hcolumn : tsupport (referenceColumn Γ.reference) ⊆ Ioo (2 * a false) (a true) := by
    intro r hr
    have hs := connectedReference_column_in_central hΓ hr
    exact ⟨hLlayer.2.trans (hIL.trans hs.1), hs.2.trans (hRI.trans hRlayer.1)⟩
  have hcol := terminalPhysicalCutoffs_column_disjoint (hab false) (hab true) hcolumn
  refine ⟨fun right => terminalPhysicalCutoff_smooth right _ _, ?_,
    terminalPhysicalCutoffs_disjoint (hab false) hsep (hab true), ?_, ?_, ?_⟩
  · intro right
    apply (terminalPhysicalCutoff_tsupport_deriv right (hab right)).trans
    intro r hr
    cases right
    · exact ⟨hl.trans_le hr.1,
        hr.2.trans_lt (hsep.trans ((hab true).trans hjoinR))⟩
    · exact ⟨(hl.trans ((hab false).trans hsep)).trans_le hr.1, hr.2.trans_lt hjoinR⟩
  · intro right
    cases right
    · exact hcol.1
    · exact hcol.2
  · intro right
    cases right
    · exact terminalPhysicalCutoff_left_germ false (hab false) hl
    · exact terminalPhysicalCutoff_right_germ true (hab true) hjoinR
  · intro right r hrange hsupp
    apply (U right).equation r
    have hsupport := terminalPhysicalCutoff_support right (hab right) hsupp
    have hentry (right : Bool) :=
      (hS.2.2.2.2.2 right S.chain.index 2 le_rfl (by decide) hband).2.2.2.2.1
    cases right
    · have he : P.sideRadius false * S.entry false S.chain.index < cut false :=
        mul_lt_mul_of_pos_left (hentry false).1 (P.sideRadius_pos false)
      have hei : P.sideRadius false * S.entry false S.chain.index < inner false :=
        he.trans (hLC.trans hCI)
      rw [uIcc_of_ge hei.le]
      exact ⟨(he.trans hrange.1).le, hsupport.le.trans hLlayer.2.le⟩
    · have he : cut true < P.sideRadius true * S.entry true S.chain.index :=
        mul_lt_mul_of_pos_left (hentry true).2 (P.sideRadius_pos true)
      have hie : inner true < P.sideRadius true * S.entry true S.chain.index :=
        hIC.trans (hCJ.trans he)
      rw [uIcc_of_le hie.le]
      exact ⟨hRlayer.1.le.trans hsupport.le, (hrange.2.trans he).le⟩

end ContinuousFlexibility.Radial
