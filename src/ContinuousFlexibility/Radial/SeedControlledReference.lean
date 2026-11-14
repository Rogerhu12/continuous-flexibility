module

public import ContinuousFlexibility.Radial.SeedCentralControl
public import ContinuousFlexibility.Radial.ConnectedReferenceBorder
public import ContinuousFlexibility.Radial.SeedConeTailConstruction
public import ContinuousFlexibility.Radial.SeedPureTailConstruction
public import ContinuousFlexibility.Radial.SeedPureTailCanonical
public import ContinuousFlexibility.Radial.SeedGluedPairConstruction
public import ContinuousFlexibility.Radial.TwoTailReferenceAssembly
public import ContinuousFlexibility.Radial.SeedReturnMargins
public import ContinuousFlexibility.Radial.OpenComponentTransport
public import ContinuousFlexibility.Radial.MorseRealizationBasic

/-!
# Building the connected reference with prescribed central data

This is the actual seed construction with its choices exposed.  The selected
tail S, central cutoff K and cone-head length q are inputs.  No second selected
tail is chosen, and the central profile and kernel have scale and amplitude
one on the entire prescribed retained patch.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

theorem exists_seedControlledReference_with_property {S : SelectedTailData}
    (hS : IsSelectedTail S)
    (hentries : S.entry false S.chain.index < S.entry true S.chain.index)
    (hentry : ∀ right, S.entry right S.chain.index ∈ radialCore (S.family S.sigma))
    (K : SeedCentralCutoff) {q : ℝ} (hq : 0 < q)
    (G : SeedGluedPair (S.family S.sigma)
      (S.entry false S.chain.index) (S.entry true S.chain.index)
      (S.outgoing false 2) (S.outgoing true 2) K q)
    (Q : ReferenceData → Prop)
    (hchoice : ∃ D : ReferenceData,
      D.a = G.radiusL * (S.family S.sigma).a ∧
      D.b = G.radiusR * (S.family S.sigma).b ∧
      D.w = G.profile ∧ D.phi = G.height ∧ IsAccumulatingProfile D ∧ Q D) :
    ∃ D : ReferenceData, Q D ∧ D.w = G.profile ∧ D.phi = G.height ∧ IsAccumulatingProfile D ∧
      EqOn D.w (centralRadialProfile 1) (Ioo (exp K.left) (exp K.right)) ∧
      EqOn D.phi centralKernelHeight (Ioo (exp K.left) (exp K.right)) ∧
      (∀ r ∈ radialCore D, radialJacobi 4 D.w D.phi r = 0) ∧
      CentralPatch D (exp K.left) (exp K.right) ∧
      ConnectedPositiveHeads D (exp K.left) (exp K.right) q ∧
      ConnectedSelectedTails S D (exp K.left) (exp K.right) := by
  let D₀ := S.family S.sigma
  let c := S.entry false S.chain.index
  let d := S.entry true S.chain.index
  have hσ := hS.2.2.1
  have hfamily := hS.2.2.2.1 S.sigma hσ
  have hreal : MorseChainRealization S.chain S.sigma D₀ S.constants := hfamily.1
  have hmass : MorseMassResistanceBounds S.chain S.sigma D₀ S.constants := hfamily.2
  have hBounds : AccumulatingProfileBounds D₀ S.constants := hreal.2.2.2.2.2.2.2.2.2
  have hD : RadialProfileGeometry D₀ := hBounds.1
  have hc : c ∈ radialCore D₀ := hentry false
  have hd : d ∈ radialCore D₀ := hentry true
  have hAccum₀ : IsAccumulatingProfile D₀ := ⟨S.constants, hBounds⟩
  obtain ⟨D, hDa, hDb, hDw, hDphi, hAccum, hQ⟩ := hchoice
  have hGeo : RadialProfileGeometry D := (Classical.choose_spec hAccum).1
  have hRR : 0 < G.radiusR := G.radiusL_pos.trans_le G.radius_order
  let L := exp K.left
  let H := exp K.right
  let L₀ := exp (K.left - q - 4)
  let H₀ := exp (K.right + q + 4)
  have hDaL₀ : D.a < L₀ := by
    rw [hDa]
    exact (mul_lt_mul_of_pos_left hc.1 G.radiusL_pos).trans G.left_entry
  have hH₀Db : H₀ < D.b := by
    rw [hDb]
    exact G.right_entry.trans (mul_lt_mul_of_pos_left hd.2 hRR)
  have hL₀L : L₀ < L := exp_lt_exp.mpr (by linarith)
  have hHH₀ : H < H₀ := exp_lt_exp.mpr (by linarith)
  have hLH : L < H := exp_lt_exp.mpr (by linarith [K.left_neg, K.right_pos])
  have hmid (r : ℝ) (hr : r ∈ Ioo L₀ H₀) :
      D.w =ᶠ[𝓝 r] K.profile ∧ D.phi =ᶠ[𝓝 r] K.height := by
    rw [hDw, hDphi]
    exact G.middle_germ r hr
  have hcentral (r : ℝ) (hr : r ∈ Ioo L H) : r ∈ Ioo L₀ H₀ :=
    ⟨hL₀L.trans hr.1, hr.2.trans hHH₀⟩
  refine ⟨D, hQ, hDw, hDphi, hAccum, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r hr
    exact (hmid r (hcentral r hr)).1.eq_of_nhds.trans (K.profile_retained hr)
  · intro r hr
    exact (hmid r (hcentral r hr)).2.eq_of_nhds.trans (K.height_retained hr)
  · intro r hr
    rw [hDw, hDphi]
    apply G.equation r
    simpa only [radialCore, hDa, hDb] using hr
  · refine ⟨hDaL₀.trans hL₀L, K.retained_turns.2.1, K.retained_turns.2.2,
      hHH₀.trans hH₀Db, 1, 1, by norm_num, by norm_num, ?_, ?_⟩
    · intro r hr
      exact (hmid r (hcentral r hr)).1.eq_of_nhds.trans (K.profile_retained hr)
    · intro r hr
      simpa only [one_mul] using
        (hmid r (hcentral r hr)).2.eq_of_nhds.trans (K.height_retained hr)
  · unfold ConnectedPositiveHeads
    obtain ⟨cL, cR, aL, aR, hcL, hcR, haL, haR, hconeL, hconeR⟩ := K.exact_cones
    let l₁ := exp (K.left - q - 3)
    let l₂ := exp (K.left - 2)
    let h₁ := exp (K.right + 2)
    let h₂ := exp (K.right + q + 3)
    have hL₀l₁ : L₀ < l₁ := exp_lt_exp.mpr (by linarith)
    have hl₁l₂ : l₁ < l₂ := exp_lt_exp.mpr (by linarith)
    have hl₂L : l₂ < L := exp_lt_exp.mpr (by linarith)
    have hHh₁ : H < h₁ := exp_lt_exp.mpr (by linarith)
    have hh₁h₂ : h₁ < h₂ := exp_lt_exp.mpr (by linarith)
    have hh₂H₀ : h₂ < H₀ := exp_lt_exp.mpr (by linarith)
    have hhead (r : ℝ) (hr : r ∈ Ioo l₁ h₂) : r ∈ Ioo L₀ H₀ :=
      ⟨hL₀l₁.trans hr.1, hr.2.trans hh₂H₀⟩
    refine ⟨l₁, l₂, h₁, h₂, cL, cR, hDaL₀.trans hL₀l₁, hl₁l₂, hl₂L,
      hHh₁, hh₁h₂, hh₂H₀.trans hH₀Db, hcL, hcR, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · dsimp only [l₂, l₁]
      rw [log_div (exp_ne_zero _) (exp_ne_zero _), log_exp, log_exp]
      linarith
    · dsimp only [h₂, h₁]
      rw [log_div (exp_ne_zero _) (exp_ne_zero _), log_exp, log_exp]
      linarith
    · intro r hr
      have hrwin := hhead r ⟨hr.1, hr.2.trans
        (hl₂L.trans (hLH.trans (hHh₁.trans hh₁h₂)))⟩
      rw [(hmid r hrwin).1.eq_of_nhds]
      have hrpos : 0 < r := (exp_pos _).trans hr.1
      have hlog : log r < K.left - 2 := by
        simpa only [l₂, log_exp] using log_lt_log hrpos hr.2
      exact (hconeL r hrpos (by linarith only [hlog])).1
    · intro r hr
      have hrwin := hhead r ⟨(hl₁l₂.trans (hl₂L.trans (hLH.trans hHh₁))).trans hr.1, hr.2⟩
      rw [(hmid r hrwin).1.eq_of_nhds]
      have hrpos : 0 < r := (exp_pos _).trans hr.1
      have hlog : K.right + 2 < log r := by
        simpa only [h₁, log_exp] using log_lt_log (exp_pos _) hr.1
      exact (hconeR r hrpos (by linarith only [hlog])).1
    · intro r hr
      have hrwin := hhead r ⟨hl₁l₂.trans hr.1,
        hr.2.trans (hLH.trans (hHh₁.trans hh₁h₂))⟩
      rw [(hmid r hrwin).1.deriv_eq]
      have hrpos : 0 < r := (exp_pos _).trans hr.1
      apply K.profile_deriv_pos hrpos
      left
      have hlog : log r < K.left := by
        simpa only [L, log_exp] using log_lt_log hrpos hr.2
      exact hlog.le
    · intro r hr
      have hrwin := hhead r ⟨(hl₁l₂.trans (hl₂L.trans hLH)).trans hr.1,
        hr.2.trans hh₁h₂⟩
      rw [(hmid r hrwin).1.deriv_eq]
      have hrpos : 0 < r := (exp_pos _).trans hr.1
      apply K.profile_deriv_pos hrpos
      right
      have hlog : K.right < log r := by
        simpa only [H, log_exp] using log_lt_log (exp_pos _) hr.1
      exact hlog.le
  · unfold ConnectedSelectedTails
    intro right
    cases right with
    | false =>
        refine ⟨G.radiusL, G.heightL, G.amplitudeL, G.radiusL_pos, G.heightL_pos,
          G.amplitudeL_ne, hDa, ?_, ?_⟩
        · intro r hr
          refine ⟨?_, ?_, ?_⟩
          · change D.a < G.radiusL * r ∧ G.radiusL * r < L
            rw [hDa]
            exact ⟨mul_lt_mul_of_pos_left hr.1 G.radiusL_pos,
              (mul_lt_mul_of_pos_left hr.2 G.radiusL_pos).trans
                (G.left_entry.trans hL₀L)⟩
          · rw [hDw]
            exact (G.left_tail r hr).1
          · rw [hDphi]
            exact (G.left_tail r hr).2
        · intro l h hneg hsub
          apply negativeRadialComponent_travel_of_open_tail
            G.radiusL_pos G.heightL_pos hneg
          · rw [hDa]
            exact mul_lt_mul_of_pos_left hneg.1 G.radiusL_pos
          · rw [hDb]
            exact (mul_lt_mul_of_pos_left hneg.2.2.1 G.radiusL_pos).trans_le
              (mul_le_mul_of_nonneg_right G.radius_order (hD.1.trans hD.2.1).le)
          · exact hD.2.2.1.1
          · exact hGeo.2.2.1.1
          · exact hsub
          · intro r hr
            rw [hDw]
            exact (G.left_tail r hr).1
    | true =>
        refine ⟨G.radiusR, G.heightR, G.amplitudeR, hRR, G.heightR_pos,
          G.amplitudeR_ne, hDb, ?_, ?_⟩
        · intro r hr
          refine ⟨?_, ?_, ?_⟩
          · change H < G.radiusR * r ∧ G.radiusR * r < D.b
            rw [hDb]
            exact ⟨(hHH₀.trans G.right_entry).trans (mul_lt_mul_of_pos_left hr.1 hRR),
              mul_lt_mul_of_pos_left hr.2 hRR⟩
          · rw [hDw]
            exact (G.right_tail r hr).1
          · rw [hDphi]
            exact (G.right_tail r hr).2
        · intro l h hneg hsub
          apply negativeRadialComponent_travel_of_open_tail hRR G.heightR_pos hneg
          · rw [hDa]
            exact (mul_le_mul_of_nonneg_right G.radius_order hD.1.le).trans_lt
              (mul_lt_mul_of_pos_left hneg.1 hRR)
          · rw [hDb]
            exact mul_lt_mul_of_pos_left hneg.2.2.1 hRR
          · exact hD.2.2.1.1
          · exact hGeo.2.2.1.1
          · exact hsub
          · intro r hr
            rw [hDw]
            exact (G.right_tail r hr).1

theorem exists_seedControlledReference_of_gluedPair {S : SelectedTailData}
    (hS : IsSelectedTail S)
    (hentries : S.entry false S.chain.index < S.entry true S.chain.index)
    (hentry : ∀ right, S.entry right S.chain.index ∈ radialCore (S.family S.sigma))
    (K : SeedCentralCutoff) {q : ℝ} (hq : 0 < q)
    (G : SeedGluedPair (S.family S.sigma)
      (S.entry false S.chain.index) (S.entry true S.chain.index)
      (S.outgoing false 2) (S.outgoing true 2) K q) :
    ∃ D : ReferenceData, D.w = G.profile ∧ D.phi = G.height ∧ IsAccumulatingProfile D ∧
      EqOn D.w (centralRadialProfile 1) (Ioo (exp K.left) (exp K.right)) ∧
      EqOn D.phi centralKernelHeight (Ioo (exp K.left) (exp K.right)) ∧
      (∀ r ∈ radialCore D, radialJacobi 4 D.w D.phi r = 0) ∧
      CentralPatch D (exp K.left) (exp K.right) ∧
      ConnectedPositiveHeads D (exp K.left) (exp K.right) q ∧
      ConnectedSelectedTails S D (exp K.left) (exp K.right) := by
  have hreal := (hS.2.2.2.1 S.sigma hS.2.2.1).1
  have hAccum₀ : IsAccumulatingProfile (S.family S.sigma) :=
    ⟨S.constants, hreal.accumulating⟩
  obtain ⟨D, ha, hb, hw, hphi, hD⟩ :=
    exists_accumulating_reference_of_two_tail_surgery hAccum₀ G.radiusL_pos
      G.radius_order G.heightL_pos G.heightR_pos (hentry false).1 hentries (hentry true).2
      G.geometry (fun r hr => (G.left_tail r hr).1) (fun r hr => (G.right_tail r hr).1)
  obtain ⟨E, _, hE⟩ := exists_seedControlledReference_with_property
    hS hentries hentry K hq G (fun _ => True) ⟨D, ha, hb, hw, hphi, hD, trivial⟩
  exact ⟨E, hE⟩

theorem exists_seedControlledReference_with_construction_transport {S : SelectedTailData}
    (hS : IsSelectedTail S)
    (hentries : S.entry false S.chain.index < S.entry true S.chain.index)
    (hentry : ∀ right, S.entry right S.chain.index ∈ radialCore (S.family S.sigma))
    (hband : radialFrequencyBand S.chain S.Cstar S.chain.index 2)
    (K : SeedCentralCutoff) {q : ℝ} (hq : 0 < q)
    (G : SeedGluedPair (S.family S.sigma)
      (S.entry false S.chain.index) (S.entry true S.chain.index)
      (S.outgoing false 2) (S.outgoing true 2) K q) :
    ∃ D : ReferenceData, RadialConstructionGeometry D ∧ D.w = G.profile ∧
      D.phi = G.height ∧ IsAccumulatingProfile D ∧
      EqOn D.w (centralRadialProfile 1) (Ioo (exp K.left) (exp K.right)) ∧
      EqOn D.phi centralKernelHeight (Ioo (exp K.left) (exp K.right)) ∧
      (∀ r ∈ radialCore D, radialJacobi 4 D.w D.phi r = 0) ∧
      CentralPatch D (exp K.left) (exp K.right) ∧
      ConnectedPositiveHeads D (exp K.left) (exp K.right) q ∧
      ConnectedSelectedTails S D (exp K.left) (exp K.right) ∧
      D.a = G.radiusL * (S.family S.sigma).a ∧
      D.b = G.radiusR * (S.family S.sigma).b ∧
      ∃ e : ℝ ≃o ℝ, ∃ N : ℕ, 1 ≤ N ∧
        D.cellIndex = (fun m => max ((S.family S.sigma).cellIndex m) N) ∧
        (∀ m, e ⁻¹' (S.family S.sigma).cells m ⊆ D.cells m) ∧
        D.localizer = (fun m r => (S.family S.sigma).localizer m (e r)) ∧
        (∀ r, r ≤ S.entry false S.chain.index → e.symm r = G.radiusL * r) ∧
        (∀ r, S.entry true S.chain.index ≤ r → e.symm r = G.radiusR * r) := by
  have hreal := (hS.2.2.2.1 S.sigma hS.2.2.1).1
  have hseam (side : Bool) :
      S.entry side S.chain.index = morseChainSeam S.chain side S.chain.index := by
    simpa only [morseChainSeam] using
      (hS.2.2.2.2.2 side S.chain.index 2 le_rfl (by decide) hband).2.2.2.2.2.1
  let Q : ReferenceData → Prop := fun D =>
    RadialConstructionGeometry D ∧
      D.a = G.radiusL * (S.family S.sigma).a ∧
      D.b = G.radiusR * (S.family S.sigma).b ∧
      ∃ e : ℝ ≃o ℝ, ∃ N : ℕ, 1 ≤ N ∧
        D.cellIndex = (fun m => max ((S.family S.sigma).cellIndex m) N) ∧
        (∀ m, e ⁻¹' (S.family S.sigma).cells m ⊆ D.cells m) ∧
        D.localizer = (fun m r => (S.family S.sigma).localizer m (e r)) ∧
        (∀ r, r ≤ S.entry false S.chain.index → e.symm r = G.radiusL * r) ∧
        (∀ r, S.entry true S.chain.index ≤ r → e.symm r = G.radiusR * r)
  obtain ⟨E, ha, hb, hw, hphi, hacc, hconstruction, htransport⟩ :=
    G.exists_accumulating_reference_with_construction_geometry_transport
      hreal hS.2.2.1 hq (le_refl S.chain.index) (hseam false) (hseam true)
      (hentry false) (hentry true) hentries
  obtain ⟨D, hQ, hDw, hDphi, hDacc, hcentral, hcentralPhi,
      hkernel, hpatch, hheads, htails⟩ :=
    exists_seedControlledReference_with_property hS hentries hentry K hq G Q
      ⟨E, ha, hb, hw, hphi, hacc, hconstruction, ha, hb, htransport⟩
  exact ⟨D, hQ.1, hDw, hDphi, hDacc, hcentral, hcentralPhi,
    hkernel, hpatch, hheads, htails, hQ.2⟩

theorem exists_seedControlledReference_with_construction {S : SelectedTailData}
    (hS : IsSelectedTail S)
    (hentries : S.entry false S.chain.index < S.entry true S.chain.index)
    (hentry : ∀ right, S.entry right S.chain.index ∈ radialCore (S.family S.sigma))
    (hband : radialFrequencyBand S.chain S.Cstar S.chain.index 2)
    (K : SeedCentralCutoff) {q : ℝ} (hq : 0 < q)
    (G : SeedGluedPair (S.family S.sigma)
      (S.entry false S.chain.index) (S.entry true S.chain.index)
      (S.outgoing false 2) (S.outgoing true 2) K q) :
    ∃ D : ReferenceData, RadialConstructionGeometry D ∧ D.w = G.profile ∧ D.phi = G.height ∧ IsAccumulatingProfile D ∧
      EqOn D.w (centralRadialProfile 1) (Ioo (exp K.left) (exp K.right)) ∧
      EqOn D.phi centralKernelHeight (Ioo (exp K.left) (exp K.right)) ∧
      (∀ r ∈ radialCore D, radialJacobi 4 D.w D.phi r = 0) ∧
      CentralPatch D (exp K.left) (exp K.right) ∧
      ConnectedPositiveHeads D (exp K.left) (exp K.right) q ∧
      ConnectedSelectedTails S D (exp K.left) (exp K.right) := by
  obtain ⟨D, hconstruction, hw, hphi, hacc, hcentral, hcentralPhi,
      hkernel, hpatch, hheads, htails, _⟩ :=
    exists_seedControlledReference_with_construction_transport
      hS hentries hentry hband K hq G
  exact ⟨D, hconstruction, hw, hphi, hacc, hcentral, hcentralPhi,
    hkernel, hpatch, hheads, htails⟩

/-- The original controlled construction, retaining its exact interface.
The assembly companion also accepts an already constructed, retained pair. -/
theorem exists_seedControlledReference {S : SelectedTailData}
    (hS : IsSelectedTail S)
    (hentries : S.entry false S.chain.index < S.entry true S.chain.index)
    (hentry : ∀ right,
      S.entry right S.chain.index ∈ radialCore (S.family S.sigma) ∧
      0 < deriv (S.family S.sigma).w (S.entry right S.chain.index) ∧
      RadialNaturalTail (S.family S.sigma) right 2
        (S.entry right S.chain.index) (S.outgoing right 2))
    (K : SeedCentralCutoff) {q : ℝ} (hq : 0 < q) :
    ∃ D : ReferenceData, IsAccumulatingProfile D ∧
      EqOn D.w (centralRadialProfile 1) (Ioo (exp K.left) (exp K.right)) ∧
      EqOn D.phi centralKernelHeight (Ioo (exp K.left) (exp K.right)) ∧
      (∀ r ∈ radialCore D, radialJacobi 4 D.w D.phi r = 0) ∧
      CentralPatch D (exp K.left) (exp K.right) ∧
      ConnectedPositiveHeads D (exp K.left) (exp K.right) q ∧
      ConnectedSelectedTails S D (exp K.left) (exp K.right) := by
  have hfamily := hS.2.2.2.1 S.sigma hS.2.2.1
  have hD : RadialProfileGeometry (S.family S.sigma) := MorseChainRealization.geometry hfamily.1
  obtain ⟨CL⟩ := exists_morseSecondMode_coneTail hfamily.1 hfamily.2 hS.2.2.1
    (hentry false).1 (hentry false).2.2 (hentry false).2.1
  obtain ⟨CR⟩ := exists_morseSecondMode_coneTail hfamily.1 hfamily.2 hS.2.2.1
    (hentry true).1 (hentry true).2.2 (hentry true).2.1
  obtain ⟨PL⟩ := CL.toPureTail (hentry false).1
  obtain ⟨PR⟩ := CR.toPureTail (hentry true).1
  obtain ⟨TL, hTL⟩ := PL.toCanonical hD (hentry false).1
  obtain ⟨TR, hTR⟩ := PR.toCanonical hD (hentry true).1
  obtain ⟨G⟩ := exists_seedGluedPair hD (hentry false).1 (hentry true).1 TL TR
    (by simpa using hTL) (by simpa using hTR) K hq
  obtain ⟨D, _, _, h⟩ := exists_seedControlledReference_of_gluedPair hS hentries
    (fun right => (hentry right).1) K hq G
  exact ⟨D, h⟩

end ContinuousFlexibility.Radial
