module

public import ContinuousFlexibility.Radial.SeedPreparedTail
public import ContinuousFlexibility.Radial.SeedConeTailConstruction
public import ContinuousFlexibility.Radial.SeedPureTailConstruction
public import ContinuousFlexibility.Radial.SeedPureTailCanonical
public import ContinuousFlexibility.Radial.SeedGluedPairConstruction
public import ContinuousFlexibility.Radial.SeedReturnMargins
public import ContinuousFlexibility.Radial.OpenComponentTransport

/-!
# The central seed joined to the selected natural tails

The actual cone-tail continuations and positive connectors produce a global
second-mode solution. Independent tail rescaling then transports the original
accumulating partition and every negative component exactly.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

theorem seedReference_theorem (_hR03 : R03Statement) (hR07 : R07Statement) : R08Statement := by
  intro q hq
  obtain ⟨S, hS, start, hstart, hseams, hentries, hentry⟩ :=
    exists_seedPreparedSelectedTail_with_seams hR07
  let D₀ := S.family S.sigma
  let c := S.entry false S.chain.index
  let d := S.entry true S.chain.index
  have hσ := hS.2.2.1
  have hfamily := hS.2.2.2.1 S.sigma hσ
  have hreal : MorseChainRealization S.chain S.sigma D₀ S.constants := hfamily.1
  have hmass : MorseMassResistanceBounds S.chain S.sigma D₀ S.constants := hfamily.2
  have hBounds : AccumulatingProfileBounds D₀ S.constants := hreal.2.2.2.2.2.2.2.2.2
  have hD : RadialProfileGeometry D₀ := hBounds.1
  have hc : c ∈ radialCore D₀ := (hentry false).1
  have hd : d ∈ radialCore D₀ := (hentry true).1
  obtain ⟨CL⟩ := exists_morseSecondMode_coneTail hreal hmass hσ hc
    (hentry false).2.2 (hentry false).2.1
  obtain ⟨CR⟩ := exists_morseSecondMode_coneTail hreal hmass hσ hd
    (hentry true).2.2 (hentry true).2.1
  obtain ⟨PL⟩ := CL.toPureTail hc
  obtain ⟨PR⟩ := CR.toPureTail hd
  obtain ⟨TL, hTL⟩ := PL.toCanonical hD hc
  obtain ⟨TR, hTR⟩ := PR.toCanonical hD hd
  obtain ⟨K⟩ := exists_seedCentralCutoff
  obtain ⟨G⟩ := exists_seedGluedPair hD hc hd TL TR
    (by simpa using hTL)
    (by simpa using hTR) K hq
  obtain ⟨D, hDa, hDb, hDw, hDphi, hAccum, hConstruction⟩ :=
    G.exists_accumulating_reference_with_construction_geometry hreal hσ hq hstart
      (hseams false) (hseams true) hc hd hentries
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
  refine ⟨S, hS, D, hAccum, hConstruction, L, H, ?_, ?_, ?_⟩
  · refine ⟨hDaL₀.trans hL₀L, K.retained_turns.2.1, K.retained_turns.2.2,
      hHH₀.trans hH₀Db, 1, 1, by norm_num, by norm_num, ?_, ?_⟩
    · intro r hr
      exact (hmid r (hcentral r hr)).1.eq_of_nhds.trans (K.profile_retained hr)
    · intro r hr
      simpa only [one_mul] using
        (hmid r (hcentral r hr)).2.eq_of_nhds.trans (K.height_retained hr)
  · obtain ⟨cL, cR, aL, aR, hcL, hcR, haL, haR, hconeL, hconeR⟩ := K.exact_cones
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
  · intro right
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

end ContinuousFlexibility.Radial
