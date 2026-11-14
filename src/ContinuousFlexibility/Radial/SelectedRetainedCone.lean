module

public import ContinuousFlexibility.Radial.SeedRetainedCone
public import ContinuousFlexibility.Radial.SeedNaturalState
public import ContinuousFlexibility.Radial.MorseSecondModeSmoothExtension
public import ContinuousFlexibility.Radial.SelectedNaturalJoin

/-!
# The same selected tail with an arbitrarily long retained first cone

The second mode is first continued through the original cut-to-entry
segment, so the selected tail and its entrance Cauchy data do not change.
At the original cone germ the profile is extended by that exact cone.
Only farther inward than a freely chosen logarithmic length do the
pure-mode and canonical-mode corrections begin.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

structure SeedRetainedFirstCone (S : SelectedTailData) (right : Bool) (length : ℝ) where
  natural : ℝ → ℝ
  natural_smooth : ContDiff ℝ ∞ natural
  natural_tail : RadialNaturalTail (S.family S.sigma) right 2
    (S.cut right S.chain.index) natural
  natural_entry : natural (S.entry right S.chain.index) =
    S.outgoing right 2 (S.entry right S.chain.index)
  natural_entry_deriv : deriv natural (S.entry right S.chain.index) =
    deriv (S.outgoing right 2) (S.entry right S.chain.index)
  natural_retained : EqOn natural (S.outgoing right 2)
    (radialTailInterval (S.family S.sigma) right (S.entry right S.chain.index))
  tail : SeedPureTail (S.family S.sigma) right (S.cut right S.chain.index) natural
  canonical : tail.mode = (if right then (-2 : ℝ) else 2)
  coneScale : ℝ
  coneScale_pos : 0 < coneScale
  old_cone_germ : (S.family S.sigma).w =ᶠ[𝓝 (S.cut right S.chain.index)]
    (fun t => coneScale * t)
  inner : ℝ
  inner_pos : 0 < inner
  inner_order : if right then inner < S.cut right S.chain.index
    else S.cut right S.chain.index < inner
  cone_length : if right then length ≤ log (S.cut right S.chain.index / inner)
    else length ≤ log (inner / S.cut right S.chain.index)
  pure_cut : if right then tail.cut < inner else inner < tail.cut
  cone_germ : ∀ r ∈ uIcc inner (S.cut right S.chain.index),
    tail.profile =ᶠ[𝓝 r] (fun t => coneScale * t)
  increasing_inward : ∀ r, 0 < r →
    (if right then r ≤ S.cut right S.chain.index else S.cut right S.chain.index ≤ r) →
    0 < deriv tail.profile r
  logSlope_inward : ∀ r, 0 < r →
    (if right then r ≤ S.cut right S.chain.index else S.cut right S.chain.index ≤ r) →
    (3 / 4 : ℝ) * tail.profile r ≤ r * deriv tail.profile r

/-- This is a construction from the actual selected data. In particular
neither the selected sequence nor either original incoming state is reselected. -/
theorem exists_seedRetainedFirstCone {S : SelectedTailData}
    (hS : IsSelectedTail S)
    (hband : radialFrequencyBand S.chain S.Cstar S.chain.index 2)
    (right : Bool) {length : ℝ} (hlength : 0 < length) :
    Nonempty (SeedRetainedFirstCone S right length) := by
  let D := S.family S.sigma
  let c := S.cut right S.chain.index
  let e := S.entry right S.chain.index
  have hσ := hS.2.2.1
  have hfamily := hS.2.2.2.1 S.sigma hσ
  have hreal : MorseChainRealization S.chain S.sigma D S.constants := hfamily.1
  have hmass : MorseMassResistanceBounds S.chain S.sigma D S.constants := hfamily.2
  have hD : RadialProfileGeometry D := hreal.geometry
  have hmatching := hS.2.2.2.2.2 right S.chain.index 2 le_rfl (by decide) hband
  rcases hmatching with ⟨hc, he, _, _, horder, _, hfirst, _, _, _, _, hN, _⟩
  have hce : if right then c < e else e < c := by
    cases right <;> exact horder.1.trans horder.2
  have hfirstCone : ∃ C : ℝ, 0 < C ∧ D.w =ᶠ[𝓝 c] (fun r => C * r) := by
    have hh := hfirst
    rw [if_pos rfl] at hh
    exact hh.1
  obtain ⟨C, hC, hCg⟩ := hfirstCone
  obtain ⟨V, hVs, hV₀, hVtail, _, _⟩ :=
    morseSecondMode_naturalTail_smoothZeroExtension hreal hmass hσ he hN
  have hV₁ : deriv V e = deriv (S.outgoing right 2) e := by
    simpa only [radialJet_eq_iteratedDeriv, iteratedDeriv_one] using
      radialTail_extension_entry_jets he hN.1 hVs.contDiffAt hV₀ hVtail 1
  have hVODE := radialTail_extension_radialJacobi hD he hN hVs hVtail
  have hNV : RadialNaturalTail D right 2 e V := by
    refine ⟨hVs.contDiffAt, ⟨hVs.contDiffOn, ?_⟩, ?_, ?_⟩
    · intro r hr
      simpa only [Nat.cast_ofNat, show (2 : ℝ) ^ 2 = 4 by norm_num] using hVODE.2 r hr
    · exact (r07_memLp_radialHilbertMeasure hD.1 hD.2.2.1.1.continuous
        hVs.continuous).restrict _
    · obtain ⟨r, hr, hn⟩ := hN.2.2.2
      exact ⟨r, hr, by rw [hVtail r hr]; exact hn⟩
  obtain ⟨v, hvs, hvN, hv₀, hv₁, hvEq, _⟩ :=
    exists_radialNaturalTail_continuation_preserving_tail hD hc he hce hVs hNV
  obtain ⟨W, hWs, hW₀, hWtail, hWzero, _⟩ :=
    morseSecondMode_naturalTail_smoothZeroExtension hreal hmass hσ hc hvN
  have hW₁ : deriv W c = deriv v c := by
    simpa only [radialJet_eq_iteratedDeriv, iteratedDeriv_one] using
      radialTail_extension_entry_jets hc hvN.1 hWs.contDiffAt hW₀ hWtail 1
  have hWne : (W c, deriv W c) ≠ (0, 0) := by
    have hWvalue : W c = v c := hW₀
    rw [hWvalue, hW₁]
    exact radialNaturalTail_entry_state_ne_zero hD hc hvN
  obtain ⟨T, hTcone⟩ := exists_seedConeTail_of_coneGerm hD hc hC hCg hWs hWtail hWzero
    (radialTail_extension_radialJacobi hD hc hvN hWs hWtail) hWne
  let a := if right then T.cut * exp (-length - 1) else T.cut * exp (length + 1)
  have ha : 0 < a := by
    cases right <;> exact mul_pos T.cut_pos (exp_pos _)
  have haT : if right then a < T.cut else T.cut < a := by
    cases right
    · change T.cut < T.cut * exp (length + 1)
      have hh : 1 < exp (length + 1) := one_lt_exp_iff.mpr (by linarith)
      simpa only [mul_one] using mul_lt_mul_of_pos_left hh T.cut_pos
    · change T.cut * exp (-length - 1) < T.cut
      have hh : exp (-length - 1) < 1 := exp_lt_one_iff.mpr (by linarith)
      simpa only [mul_one] using mul_lt_mul_of_pos_left hh T.cut_pos
  have hac : if right then a < c else c < a := by
    cases right
    · exact T.cut_order.trans haT
    · exact haT.trans T.cut_order
  have halength : if right then length ≤ log (c / a) else length ≤ log (a / c) := by
    have hcpos : 0 < c := hD.1.trans hc.1
    cases right
    · change length ≤ log ((T.cut * exp (length + 1)) / c)
      rw [log_div (mul_ne_zero T.cut_pos.ne' (exp_ne_zero _)) hcpos.ne',
        log_mul T.cut_pos.ne' (exp_ne_zero _), log_exp]
      have hh := log_lt_log hcpos T.cut_order
      linarith
    · change length ≤ log (c / (T.cut * exp (-length - 1)))
      rw [log_div hcpos.ne' (mul_ne_zero T.cut_pos.ne' (exp_ne_zero _)),
        log_mul T.cut_pos.ne' (exp_ne_zero _), log_exp]
      have hh := log_lt_log T.cut_pos T.cut_order
      linarith
  have haTle : if right then a ≤ T.cut else T.cut ≤ a := by
    cases right <;> exact haT.le
  obtain ⟨P, hPmode, hPa, hPret, hPd, hPlower⟩ :=
    T.toCanonical_retaining_at_logSlope hD hc ha haTle
  refine ⟨{
    natural := v
    natural_smooth := hvs
    natural_tail := hvN
    natural_entry := hv₀.trans hV₀
    natural_entry_deriv := hv₁.trans hV₁
    natural_retained := fun r hr => (hvEq hr).trans (hVtail r hr)
    tail := P
    canonical := hPmode
    coneScale := C
    coneScale_pos := hC
    old_cone_germ := hCg
    inner := a
    inner_pos := ha
    inner_order := hac
    cone_length := halength
    pure_cut := hPa
    cone_germ := ?_
    increasing_inward := ?_
    logSlope_inward := ?_ }⟩
  · intro r hr
    have hrc : (0 < r) ∧ (if right then a ≤ r else r ≤ a) ∧
        (if right then r ≤ c else c ≤ r) := by
      cases right
      · rw [uIcc_of_ge hac.le] at hr
        exact ⟨(hD.1.trans hc.1).trans_le hr.1, hr.2, hr.1⟩
      · rw [uIcc_of_le hac.le] at hr
        exact ⟨ha.trans_le hr.1, hr.1, hr.2⟩
    exact (hPret r hrc.2.1).1.trans (hTcone r hrc.1 hrc.2.2)
  · intro r hr hi
    apply hPd r hr
    rw [(hTcone r hr hi).deriv_eq]
    have hd : HasDerivAt (fun t : ℝ => C * t) C r := by
      simpa only [mul_one] using (hasDerivAt_id' r).const_mul C
    rw [hd.deriv]
    exact hC
  · intro r hr hi
    apply hPlower r hr
    have hg := hTcone r hr hi
    rw [hg.eq_of_nhds, hg.deriv_eq]
    have hd : HasDerivAt (fun t : ℝ => C * t) C r := by
      simpa only [mul_one] using (hasDerivAt_id' r).const_mul C
    rw [hd.deriv]
    nlinarith [mul_pos hC hr]

end ContinuousFlexibility.Radial
