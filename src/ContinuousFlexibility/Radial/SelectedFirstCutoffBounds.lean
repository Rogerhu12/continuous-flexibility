import ContinuousFlexibility.Radial.SelectedFirstConeProfile
import ContinuousFlexibility.Radial.TerminalConeLayer

/-!
# Actual first-band source and energy on a retained reference

The layer, stand-in, cone coefficient and boundary normalization all come
from the same retained pair. Its depth can be selected after the finite
first band is fixed, without replacing the old natural solutions.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal
open ContinuousFlexibility.Statements

theorem SeedRetainedPair.first_physical_cone_length {S : SelectedTailData}
    {K : SeedCentralCutoff} {q length : ℝ} (P : SeedRetainedPair S K q length)
    (right : Bool) :
    if right then
      length ≤ log ((P.sideRadius right * S.cut right S.chain.index) /
        (P.sideRadius right * (P.side right).inner))
    else
      length ≤ log ((P.sideRadius right * (P.side right).inner) /
        (P.sideRadius right * S.cut right S.chain.index)) := by
  cases right
  · simpa only [Bool.false_eq_true, ite_false, SeedRetainedPair.side,
      mul_div_mul_left _ _ (P.sideRadius_pos false).ne'] using P.left.cone_length
  · simpa only [ite_true, SeedRetainedPair.side,
      mul_div_mul_left _ _ (P.sideRadius_pos true).ne'] using P.right.cone_length

theorem SeedRetainedPair.first_cutoff_source_energy {S : SelectedTailData}
    {K : SeedCentralCutoff} {q length H : ℝ} (P : SeedRetainedPair S K q length)
    {D : ReferenceData} (hD : RadialProfileGeometry D) (hw : D.w = P.pair.profile)
    (hS : IsSelectedTail S)
    (hband : radialFrequencyBand S.chain S.Cstar S.chain.index 2) (right : Bool)
    (hcone : ∃ C : ℝ, 0 < C ∧ ∀ x ∈ uIcc (S.cut right S.chain.index)
      (S.joinInner right S.chain.index), (S.family S.sigma).w =ᶠ[𝓝 x] (fun t => C * t))
    {j : ℕ} (hj : 2 ≤ j) (U : SeedPhysicalFirstIncoming P D right j)
    (hH : 2 * log 2 ≤ H) (hH' : log 2 < H) (hL : H < length) :
    let c := P.sideRadius right * S.cut right S.chain.index
    let p := P.sideRadius right * S.joinInner right S.chain.index
    let inner := P.sideRadius right * (P.side right).inner
    let a := terminalConeLayerLeft right c H
    let lam := standInBoundaryScale ((j : ℝ) ^ 2) (D.w p) p
    let χ := terminalPhysicalCutoff right a (2 * a)
    0 < a ∧
      (if right then inner < a ∧ 2 * a < c else c < a ∧ 2 * a < inner) ∧
      MemLp (terminalCapHilbertSource lam D.w χ U.solution) 2 (radialHilbertMeasure D) ∧
      eLpNorm (terminalCapHilbertSource lam D.w χ U.solution) 2 (radialHilbertMeasure D) ≤
        ENNReal.ofReal (terminalConeSourceConstant * exp (-((j : ℝ) * H / 2))) ∧
      ∀ lo hi : ℝ, lo ≤ a → 2 * a ≤ hi →
        0 ≤ (∫ r in lo..hi, terminalCapCutoffEnergy D.w χ U.solution r) / lam ∧
        (∫ r in lo..hi, terminalCapCutoffEnergy D.w χ U.solution r) / lam ≤
          (1 / (j : ℝ)) * (2 * terminalPhysicalCutoffJetConstant 1 ^ 2) *
            exp (-((j : ℝ) * H)) := by
  let c := P.sideRadius right * S.cut right S.chain.index
  let p := P.sideRadius right * S.joinInner right S.chain.index
  let inner := P.sideRadius right * (P.side right).inner
  let a := terminalConeLayerLeft right c H
  let scale := P.sideHeight right * (P.side right).coneScale
  let lam := standInBoundaryScale ((j : ℝ) ^ 2) (D.w p) p
  let χ := terminalPhysicalCutoff right a (2 * a)
  have hD₀ : RadialProfileGeometry (S.family S.sigma) :=
    MorseChainRealization.geometry (hS.2.2.2.1 S.sigma hS.2.2.1).1
  have hm := hS.2.2.2.2.2 right S.chain.index 2 le_rfl (by decide) hband
  have hc : 0 < c := mul_pos (P.sideRadius_pos right) (hD₀.1.trans hm.1.1)
  have hp : 0 < p := mul_pos (P.sideRadius_pos right) (hD₀.1.trans hm.2.2.1.1)
  have hi : 0 < inner := mul_pos (P.sideRadius_pos right) (P.side right).inner_pos
  have hs : 0 < scale := mul_pos (P.sideHeight_pos right) (P.side right).coneScale_pos
  have ha : 0 < a := terminalConeLayerLeft_pos right hc H
  have hj₂ : (2 : ℝ) ≤ j := by exact_mod_cast hj
  have hj₁ : (1 : ℝ) ≤ j := (by norm_num : (1 : ℝ) ≤ 2).trans hj₂
  have hjpos : (0 : ℝ) < j := (by norm_num : (0 : ℝ) < 1).trans_le hj₁
  have hcp : if right then c ≤ p else p ≤ c := by
    have ho := hm.2.2.2.2.1
    cases right
    · exact mul_le_mul_of_nonneg_left ho.2.le (P.sideRadius_pos false).le
    · exact mul_le_mul_of_nonneg_left ho.1.le (P.sideRadius_pos true).le
  have hlen := P.first_physical_cone_length right
  have hinside := terminalConeLayer_inside right hc hi hH' hL hlen
  have hsub : Icc a (2 * a) ⊆ uIcc inner p := by
    cases right
    · change c < a ∧ 2 * a < inner at hinside
      change p ≤ c at hcp
      have hpi : p ≤ inner := by linarith only [hinside.1, hinside.2, hcp, ha]
      rw [uIcc_of_ge hpi]
      intro r hr
      exact ⟨hcp.trans (hinside.1.le.trans hr.1), hr.2.trans hinside.2.le⟩
    · change inner < a ∧ 2 * a < c at hinside
      change c ≤ p at hcp
      have hip : inner ≤ p := by linarith only [hinside.1, hinside.2, hcp, ha]
      rw [uIcc_of_le hip]
      intro r hr
      exact ⟨hinside.1.le.trans hr.1, hr.2.trans (hinside.2.le.trans hcp)⟩
  have hg (r : ℝ) (hr : r ∈ Icc a (2 * a)) :
      D.w =ᶠ[𝓝 r] fun t => scale * t :=
    P.reference_first_cone_germ hw hS hband right hcone (hsub hr)
  have hlam : lam = (j : ℝ) ^ 2 * scale :=
    P.reference_first_boundaryScale hw hS hband right hcone j
  have hsource := terminalConeLayer_actual_source_L2 D right hc hp hi hs hj₁ hH hH' hL
    hlen hcp hD.2.2.1.1 U.smooth hg U.cone_power
  refine ⟨ha, hinside, ?_, ?_, ?_⟩
  · change MemLp (terminalCapHilbertSource lam D.w χ U.solution) 2 (radialHilbertMeasure D)
    rw [hlam]
    exact hsource.1
  · change eLpNorm (terminalCapHilbertSource lam D.w χ U.solution) 2 (radialHilbertMeasure D) ≤ _
    rw [hlam]
    exact hsource.2
  · intro lo high hlo hhi
    change 0 ≤ (∫ r in lo..high, terminalCapCutoffEnergy D.w χ U.solution r) / lam ∧ _
    simp only [hlam]
    have hjet := terminalConeLayer_actual_jets right hc hp hi hjpos.le hH hH' hL
      hlen hcp U.smooth U.cone_power
    refine ⟨(terminalCone_cutoffEnergy_budget right ha hs hjpos hlo hhi hD.2.2.1.1
      U.smooth (fun r hr => (hg r hr).eq_of_nhds) (fun r hr => (hjet r hr).2)).1, ?_⟩
    exact terminalConeLayer_actual_energy right hc hp hi hs hj₁ hH hH' hL hlen hcp hlo hhi
      hD.2.2.1.1 U.smooth (fun r hr => (hg r hr).eq_of_nhds) U.cone_power

end ContinuousFlexibility.Radial
