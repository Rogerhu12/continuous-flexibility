import ContinuousFlexibility.Radial.SelectedLaterCapData
import ContinuousFlexibility.Radial.TerminalMorseCapExtension
import ContinuousFlexibility.Radial.TerminalMorseRelativeSource
import ContinuousFlexibility.Radial.TerminalMorseEnergyBudget

/-!
# Source and energy of the actual later terminal cutoffs

Both errors use the selected incoming solution, its actual matching
slope and the same physical cutoff. The coefficient powers are fixed
before the selected sequence, radius dilations and profile heights.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real MeasureTheory
open scoped ContDiff ENNReal
open ContinuousFlexibility.Statements

def SeedRetainedPair.laterTerminalCutoff {S : SelectedTailData} {K : SeedCentralCutoff}
    {q length : ℝ} (P : SeedRetainedPair S K q length)
    (G : MorseChainGeometryWitness S.chain) (n : ℕ) (side : Bool) : ℝ → ℝ :=
  terminalMorsePhysicalCutoff side (morseChainA S.chain (n - 1)) (morseChainB S.chain (n - 1))
    (P.sideRadius side * G.factor side (n - 1 - S.chain.index))
    (G.normal (n - 1 - S.chain.index))

theorem SeedRetainedPair.reference_later_cutoff_source_energy {S : SelectedTailData}
    {K : SeedCentralCutoff} {q length : ℝ} (P : SeedRetainedPair S K q length)
    {D : ReferenceData} (hD : RadialProfileGeometry D) (hw : D.w = P.pair.profile)
    (hS : IsSelectedTail S) (G : MorseChainGeometryWitness S.chain)
    (hentry : S.entry = r07CellEntry S.chain)
    (hfirst : radialFrequencyBand S.chain S.Cstar S.chain.index 2)
    (hC : 1000 ≤ S.Cstar) (side : Bool) {n j : ℕ}
    (hn : S.chain.index < n) (hj : 2 ≤ j) (heven : Even j)
    (hband : radialFrequencyBand S.chain S.Cstar n j)
    (hcut : S.cut side n = r07PreviousCellCut S.chain side (n - 1))
    (hjoin : S.joinInner side n = r07PreviousCellJoin S.chain side (n - 1))
    (hu : ContDiff ℝ ∞ (S.incoming side j))
    (haction : 1000000000 ≤ (j : ℝ) * sqrt (morseChainA S.chain (n - 1))) :
    let m := n - 1
    let A := morseChainA S.chain m
    let B := morseChainB S.chain m
    let r := G.normal (m - S.chain.index)
    let s := P.sideRadius side * G.factor side (m - S.chain.index)
    let U := radialRadiusScale (P.sideRadius side) 1 (S.incoming side j)
    let χ := P.laterTerminalCutoff G n side
    let p := P.sideRadius side * S.joinInner side n
    let lam := standInBoundaryScale ((j : ℝ) ^ 2) (D.w p) p
    let d := standInBoundarySlope (r07OutwardSign side) ((j : ℝ) ^ 2) p U
    let σ := (j : ℝ) * sqrt A / 100000000
    MemLp (terminalCapHilbertSource lam D.w χ U) 2 (radialHilbertMeasure D) ∧
      eLpNorm (terminalCapHilbertSource lam D.w χ U) 2 (radialHilbertMeasure D) ≤
        ENNReal.ofReal ((sqrt d * radialE n ^ terminalMorseRelativeSourceExponent) * exp (-σ)) ∧
      ∀ lo hi : ℝ, lo ≤ terminalMorseLayerRadius side A B s r 0 →
        terminalMorseLayerRadius side A B s r (terminalMorseLayerLength side A) ≤ hi →
        0 ≤ (∫ z in lo..hi, terminalCapCutoffEnergy D.w χ U z) / lam ∧
          (∫ z in lo..hi, terminalCapCutoffEnergy D.w χ U z) / lam ≤
            d * radialE n ^ terminalMorseEnergyErrorExponent * exp (-2 * σ) := by
  let m := n - 1
  let A := morseChainA S.chain m
  let B := morseChainB S.chain m
  let r := G.normal (m - S.chain.index)
  let s := P.sideRadius side * G.factor side (m - S.chain.index)
  let U := radialRadiusScale (P.sideRadius side) 1 (S.incoming side j)
  let p := P.sideRadius side * S.joinInner side n
  let lam := standInBoundaryScale ((j : ℝ) ^ 2) (D.w p) p
  let d := standInBoundarySlope (r07OutwardSign side) ((j : ℝ) ^ 2) p U
  have hm : S.chain.index ≤ m := by dsimp only [m]; omega
  have hn₁ : 1 ≤ n := by omega
  have hj₀ : (0 : ℝ) < j := by exact_mod_cast (by omega : 0 < j)
  obtain ⟨hs, hscale, hr, hU, hweight, hode, hzero, hnorm, hinit⟩ :=
    P.reference_later_cap_data hw hS G hentry hfirst hC side hn hj heven hband hcut hjoin hu
  obtain ⟨hB, hAB, hA₀, hBAlo, hBAhi⟩ := G.cell_terminal_parameters hm
  have hp : s * r (if side then morseRightCapEnd A B (1 / 100) else morseCellLeftCut) = p := by
    have he := (G.scaled_previousCap_endpoints (P.sideRadius side) side hm).2
    rw [← hjoin] at he
    exact he
  have hlam : lam = standInBoundaryScale ((j : ℝ) ^ 2)
      (D.w (s * r (if side then morseRightCapEnd A B (1 / 100) else morseCellLeftCut)))
      (s * r (if side then morseRightCapEnd A B (1 / 100) else morseCellLeftCut)) := by
    rw [hp]
  have hsource := terminalMorse_cutoff_source_relative_radialE D S.chain side m n
    (G.d_exact m) (Nat.sub_le _ _) hn₁ hB hAB hj₀ hs hscale hA₀ hBAlo hBAhi hr
    hD.2.2.1.1 hU hweight hode hzero hnorm hinit haction hlam
  have henergy := terminalMorseCapLift_energy_error_radialE S.chain side m n
    (G.d_exact m) (Nat.sub_le _ _) hn₁ hB hAB hj₀ hs hscale hA₀ hBAlo hBAhi hr
    hD.2.2.1.1 hU hweight hode hzero hnorm hinit haction hlam
  have hd : 0 < d :=
    (P.reference_later_incoming_data hw hS G hentry hfirst hC side
      hn hj heven hband hcut hjoin hu).2.2.2.2.2.1
  refine ⟨hsource.1, ?_, ?_⟩
  · simpa only [hp, r07OutwardSign] using hsource.2
  · intro lo hi hlo hhi
    change 0 ≤ (∫ z in lo..hi,
        terminalCapCutoffEnergy D.w (terminalMorsePhysicalCutoff side A B s r) U z) / lam ∧ _
    rw [terminalMorse_cutoffEnergy_integral_cap side hB hAB hs hr hD.2.2.1.1 hU hlo hhi]
    refine ⟨henergy.1, ?_⟩
    have he : (∫ z in (terminalMorseLayerRadius side A B s r 0)..
        (terminalMorseLayerRadius side A B s r (terminalMorseLayerLength side A)),
        terminalCapCutoffEnergy D.w (terminalMorsePhysicalCutoff side A B s r) U z) / lam ≤
        d * radialE n ^ terminalMorseEnergyErrorExponent *
          exp (-2 * ((j : ℝ) * sqrt A / 50000000)) := by
      simpa only [hp, r07OutwardSign] using henergy.2.1
    apply he.trans
    apply mul_le_mul_of_nonneg_left _
      (mul_nonneg hd.le (Real.rpow_nonneg (show 0 ≤ radialE n from (exp_pos _).le) _))
    apply exp_le_exp.mpr
    have ha : 0 ≤ (j : ℝ) * sqrt A := mul_nonneg hj₀.le (sqrt_nonneg A)
    linarith only [ha]

end ContinuousFlexibility.Radial
