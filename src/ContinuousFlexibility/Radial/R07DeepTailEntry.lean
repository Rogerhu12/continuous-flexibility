module

public import ContinuousFlexibility.Radial.R07DeepTailData
public import ContinuousFlexibility.Radial.R07ChainIncoming
public import ContinuousFlexibility.Radial.MorseChainProfileGluing

/-!
# Ordering the deep entrance beyond a prescribed cell
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real
open ContinuousFlexibility.Statements

theorem r07_deepPhysicalEntrance_core {T : MorseChainData} {D : ReferenceData}
    {σ C : ℕ → ℝ} (h : MorseChainRealization T σ D C)
    (right : Bool) {start : ℕ} (hstart : T.index < start) :
    (if right then r07MassNodeRadius T right start
      else morseChainResistanceEnd T right start) ∈ radialCore D := by
  cases right
  · exact r07_chain_resistanceEnd_core h false hstart
  · exact (r07_chain_mass_nodes_core h true hstart.le).1

/-- Moving the deep start at least two cells past the matching index
places its physical entrance strictly farther out, in either direction. -/
theorem r07_deepPhysicalEntrance_after_entry {T : MorseChainData} {D : ReferenceData}
    (G : MorseChainGeometryWitness T) {σ C : ℕ → ℝ}
    (h : MorseChainRealization T σ D C) (right : Bool) {n start : ℕ}
    (hn : T.index ≤ n) (hstart : n + 2 ≤ start) :
    let f := if right then r07MassNodeRadius T right start
      else morseChainResistanceEnd T right start
    if right then r07CellEntry T right n < f else f < r07CellEntry T right n := by
  have hs : T.index ≤ start := by omega
  have hnEq : T.index + (n - T.index) = n := by omega
  have hsEq : T.index + (start - T.index) = start := by omega
  cases right
  · have hp : T.index ≤ start - 1 := by omega
    have hpEq : T.index + (start - 1 - T.index) = start - 1 := by omega
    have hsuc : start - 1 + 1 = start := by omega
    have hf : morseChainResistanceEnd T false start =
        T.radius false (start - 1) (T.leftX false (start - 1)) := by
      simpa only [hsuc] using (r07_chain_resistance_ends h hp).2
    let P := morseChainLeftProfileData G (fun _ => 1) (fun _ => ⟨le_rfl, by norm_num⟩)
    have hm := P.enter_strictMono.monotone
      (show n - T.index ≤ start - 1 - T.index by omega)
    have hle : T.radius false (start - 1) (T.rightX false (start - 1)) ≤
        T.radius false n (T.rightX false n) := by
      change -morseChainCellRightRadius T false (n - T.index) ≤
        -morseChainCellRightRadius T false (start - 1 - T.index) at hm
      simpa only [morseChainCellRightRadius, hnEq, hpEq, neg_le_neg_iff] using hm
    have hc := r07_chain_model_cuts h false hp
    change morseChainResistanceEnd T false start < T.radius false n (T.rightX false n)
    rw [hf]
    exact (hc.1.trans hc.2).trans_le hle
  · let P := morseChainRightProfileData G (fun _ => 1) (fun _ => ⟨le_rfl, by norm_num⟩)
    have hm := P.enter_strictMono (show n - T.index < start - T.index by omega)
    change morseChainCellLeftRadius T true (n - T.index) <
      morseChainCellLeftRadius T true (start - T.index) at hm
    simpa only [morseChainCellLeftRadius, hnEq, hsEq, r07CellEntry,
      r07MassNodeRadius, if_true] using hm

end ContinuousFlexibility.Radial
