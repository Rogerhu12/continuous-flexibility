import ContinuousFlexibility.Analysis.RetainedMorsePositiveGapCoordinates
import ContinuousFlexibility.Analysis.MaterialCellEndpointModels

/-!
# Endpoint-coordinate oscillation on the actual retained positive gaps

Every original point is in a cell of index n or n + 1. The same retained
index floor preserves this one-step difference. The actual material
cell comparison consequently bounds the oscillation of endpointX on
the whole closed scaled gap, without a common containing cell.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set
open ContinuousFlexibility.Statements ContinuousFlexibility.Analysis

theorem retainedReference_positive_gap_endpointX_oscillation
    {S : SelectedTailData} {K : SeedCentralCutoff} {q length : ℝ}
    (P : SeedRetainedPair S K q length) (hS : IsSelectedTail S)
    (hband : radialFrequencyBand S.chain S.Cstar S.chain.index 2)
    {Γ : ConnectedReferenceGeometry} (hcoordinates : R11aRetainedCoordinates P Γ)
    {T : MaterialData} (hT : IsMaterialData Γ.reference T) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (side : Bool) (n : ℕ), S.chain.index ≤ n → ∀ r s,
      r ∈ Icc (n06MorsePositiveLeft S.chain side n)
        (n06MorsePositiveRight S.chain side n) →
      s ∈ Icc (n06MorsePositiveLeft S.chain side n)
        (n06MorsePositiveRight S.chain side n) →
      |endpointX 1 (Statements.endpointDistance Γ.reference (P.sideRadius side * r)) -
        endpointX 1 (Statements.endpointDistance Γ.reference (P.sideRadius side * s))| ≤ L := by
  have hdata := hT
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hcompare⟩ := hdata
  obtain ⟨B, A, hB, _, hindexBound⟩ := hcompare
  have htransport := (retainedReference_positive_gap_cell_transport
    P hS hband hcoordinates).1
  obtain ⟨_, N, _, hlabels, hindex, _⟩ := hcoordinates
  have hreal := (hS.2.2.2.1 S.sigma hS.2.2.1).1
  have hfloor (m : ℕ) : Γ.reference.cellIndex m =
      max ((S.family S.sigma).cellIndex m) N := by rw [hindex, hlabels]
  refine ⟨2 * B + 1, by positivity, ?_⟩
  intro side n hn r s hr hs
  obtain ⟨j, hj, hrj⟩ := morseRealization_positive_gap_cell_labels hreal side hn hr
  obtain ⟨k, hk, hsk⟩ := morseRealization_positive_gap_cell_labels hreal side hn hs
  have hidx (m : ℕ)
      (hm : (S.family S.sigma).cellIndex m = n ∨
        (S.family S.sigma).cellIndex m = n + 1) :
      max n N ≤ Γ.reference.cellIndex m ∧
        Γ.reference.cellIndex m ≤ max (n + 1) N := by
    rw [hfloor m]
    rcases hm with hm | hm
    · rw [hm]
      exact ⟨le_rfl, max_le_max (Nat.le_succ n) le_rfl⟩
    · rw [hm]
      exact ⟨max_le_max (Nat.le_succ n) le_rfl, le_rfl⟩
  have hjidx := hidx j hj
  have hkidx := hidx k hk
  have hsucc : max (n + 1) N ≤ max n N + 1 :=
    max_le (Nat.succ_le_succ (le_max_left n N))
      ((le_max_right n N).trans (Nat.le_succ _))
  have hjk : Γ.reference.cellIndex j ≤ Γ.reference.cellIndex k + 1 :=
    hjidx.2.trans (hsucc.trans (Nat.succ_le_succ hkidx.1))
  have hkj : Γ.reference.cellIndex k ≤ Γ.reference.cellIndex j + 1 :=
    hkidx.2.trans (hsucc.trans (Nat.succ_le_succ hjidx.1))
  have hjk' : (Γ.reference.cellIndex j : ℝ) ≤ Γ.reference.cellIndex k + 1 := by
    exact_mod_cast hjk
  have hkj' : (Γ.reference.cellIndex k : ℝ) ≤ Γ.reference.cellIndex j + 1 := by
    exact_mod_cast hkj
  have hrX := abs_le.mp (hindexBound j (P.sideRadius side * r)
    (htransport side n hn j r hr hrj)).1
  have hsX := abs_le.mp (hindexBound k (P.sideRadius side * s)
    (htransport side n hn k s hs hsk)).1
  exact abs_le.mpr ⟨by linarith only [hrX.1, hsX.2, hkj'],
    by linarith only [hrX.2, hsX.1, hjk']⟩

end ContinuousFlexibility.Radial
