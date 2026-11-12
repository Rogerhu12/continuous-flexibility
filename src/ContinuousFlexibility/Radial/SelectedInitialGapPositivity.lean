import ContinuousFlexibility.Radial.R07MiddlePreservation

/-!
# Positivity on the original selected cut-to-entry bridges

The original replacement middle is strictly increasing on its entire
closed interval. Its full profile germs preserve that fact through both
seams. The selected cut order places each first cut-to-entry bridge
inside this interval, including the part beyond the first matching join.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set
open scoped ContDiff
open ContinuousFlexibility.Statements

theorem r07MiddleReferenceFamily_deriv_pos {T : MorseChainData}
    (G : MorseChainGeometryWitness T) {M phi : ℝ → ℝ}
    (hM : R07MiddleAdmissible G M) (sigma : ℕ → ℝ)
    (hsigma : ∀ n, 1 ≤ sigma n ∧ sigma n ≤ 2) {r : ℝ}
    (hr : r ∈ Icc (morseChainCellRightRadius T false 0)
      (morseChainCellLeftRadius T true 0)) :
    0 < deriv (r07MiddleReferenceFamily G M phi sigma).w r := by
  have hg := (r07MiddlePatchedProfile_germs G hM sigma hsigma).2 r hr
  rw [r07MiddleReferenceFamily_admissible G M phi sigma hsigma]
  change 0 < deriv (r07MiddlePatchedProfile G M sigma hsigma) r
  rw [hg.deriv_eq, deriv_const_mul_field]
  exact mul_pos (morseChainAmplitude_pos T sigma hsigma T.index) (hM.2.2.2.2 r hr)

theorem selected_initial_span_mem_middle {S : SelectedTailData}
    (hS : IsSelectedTail S)
    (hband : radialFrequencyBand S.chain S.Cstar S.chain.index 2)
    (hentry : S.entry = r07CellEntry S.chain)
    (hcuts : S.cut false S.chain.index < S.cut true S.chain.index)
    (side : Bool) {r : ℝ}
    (hr : r ∈ uIcc (S.cut side S.chain.index) (S.entry side S.chain.index)) :
    r ∈ Icc (morseChainCellRightRadius S.chain false 0)
      (morseChainCellLeftRadius S.chain true 0) := by
  have hL := (hS.2.2.2.2.2 false S.chain.index 2 le_rfl (by decide) hband).2.2.2.2.1
  have hR := (hS.2.2.2.2.2 true S.chain.index 2 le_rfl (by decide) hband).2.2.2.2.1
  have heL : S.entry false S.chain.index < S.cut false S.chain.index := hL.1.trans hL.2
  have heR : S.cut true S.chain.index < S.entry true S.chain.index := hR.1.trans hR.2
  have hm : r ∈ Icc (S.entry false S.chain.index) (S.entry true S.chain.index) := by
    cases side
    · rw [uIcc_of_ge heL.le] at hr
      exact ⟨hr.1, hr.2.trans (hcuts.trans heR).le⟩
    · rw [uIcc_of_le heR.le] at hr
      exact ⟨(heL.trans hcuts).le.trans hr.1, hr.2⟩
  simpa only [hentry, r07CellEntry, morseChainCellRightRadius, morseChainCellLeftRadius,
    Bool.false_eq_true, ite_false, ite_true, Nat.add_zero] using hm

/-- This is a consequence of the actual selected-family constructor,
not an additional condition on an arbitrary selected tail. -/
theorem selected_initial_bridge_deriv_pos {S : SelectedTailData}
    (hS : IsSelectedTail S)
    (hband : radialFrequencyBand S.chain S.Cstar S.chain.index 2)
    (hentry : S.entry = r07CellEntry S.chain)
    (hcuts : S.cut false S.chain.index < S.cut true S.chain.index)
    (G : MorseChainGeometryWitness S.chain) {M phi : ℝ → ℝ}
    (hM : R07MiddleAdmissible G M)
    (hfamily : S.family = r07MiddleReferenceFamily G M phi)
    (side : Bool) {r : ℝ}
    (hr : r ∈ uIcc (S.cut side S.chain.index) (S.entry side S.chain.index)) :
    0 < deriv (S.family S.sigma).w r := by
  rw [hfamily]
  exact r07MiddleReferenceFamily_deriv_pos G hM S.sigma hS.2.2.1
    (selected_initial_span_mem_middle hS hband hentry hcuts side hr)

end ContinuousFlexibility.Radial
