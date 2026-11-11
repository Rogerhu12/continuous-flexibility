import ContinuousFlexibility.Radial.SelectedRetainedOuterRealizations
import ContinuousFlexibility.Radial.SelectedTerminalMatching
import ContinuousFlexibility.Radial.SelectedTerminalOuterSupply

/-!
# The actual exterior construction supplies either terminal matching shell

The same fixed natural functions determine the boundary rows and the actual
outer inverse. Installing an arbitrary inner operator leaves this construction
unchanged, so the result applies to both first and later frequency bands.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

theorem SeedRetainedPair.selectedTerminal_outerSupply {S : SelectedTailData}
    {K : SeedCentralCutoff} {q length : ℝ} (P : SeedRetainedPair S K q length)
    {D : ReferenceData} (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D)
    (hw : D.w = P.pair.profile)
    (hS : IsSelectedTail S) (G : MorseChainGeometryWitness S.chain)
    (hends : ∀ sigma tau, (S.family sigma).a = (S.family tau).a ∧
      (S.family sigma).b = (S.family tau).b)
    (hentry : S.entry = r07CellEntry S.chain)
    (hfirst : radialFrequencyBand S.chain S.Cstar S.chain.index 2)
    (hcut : ∀ right n, S.chain.index < n →
      S.cut right n = r07PreviousCellCut S.chain right (n - 1))
    {n j : ℕ} (hj : 2 ≤ j) (heven : Even j)
    (hband : radialFrequencyBand S.chain S.Cstar n j)
    (V : Bool → ℝ → ℝ) (hV : ∀ right, ContDiff ℝ ∞ (V right))
    (hN : ∀ right, RadialNaturalTail D right j
      (P.sideRadius right * S.joinInner right n) (V right))
    (horder : P.sideRadius false * S.joinInner false n <
      P.sideRadius true * S.joinInner true n)
    (margin : ℝ) (slope : Bool → ℝ) :
    SelectedTerminalOuterSupply (selectedTerminalMatching D j n margin
      (fun right => P.sideRadius right * S.joinInner right n) slope
      (fun right => outerUnitState (selectedBoundaryState D j (r07OutwardSign right)
        (P.sideRadius right * S.joinInner right n) (V right)))) := by
  let cut := fun right => P.sideRadius right * S.joinInner right n
  let boundary := fun right => outerUnitState
    (selectedBoundaryState D j (r07OutwardSign right) (cut right) (V right))
  let base := selectedTerminalMatching D j n margin cut slope boundary
  intro A u
  let M : RadialMatchingData D := { base with innerInverse := A, innerRepresentative := u }
  have hdiag (i : Fin 2) : (M.A i i, M.B i i) =
      boundary (selectedTerminalSide i) := by
    have hi := selectedTerminalMatching_diagonal D j n margin cut slope boundary i
    exact Prod.ext hi.1 hi.2
  have hoff : ∀ i k, i ≠ k → M.A i k = 0 ∧ M.B i k = 0 :=
    selectedTerminalMatching_offDiagonal D j n margin cut slope boundary
  exact P.exists_selectedOuterRealizations hD hB hw hS G hends hentry hfirst hcut
    hj heven hband V hV hN M rfl rfl rfl horder (fun _ => rfl)
    hdiag hoff (fun _ => rfl)

end ContinuousFlexibility.Radial
