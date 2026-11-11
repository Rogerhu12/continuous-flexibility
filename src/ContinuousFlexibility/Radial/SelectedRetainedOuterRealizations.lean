import ContinuousFlexibility.Radial.SelectedRetainedRegionalInverse
import ContinuousFlexibility.Radial.SelectedOuterRealizations

/-!
# Actual exterior realizations for one fixed selected band and reference

This supplier constructs the four outer fields of an existing matching
shell. Its natural functions are inputs already fixed by the first- or
later-band construction. The old outer fields and all inner fields are
irrelevant to the construction and are never used as hypotheses.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology ContDiff
open ContinuousFlexibility.Statements ContinuousFlexibility.Analysis

theorem SeedRetainedPair.exists_selectedOuterRealizations {S : SelectedTailData}
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
    (M : RadialMatchingData D) (hfreq : M.frequency = j)
    (hleft : M.innerLeft = P.sideRadius false * S.joinInner false n)
    (hright : M.innerRight = P.sideRadius true * S.joinInner true n)
    (horder : M.innerLeft < M.innerRight)
    (hscale : ∀ i,
      let right := if i = (0 : Fin 2) then false else true
      let c := P.sideRadius right * S.joinInner right n
      M.boundaryScale i = standInBoundaryScale ((j : ℝ) ^ 2) (D.w c) c)
    (hdiag : ∀ i,
      let right := if i = (0 : Fin 2) then false else true
      let c := P.sideRadius right * S.joinInner right n
      (M.A i i, M.B i i) =
        outerUnitState (selectedBoundaryState D j (r07OutwardSign right) c (V right)))
    (hoff : ∀ i k, i ≠ k → M.A i k = 0 ∧ M.B i k = 0)
    (hsource : ∀ F, M.sourceOuter F = modeOuterSource D M.innerLeft M.innerRight F) :
    ∃ RO : RadialModePair D →L[ℝ] RadialModePair D,
      ∃ rep : RadialModePair D → ℝ → ℝ,
        ∃ Q : Fin 2 → RadialModePair D, ∃ p : Fin 2 → ℝ → ℝ,
          MatchingOuterRealizations D
            { M with
              outerInverse := RO
              outerRepresentative := rep
              outerPoisson := Q
              outerFunction := p } := by
  classical
  obtain ⟨R, hR⟩ := P.exists_selectedOuterRegionalInverse hD hw hS G hends hentry hfirst hcut
    hj heven hband V hV hN
  have hcm (right : Bool) : (if right then M.innerRight else M.innerLeft) =
      P.sideRadius right * S.joinInner right n := by
    cases right
    · exact hleft
    · exact hright
  have hcFin (i : Fin 2) : matchingCut D M i =
      P.sideRadius (if i = 0 then false else true) *
        S.joinInner (if i = 0 then false else true) n := by
    fin_cases i
    · exact hleft
    · exact hright
  have ha : D.a < M.innerLeft := by rw [hleft]; exact (hR false).1.1
  have hb : M.innerRight < D.b := by rw [hright]; exact (hR true).1.2
  have hlam (i : Fin 2) : 0 < M.boundaryScale i := by
    rw [hscale i]
    exact (hR (if i = 0 then false else true)).2.1
  have hdata (right : Bool) :
      ∃ R' : Lp ℝ 2 ((radialHilbertMeasure D).restrict
        (radialTailInterval D right (if right then M.innerRight else M.innerLeft))) →L[ℝ]
        Lp ℝ 2 ((radialHilbertMeasure D).restrict
          (radialTailInterval D right (if right then M.innerRight else M.innerLeft))),
        RadialTailWeakPairing D hD right
          (if right then M.innerRight else M.innerLeft) M.frequency R' ∧
          (let i : Fin 2 := if right then 1 else 0
            RadialTailRegularResponse D right (if right then M.innerRight else M.innerLeft)
              (M.boundaryScale i) (M.A i i, M.B i i) R') ∧
          (let i : Fin 2 := if right then 1 else 0
            RadialTailCauchyUnique D right (if right then M.innerRight else M.innerLeft)
              ((M.frequency : ℝ) ^ 2) (M.boundaryScale i) (M.A i i, M.B i i)) := by
    let i : Fin 2 := if right then 1 else 0
    have hi : (if i = 0 then false else true) = right := by
      cases right <;> norm_num [i]
    dsimp only
    rw [hcm right, hfreq, hscale i, hdiag i, hi]
    exact ⟨R right, (hR right).2.2⟩
  choose R' hweak hregular hunique using hdata
  apply exists_outerRealizations_of_regional hD hB M ha horder hb
    (by rwa [hfreq]) hlam _ hsource hoff V hV _ _ R' hweak hregular hunique
  · intro i
    rw [hfreq, hcFin i]
    exact hscale i
  · intro right
    have hi : matchingCut D M (if right then 1 else 0) =
        P.sideRadius right * S.joinInner right n := by
      cases right
      · exact hleft
      · exact hright
    rw [hfreq, hi]
    exact hN right
  · intro i
    have hs : bufferSign i = r07OutwardSign (if i = 0 then false else true) := by
      fin_cases i <;> norm_num [bufferSign, r07OutwardSign]
    rw [hfreq, hcFin i, hs]
    exact hdiag i

end ContinuousFlexibility.Radial
