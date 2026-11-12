import ContinuousFlexibility.Radial.SelectedOuterGraphUniqueness
import ContinuousFlexibility.Radial.SelectedFirstNaturalTransport
import ContinuousFlexibility.Radial.SelectedOuterPoisson
import ContinuousFlexibility.Radial.MatchedPiecesAssembly

/-!
# Installing the constructed exterior inverse and Poisson columns

Only the four exterior fields are installed. All frequencies, cuts,
physical scales, source restrictions and diagonal boundary rows belong to
the given common matching datum. Poisson columns are constructed from the
same prescribed natural functions used to identify the inverse's domain.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory Real
open scoped Topology ContDiff
open ContinuousFlexibility.Statements ContinuousFlexibility.Analysis

theorem exists_outerRealizations_of_regional {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D) (M : RadialMatchingData D)
    (ha : D.a < M.innerLeft) (hm : M.innerLeft < M.innerRight) (hb : M.innerRight < D.b)
    (hj : 2 ≤ M.frequency) (hlam : ∀ i, 0 < M.boundaryScale i)
    (hscale : ∀ i, M.boundaryScale i = standInBoundaryScale ((M.frequency : ℝ) ^ 2)
      (D.w (matchingCut D M i)) (matchingCut D M i))
    (hsource : ∀ F, M.sourceOuter F = modeOuterSource D M.innerLeft M.innerRight F)
    (hoff : ∀ i k, i ≠ k → M.A i k = 0 ∧ M.B i k = 0)
    (V : Bool → ℝ → ℝ) (hV : ∀ right, ContDiff ℝ ∞ (V right))
    (hN : ∀ right, RadialNaturalTail D right M.frequency
      (matchingCut D M (if right then 1 else 0)) (V right))
    (hdiag : ∀ i, (M.A i i, M.B i i) = outerUnitState
      (selectedBoundaryState D M.frequency (bufferSign i) (matchingCut D M i)
        (V (if i = 0 then false else true))))
    (R : ∀ right : Bool,
      Lp ℝ 2 ((radialHilbertMeasure D).restrict
        (radialTailInterval D right (if right then M.innerRight else M.innerLeft))) →L[ℝ]
      Lp ℝ 2 ((radialHilbertMeasure D).restrict
        (radialTailInterval D right (if right then M.innerRight else M.innerLeft))))
    (hweak : ∀ right, RadialTailWeakPairing D hD right
      (if right then M.innerRight else M.innerLeft) M.frequency (R right))
    (hregular : ∀ right,
      let i : Fin 2 := if right then 1 else 0
      RadialTailRegularResponse D right (if right then M.innerRight else M.innerLeft)
        (M.boundaryScale i) (M.A i i, M.B i i) (R right))
    (hunique : ∀ right,
      let i : Fin 2 := if right then 1 else 0
      RadialTailCauchyUnique D right (if right then M.innerRight else M.innerLeft)
        ((M.frequency : ℝ) ^ 2) (M.boundaryScale i) (M.A i i, M.B i i)) :
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
  let RO := radialOuterPairOperator D M.innerLeft M.innerRight (R false) (R true)
  have hgraph (F : RadialModePair D) : ModeOuterSeparatedGraph D M (RO F) F :=
    radialOuterPairOperator_graph hD hB M ha hm hb hlam R hweak hregular F
  have huniq {U F : RadialModePair D} (hU : ModeOuterSeparatedGraph D M U F) : RO F = U :=
    radialOuterPairOperator_unique hD hB M ha hm hb hlam R hweak hregular hunique hU
  have hreps (F : RadialModePair D) := (hgraph (M.sourceOuter F)).2.2
  choose rep hrep hreg hzero hboundary using hreps
  have hjn : (M.frequency : ℝ) ≠ 0 := by exact_mod_cast (by omega : M.frequency ≠ 0)
  have hpoisson (i : Fin 2) : ∃ Q : RadialModePair D, ∃ p : ℝ → ℝ,
      (Q.1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] p ∧
      (Q.1 : ℝ → ℝ) =ᵐ[(radialHilbertMeasure D).restrict
        (Ioo M.innerLeft M.innerRight)] (fun _ => 0) ∧
      ContDiffOn ℝ 2 p (Ioc D.a M.innerLeft ∪ Ico M.innerRight D.b) ∧
      Q.2 = 0 ∧ ModeLocalEquation D M.frequency (matchingOuterRegion D M) Q 0 ∧
      ∀ k, p (matchingCut D M k) = M.A k i / sqrt (M.boundaryScale k) ∧
        matchingOuterFlux D M p k = M.B k i := by
    let right : Bool := if i = 0 then false else true
    have hi : (if right then (1 : Fin 2) else 0) = i := by
      fin_cases i <;> norm_num [right]
    have hstate : selectedBoundaryState D M.frequency
        (bufferSign (if right then 1 else 0)) (matchingCut D M (if right then 1 else 0))
        (V right) ≠ 0 := by
      apply selectedBoundaryState_ne_zero_of_natural (matchingProfileGeometry hD) hjn
        (matchingCut_mem_core_of_geometry ha hm hb _) _ (hV right) (hN right)
      cases right <;> norm_num [bufferSign]
    obtain ⟨Q, p, _, hrepQ, hzeroQ, _, hregQ, hscalarQ, heqQ, _, htraces⟩ :=
      exists_selectedOuterPoisson hD M ha hm hb right (hV right) (hN right)
        (hlam _) (hscale _) hstate
    refine ⟨Q, p, hrepQ, hzeroQ, hregQ, hscalarQ, heqQ, ?_⟩
    intro k
    have ht := htraces k
    rw [hi] at ht
    have hAB : outerUnitState (selectedBoundaryState D M.frequency (bufferSign i)
        (matchingCut D M i) (V right)) = (M.A i i, M.B i i) := (hdiag i).symm
    rw [hAB] at ht
    by_cases hki : k = i
    · subst k
      simpa only [ite_true, Prod.fst, Prod.snd] using ht
    · simpa only [if_neg hki, (hoff k i hki).1, (hoff k i hki).2, zero_div] using ht
  choose Q p hQ using hpoisson
  refine ⟨RO, rep, Q, p, ?_⟩
  refine ⟨fun F _ => hgraph (M.sourceOuter F), fun _ _ h => huniq h, ?_, ?_, hQ⟩
  · intro F
    rw [hsource F]
    exact ⟨(modeRegionSources_spec D M.innerLeft M.innerRight F).2.1,
      (modeRegionSources_spec D M.innerLeft M.innerRight F).2.2.2⟩
  · intro F
    exact ⟨hrep F, (hgraph (M.sourceOuter F)).1, hreg F, hzero F,
      (hgraph (M.sourceOuter F)).2.1, hboundary F⟩

end ContinuousFlexibility.Radial
