module

public import ContinuousFlexibility.Radial.MatchedCellBounds
public import ContinuousFlexibility.Radial.MatchedModeLocalization
public import ContinuousFlexibility.Radial.MatchingSourcePairing
public import ContinuousFlexibility.Radial.MatchingGraphRestrictions

/-!
# Actual source rows in localized matching bounds

The frozen local realization clauses make the source maps genuine
orthogonal restrictions. The inner and outer Poisson columns are fixed
by their respective restrictions. This removes the source-row and
source-map hypotheses from the matching matrix estimate.

The local inverse norms and the four column norms remain separate:
the actual buffer decomposition can then distinguish the leading
column from the exponentially small return into the interior.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Statements

theorem actualMatchedRepresentation_localRealizations {D : ReferenceData}
    {G : RadialModePair D →L[ℝ] RadialModePair D} {M : RadialMatchingData D}
    (hM : ActualMatchedRepresentation D G M) : MatchingLocalRealizations D M := by
  rcases hM with ⟨_, _, _, _, _, _, _, _, hlocal, _⟩
  exact hlocal

theorem matchedMode_inner_row {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {M : RadialMatchingData D}
    (hM : MatchingLocalRealizations D M)
    (Q : RadialModePair D →L[ℝ] RadialModePair D)
    (hQ : ∀ U F, modePairing D U (Q F) = modePairing D (Q U) F)
    (i : Fin 2) (F : RadialModePair D) :
    modePairing D (M.innerPoisson i) (M.sourceInner (Q F)) =
      modePairing D (Q (M.innerPoisson i)) F := by
  rw [matchingSourceInner_pairing_of_fixed D M hM _ _
    (matching_sourceInner_innerPoisson hD hM i)]
  exact hQ _ _

theorem matchedMode_outer_row {D : ReferenceData}
    {M : RadialMatchingData D} (hM : MatchingLocalRealizations D M)
    (Q : RadialModePair D →L[ℝ] RadialModePair D)
    (hQ : ∀ U F, modePairing D U (Q F) = modePairing D (Q U) F)
    (i : Fin 2) (F : RadialModePair D) :
    modePairing D (M.outerPoisson i) (M.sourceOuter (Q F)) =
      modePairing D (Q (M.outerPoisson i)) F := by
  rw [matchingSourceOuter_pairing_of_fixed D M hM _ _
    (matching_sourceOuter_outerPoisson hM i)]
  exact hQ _ _

/-- The bound for the actual source restrictions. Both the field-cell
maps and the separate border map satisfy the pairing symmetry hQ.
There are no assumed source-row identities in this statement. -/
theorem matchedMode_actual_opNorm_bound {D : ReferenceData}
    (hD : IsAccumulatingProfile D)
    {G : RadialModePair D →L[ℝ] RadialModePair D} {M : RadialMatchingData D}
    (hM : ActualMatchedRepresentation D G M)
    (P Q : RadialModePair D →L[ℝ] RadialModePair D)
    (hQ : ∀ U F, modePairing D U (Q F) = modePairing D (Q U) F)
    {I O p v h o : ℝ}
    (hI₀ : 0 ≤ I) (hO₀ : 0 ≤ O) (hp : 0 ≤ p) (hv : 0 ≤ v)
    (hh : 0 ≤ h) (ho : 0 ≤ o)
    (hI : ‖P ∘L M.innerInverse ∘L
      matchingSourceInnerCLM D M (actualMatchedRepresentation_localRealizations hM) ∘L Q‖ ≤ I)
    (hO : ‖P ∘L M.outerInverse ∘L
      matchingSourceOuterCLM D M (actualMatchedRepresentation_localRealizations hM) ∘L Q‖ ≤ O)
    (hP : ∀ i, ‖P (M.innerPoisson i)‖ ≤ p)
    (hV : ∀ i, ‖P (M.outerPoisson i)‖ ≤ v)
    (hH : ∀ i, ‖Q (M.innerPoisson i)‖ ≤ h)
    (hW : ∀ i, ‖Q (M.outerPoisson i)‖ ≤ o) :
    ‖P ∘L G ∘L Q‖ ≤ I + O +
      (16 * (4 / M.margin) * (p * h) + 8 * (4 / M.margin) * (p * o) +
        (96 * (4 / M.margin) + 8) * (v * h) +
        48 * (4 / M.margin) * (v * o)) := by
  let hlocal := actualMatchedRepresentation_localRealizations hM
  exact matchedCell_opNorm_bound hM P Q
    (matchingSourceInnerCLM D M hlocal) (matchingSourceOuterCLM D M hlocal)
    (matchingSourceInnerCLM_apply D M hlocal) (matchingSourceOuterCLM_apply D M hlocal)
    hI₀ hO₀ hp hv hh ho hI hO hP hV hH hW
    (matchedMode_inner_row hD hlocal Q hQ)
    (matchedMode_outer_row hlocal Q hQ)

end ContinuousFlexibility.Radial
