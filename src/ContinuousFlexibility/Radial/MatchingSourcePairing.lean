import ContinuousFlexibility.Radial.MatchingInverseFormula

/-!
# Pairing identities for the actual source restrictions

The source fields are orthogonal restrictions for the existing modal
pairing. These identities use their frozen almost-everywhere clauses,
including the scalar coordinate.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped InnerProductSpace

theorem matchingSourceInner_pairing (D : ReferenceData) (M : RadialMatchingData D)
    (hM : MatchingLocalRealizations D M) (U F : RadialModePair D) :
    modePairing D U (M.sourceInner F) = modePairing D (M.sourceInner U) F := by
  have hfield :
      ⟪U.1, (M.sourceInner F).1⟫_ℝ = ⟪(M.sourceInner U).1, F.1⟫_ℝ := by
    rw [L2.inner_def, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(hM.2.2.2.1 F).2.2.1, (hM.2.2.2.1 U).2.2.1]
      with r hF hU
    rw [hF, hU]
    simp only [RCLike.inner_apply, conj_trivial]
    by_cases hr : r ∈ Ioo M.innerLeft M.innerRight <;> simp [hr]
  unfold modePairing
  rw [hfield, (hM.2.2.2.1 F).1, (hM.2.2.2.1 U).1]

theorem matchingSourceOuter_pairing (D : ReferenceData) (M : RadialMatchingData D)
    (hM : MatchingLocalRealizations D M) (U F : RadialModePair D) :
    modePairing D U (M.sourceOuter F) = modePairing D (M.sourceOuter U) F := by
  have hfield :
      ⟪U.1, (M.sourceOuter F).1⟫_ℝ = ⟪(M.sourceOuter U).1, F.1⟫_ℝ := by
    rw [L2.inner_def, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(hM.2.2.2.1 F).2.2.2, (hM.2.2.2.1 U).2.2.2]
      with r hF hU
    rw [hF, hU]
    simp only [RCLike.inner_apply, conj_trivial]
    by_cases hr : r ∈ Ioo M.innerLeft M.innerRight <;> simp [hr]
  unfold modePairing
  rw [hfield, (hM.2.2.2.1 F).2.1, (hM.2.2.2.1 U).2.1]
  simp

theorem matchingSourceInner_pairing_of_fixed (D : ReferenceData)
    (M : RadialMatchingData D) (hM : MatchingLocalRealizations D M)
    (U F : RadialModePair D) (hU : M.sourceInner U = U) :
    modePairing D U (M.sourceInner F) = modePairing D U F := by
  rw [matchingSourceInner_pairing D M hM, hU]

theorem matchingSourceOuter_pairing_of_fixed (D : ReferenceData)
    (M : RadialMatchingData D) (hM : MatchingLocalRealizations D M)
    (U F : RadialModePair D) (hU : M.sourceOuter U = U) :
    modePairing D U (M.sourceOuter F) = modePairing D U F := by
  rw [matchingSourceOuter_pairing D M hM, hU]

end ContinuousFlexibility.Statements
