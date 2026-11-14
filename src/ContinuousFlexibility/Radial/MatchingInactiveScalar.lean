module

public import ContinuousFlexibility.Radial.MatchingInverseFormula
public import ContinuousFlexibility.Radial.ModeWeakLinearity

/-!
# The inactive scalar in the exact matching formula

At frequencies different from two, the scalar coordinate carries no
equation. The frozen local uniqueness clauses force the matching formula
to annihilate a purely scalar source. This is proved from the actual
local graphs and is not added as a condition on the supplied inverse.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped InnerProductSpace BigOperators
open ContinuousFlexibility.Radial

def matchingFormulaValue (D : ReferenceData) (M : RadialMatchingData D)
    (F : RadialModePair D) : RadialModePair D :=
  let fh := M.sourceInner F
  let fo := M.sourceOuter F
  let h := fun i => modePairing D (M.innerPoisson i) fh
  let o := fun i => modePairing D (M.outerPoisson i) fo
  let x := radialMatrixApply M.Kinv (fun i => o i + radialMatrixApply M.A h i)
  let y := fun i => radialMatrixApply
    (fun a b => M.A a b + radialMatrixProduct M.B M.Db a b) x i -
      radialMatrixApply M.B h i
  M.innerInverse fh + M.outerInverse fo +
    (∑ i, x i • M.innerPoisson i) + (∑ i, y i • M.outerPoisson i)

theorem ActualMatchedRepresentation.formula {D : ReferenceData}
    {G : RadialModePair D →L[ℝ] RadialModePair D} {M : RadialMatchingData D}
    (h : ActualMatchedRepresentation D G M) (F : RadialModePair D) :
    G F = matchingFormulaValue D M F := by
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hformula⟩
  exact hformula F

theorem modeLocalEquation_congr_source_fst {D : ReferenceData}
    {j : ℕ} {J : Set ℝ} {U F H : RadialModePair D} (hFH : F.1 = H.1) :
    ModeLocalEquation D j J U F ↔ ModeLocalEquation D j J U H := by
  unfold ModeLocalEquation
  simp only [hFH]

theorem matchingSourceInner_fst_eq_zero {D : ReferenceData}
    {M : RadialMatchingData D} (hM : MatchingLocalRealizations D M)
    {F : RadialModePair D} (hF : F.1 = 0) : (M.sourceInner F).1 = 0 := by
  have hs := (hM.2.2.2.1 F).2.2.1
  rw [hF] at hs
  apply Lp.ext
  filter_upwards [hs, Lp.coeFn_zero ℝ 2 (radialHilbertMeasure D)] with r hr hz
  simp only [Pi.zero_apply] at hz
  rw [hr, hz]
  split_ifs <;> rfl

theorem matchingSourceOuter_eq_zero {D : ReferenceData}
    {M : RadialMatchingData D} (hM : MatchingLocalRealizations D M)
    {F : RadialModePair D} (hF : F.1 = 0) : M.sourceOuter F = 0 := by
  apply Prod.ext
  · have hs := (hM.2.2.2.1 F).2.2.2
    rw [hF] at hs
    change (M.sourceOuter F).1 = 0
    apply Lp.ext
    filter_upwards [hs, Lp.coeFn_zero ℝ 2 (radialHilbertMeasure D)] with r hr hz
    simp only [Pi.zero_apply] at hz
    rw [hr, hz]
    split_ifs <;> rfl
  · exact (hM.2.2.2.1 F).2.1

theorem matchingInnerInverse_pure_scalar {D : ReferenceData}
    {M : RadialMatchingData D} (hM : MatchingLocalRealizations D M)
    (hj : M.frequency ≠ 2) {F : RadialModePair D} (hF : F.1 = 0) :
    M.innerInverse (M.sourceInner F) = 0 := by
  rcases hM.2.2.2.2.1 F with
    ⟨hae, _, heq, _, hreg, _, houter, _, hscalar, _, hcut, _⟩
  have hs : (M.innerInverse (M.sourceInner F)).2 = 0 := by
    simpa only [if_neg hj] using hscalar
  have hgraph : ModeInnerDirichletGraph D M
      (M.innerInverse (M.sourceInner F)) 0 := by
    refine ⟨?_, ?_, M.innerRepresentative F, hae, hreg, houter, ?_, ?_⟩
    · apply (modeLocalEquation_congr_source_fst
        (H := (0 : RadialModePair D)) (matchingSourceInner_fst_eq_zero hM hF)).mp heq
    · simp only [if_neg hj, hs, Prod.snd_zero, and_self]
    · simpa [matchingCut] using hcut 0
    · simpa only [matchingCut, show (1 : Fin 2) ≠ 0 by decide, if_false] using hcut 1
  have hu := hM.2.1 _ 0 hgraph
  rw [map_zero] at hu
  exact hu.symm

theorem matchingInnerPoisson_scalar_zero {D : ReferenceData}
    {M : RadialMatchingData D} (hM : MatchingLocalRealizations D M)
    (hj : M.frequency ≠ 2) (i : Fin 2) : (M.innerPoisson i).2 = 0 := by
  rcases hM.2.2.2.2.2 i with ⟨_, _, _, _, _, _, _, _, _, hrow, _⟩
  simpa only [if_neg hj] using hrow

theorem matchingOuterPoisson_scalar_zero {D : ReferenceData}
    {M : RadialMatchingData D} (hM : MatchingLocalRealizations D M)
    (i : Fin 2) : (M.outerPoisson i).2 = 0 := by
  exact (hM.2.2.2.2.2 i).2.2.2.2.2.2.1

theorem matchingFormulaValue_scalar_zero {D : ReferenceData}
    {M : RadialMatchingData D} (hM : MatchingLocalRealizations D M)
    (hj : M.frequency ≠ 2) (F : RadialModePair D) :
    (matchingFormulaValue D M F).2 = 0 := by
  have hinner : (M.innerInverse (M.sourceInner F)).2 = 0 := by
    rcases hM.2.2.2.2.1 F with ⟨_, _, _, _, _, _, _, _, hscalar, _⟩
    simpa only [if_neg hj] using hscalar
  have houter : (M.outerInverse (M.sourceOuter F)).2 = 0 :=
    (hM.2.2.2.2.1 F).2.2.2.2.2.2.2.2.2.1
  simp only [matchingFormulaValue, Prod.snd_add, Prod.snd_sum, Prod.smul_snd,
    hinner, houter, matchingInnerPoisson_scalar_zero hM hj,
    matchingOuterPoisson_scalar_zero hM, smul_zero, Finset.sum_const_zero, add_zero]

theorem matchingFormulaValue_pure_scalar {D : ReferenceData}
    {M : RadialMatchingData D} (hM : MatchingLocalRealizations D M)
    (hj : M.frequency ≠ 2) {F : RadialModePair D} (hF : F.1 = 0) :
    matchingFormulaValue D M F = 0 := by
  have hinv := matchingInnerInverse_pure_scalar hM hj hF
  have hout := matchingSourceOuter_eq_zero hM hF
  have hfirst := matchingSourceInner_fst_eq_zero hM hF
  have hh (i : Fin 2) : modePairing D (M.innerPoisson i) (M.sourceInner F) = 0 := by
    simp only [modePairing, hfirst, inner_zero_right,
      matchingInnerPoisson_scalar_zero hM hj, zero_mul, add_zero]
  have ho (i : Fin 2) : modePairing D (M.outerPoisson i) (M.sourceOuter F) = 0 := by
    simp only [hout, modePairing, Prod.fst_zero, Prod.snd_zero,
      inner_zero_right, mul_zero, add_zero]
  have hp0 (U : RadialModePair D) : modePairing D U 0 = 0 := by
    simp only [modePairing, Prod.fst_zero, Prod.snd_zero,
      inner_zero_right, mul_zero, add_zero]
  simp only [matchingFormulaValue, hh, ho, hp0, radialMatrixApply,
    mul_zero, Finset.sum_const_zero, add_zero, sub_zero, hinv, hout,
    map_zero, zero_smul]

end ContinuousFlexibility.Statements
