module

public import ContinuousFlexibility.Analysis.N04NegativeHeightFactorGerms
public import ContinuousFlexibility.Analysis.N04NegativeHeightAuxiliaryTransfer

/-!
# Current jets of the negative height and its reciprocal

The angular density identity reconstructs both height atoms from the
forward chart and the physical radial coefficient. The two normalized
scalar factors equal one at the reference state, so their square roots
and reciprocals have current estimates on a common state neighborhood.
The neighborhood is chosen at the zero auxiliary column and transferred
unchanged to every auxiliary column.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff

attribute [local instance]
  n07aNonlinearAnnularGroup n07aNonlinearAnnularModule
  n07aNonlinearAnnularAddGroup n07aNonlinearAnnularSMul n07aNonlinearAnnularSub
  n07aNonlinearAnnularParameterGroup n07aNonlinearAnnularParameterModule
  n07aNonlinearAnnularParameterAddGroup n07aNonlinearAnnularParameterSMul
  n07aNonlinearAnnularParameterSub
  n07aNonlinearDirectionsGroup n07aNonlinearDirectionsModule
  n07aNonlinearDirectionsAddGroup n07aNonlinearDirectionsSMul n07aNonlinearDirectionsSub
  n07aNonlinearSectorParameterGroup n07aNonlinearSectorParameterModule
  n07aNonlinearSectorParameterAddGroup n07aNonlinearSectorParameterSMul
  n07aNonlinearSectorParameterSub

namespace N04RealizationGauge

variable (G : N04RealizationGauge)
  (η : (G.W.S.height (3 / 4 : ℝ)).Space)

theorem negative_heightAtom_germs {b : ℕ} {ε : ℝ}
    (hb : G.W.base ≤ b) (he : 0 < ε) (heW : ε ≤ G.W.ε)
    (hchart : G.NegativeAtomData η atomIsNegativeChart b ε) :
    G.HeightGerm η b ε (G.atomFamily η .height) (G.atomRef η .height) ∧
      G.HeightGerm η b ε (G.atomFamily η .heightInverse) (G.atomRef η .heightInverse) := by
  have hD := G.W.radial.1
  have hT : IsMaterialData G.W.D G.W.U := isMaterialData_enlargedMaterialData hD G.W.hT
  have hI : HasInterpolation (parameterGrading (G.S η)) :=
    n04NegativeHeight_parameterInterpolation (S := G.W.S) G.W.hS
  have hE := (G.cost_nonneg η).2.2
  have hH := (G.cost_nonneg η).2.1
  have hFactors := G.negative_heightFactor_germs η hb he heW hchart
  have hN := hFactors.1
  have hA := hFactors.2
  have hNs := hN.sqrtFactor hD hT hI hE (G.negativeHeightAngularRef_one η) false
  have hNi := hN.sqrtFactor hD hT hI hE (G.negativeHeightAngularRef_one η) true
  have hAs := hA.sqrtFactor hD hT hI hE (G.negativeHeightNormalizedRadialRef_one η) false
  have hAi := hA.sqrtFactor hD hT hI hE (G.negativeHeightNormalizedRadialRef_one η) true
  have hRef : G.HeightGerm η b ε (fun _ => G.atomRef η .height)
      (G.atomRef η .height) :=
    N04HeightCurrentGerm.fixed he (G.negative_height_referenceData η .height trivial) hE hH
  have hRefInv : G.HeightGerm η b ε (fun _ => G.atomRef η .heightInverse)
      (G.atomRef η .heightInverse) :=
    N04HeightCurrentGerm.fixed he
      (G.negative_height_referenceData η .heightInverse trivial) hE hH
  have hHeight := (hRef.mul hNs hD hT hI hE).mul hAi hD hT hI hE
  have hInverse := (hRefInv.mul hNi hD hT hI hE).mul hAs hD hT hI hE
  constructor
  · apply hHeight.congr
    · intro z hz m hm q hq
      simpa only [n04NegativeHeightSqrtFactor, Bool.false_eq_true, if_false, if_true]
        using (G.negativeHeight_normalized_formula η z
          (sectorNeighborhood_mono (G.S η) hb heW heW hz) m hm q hq).1.symm
    · intro m hm q hq
      simp only [mul_one]
  · apply hInverse.congr
    · intro z hz m hm q hq
      simpa only [n04NegativeHeightSqrtFactor, Bool.false_eq_true, if_false, if_true]
        using (G.negativeHeight_normalized_formula η z
          (sectorNeighborhood_mono (G.S η) hb heW heW hz) m hm q hq).2.symm
    · intro m hm q hq
      simp only [mul_one]

end N04RealizationGauge

/-- The literal negative-height obligation, including one neighborhood
valid for every auxiliary column and all parameter and spatial orders. -/
theorem n04Realization_negativeHeight : N04RealizationNegativeHeightObligation := by
  intro G b ε hadm hchart
  have hg := G.negative_heightAtom_germs 0 hadm.1 hadm.2.1 hadm.2.2.1 (hchart 0)
  have hc := hg.1.common hg.2 (G.cost_nonneg 0).2.2 (G.cost_nonneg 0).2.1
  let b' : ℕ := hc.choose
  let ε' : ℝ := hc.choose_spec.choose
  have hd := hc.choose_spec.choose_spec
  have hzero : G.NegativeAtomData 0 atomIsNegativeHeight b' ε' := by
    intro a ha
    cases a <;> first | exact ha.elim | exact hd.2.2.2.1 | exact hd.2.2.2.2
  exact ⟨b', ε', hd.1, hd.2.1, hd.2.2.1,
    fun η => G.negativeHeightAtomData_auxiliary 0 η b' ε' hzero⟩

end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.n04Realization_negativeHeight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.n04Realization_negativeHeight
