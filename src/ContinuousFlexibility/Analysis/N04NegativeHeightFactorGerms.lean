import ContinuousFlexibility.Analysis.N04NegativeHeightSqrtGerms
import ContinuousFlexibility.Analysis.N04NegativeHeightNormalizedIdentity
import ContinuousFlexibility.Analysis.N04NegativeHeightReferenceLengths
import ContinuousFlexibility.Analysis.N04NegativeHeightRadialBounds
import ContinuousFlexibility.Analysis.N04RealizationLeadNegativeSplit

/-!
# Current germs of the two normalized negative height factors

Only the forward chart atoms and the already proved physical radial
coefficient enter. The reference height is a fixed spatial multiplier;
no current height estimate is an input.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis.N04RealizationGauge

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

variable (G : N04RealizationGauge)
  (η : (G.W.S.height (3 / 4 : ℝ)).Space)

abbrev HeightGerm (b : ℕ) (ε : ℝ)
    (f : Parameter (G.S η) → ℕ → PolarPoint → ℝ) (f₀ : ℕ → PolarPoint → ℝ) : Prop :=
  N04HeightCurrentGerm (G.S η) G.W.U (G.V η).cell (G.Neg η) b ε f f₀

theorem negative_physicalRadial_germ {b : ℕ} {ε : ℝ}
    (hb : G.W.base ≤ b) (he : 0 < ε) (heW : ε ≤ G.W.ε) :
    G.HeightGerm η b ε (G.physicalRadialFamily η) (G.physicalRadialRef η) := by
  refine ⟨G.negative_physicalRadial_referenceData η,
    fun m _ q _ => congrFun (G.physicalRadialFamily_zero η m) q,
    b, min ε (1 / 2), le_rfl, lt_min he (by norm_num), min_le_left _ _, ?_⟩
  exact (G.negative_physicalRadial_currentData η).mono (fun _ hm => hm) hb
    (min_le_min heW le_rfl) (G.cost_nonneg η).1 (G.cost_nonneg η).2.1

theorem negative_chartAtom_germ {b : ℕ} {ε : ℝ} (he : 0 < ε)
    (hchart : G.NegativeAtomData η atomIsNegativeChart b ε)
    (a : Atom) (ha : atomIsNegativeChart a) :
    G.HeightGerm η b ε (G.atomFamily η a) (G.atomRef η a) := by
  have hgeo : atomIsGeometry a := by
    cases a <;> first | exact trivial | exact ha.elim
  exact N04HeightCurrentGerm.of_data he (hchart a ha)
    (G.negative_height_referenceData η a hgeo)
    (fun m _ q _ => congrFun (congrFun (G.height_atomFamily_zero η a) m) q)

theorem negative_heightFactor_germs {b : ℕ} {ε : ℝ}
    (hb : G.W.base ≤ b) (he : 0 < ε) (heW : ε ≤ G.W.ε)
    (hchart : G.NegativeAtomData η atomIsNegativeChart b ε) :
    G.HeightGerm η b ε (G.negativeHeightAngularFamily η) (G.negativeHeightAngularRef η) ∧
      G.HeightGerm η b ε (G.negativeHeightNormalizedRadialFamily η)
        (G.negativeHeightNormalizedRadialRef η) := by
  have hD := G.W.radial.1
  have hT : IsMaterialData G.W.D G.W.U := isMaterialData_enlargedMaterialData hD G.W.hT
  have hI : HasInterpolation (parameterGrading (G.S η)) :=
    n04NegativeHeight_parameterInterpolation (S := G.W.S) G.W.hS
  have hE := (G.cost_nonneg η).2.2
  have hH := (G.cost_nonneg η).2.1
  have hR := G.negative_chartAtom_germ η he hchart .chartRadial trivial
  have hAngle := G.negative_chartAtom_germ η he hchart .chartAngleDefect trivial
  have hJ := G.negative_chartAtom_germ η he hchart .jacobian trivial
  have hOne : G.HeightGerm η b ε (fun _ _ _ => (1 : ℝ)) (fun _ _ => 1) :=
    N04HeightCurrentGerm.const 1 he hE hH
  have hNegOne : G.HeightGerm η b ε (fun _ _ _ => (-1 : ℝ)) (fun _ _ => -1) :=
    N04HeightCurrentGerm.const (-1) he hE hH
  have hLength : G.HeightGerm η b ε
      (fun _ m _ => (G.V η).right m - (G.V η).left m)
      (fun m _ => (G.V η).right m - (G.V η).left m) :=
    N04HeightCurrentGerm.fixed he (G.negative_canonicalLength_referenceData η) hE hH
  have hPhi := hOne.add hAngle.angularPartial hE hH
  have hPhiSq := hPhi.mul hPhi hD hT hI hE
  have hXi := hLength.mul hR hD hT hI hE
  have hXiTheta := hLength.mul hR.angularPartial hD hT hI hE
  have hXiThetaSq := hXiTheta.mul hXiTheta hD hT hI hE
  have hTerm := hXi.mul hXiThetaSq hD hT hI hE
  have hNegativeTerm := hNegOne.mul hTerm hD hT hI hE
  have hN := hPhiSq.add hNegativeTerm hE hH
  have hAngular : G.HeightGerm η b ε
      (G.negativeHeightAngularFamily η) (G.negativeHeightAngularRef η) := by
    apply hN.congr
    · intro z hz m hm q hq
      simp only [negativeHeightAngularFamily, n04NegativeHeightUnitNumerator,
        G.negative_canonicalLeft_zero η m hm, zero_add, pow_two]
      ring
    · intro m hm q hq
      simp only [negativeHeightAngularRef, n04NegativeHeightUnitNumerator,
        G.negative_canonicalLeft_zero η m hm, zero_add, pow_two]
      ring
  have hFixedHeight : G.HeightGerm η b ε (fun _ => G.atomRef η .height)
      (G.atomRef η .height) :=
    N04HeightCurrentGerm.fixed he (G.negative_height_referenceData η .height trivial) hE hH
  have hFixedSquare := hFixedHeight.mul hFixedHeight hD hT hI hE
  have ha := G.negative_physicalRadial_germ η hb he heW
  have hAJ := ha.mul hJ hD hT hI hE
  have hA := hAJ.mul hFixedSquare hD hT hI hE
  refine ⟨hAngular, hA.congr ?_ ?_⟩
  · intro z hz m hm q hq
    simp only [negativeHeightNormalizedRadialFamily, pow_two]
  · intro m hm q hq
    simp only [negativeHeightNormalizedRadialRef, pow_two]

end ContinuousFlexibility.Analysis.N04RealizationGauge
