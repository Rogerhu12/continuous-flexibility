module

public import ContinuousFlexibility.Analysis.N04NegativeChartPhysicalBounds
public import ContinuousFlexibility.Analysis.N04NegativeChartCoordinateClosure

/-!
# Assembly of negative chart data from the actual physical estimates

The typed negative atlas is retained pointwise by the whole atlas and
the auxiliary-column replacement. Its exact material sample is retained
as well. Thus one physical estimate supplies all four chart atoms on
one neighborhood, before any auxiliary source column is selected.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis.N04RealizationGauge

open Set ContinuousFlexibility.Statements CanonicalGeometry

set_option backward.isDefEq.respectTransparency true

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

set_option diagnostics true in
private theorem coordinateData_of_physical_bounds
    (η₀ : (G.W.S.height (3 / 4 : ℝ)).Space) (radial : Bool) {b : ℕ} {ε : ℝ}
    (hb : G.W.base ≤ b) (hεpos : 0 < ε) (hε : ε ≤ G.W.ε) (hεhalf : ε ≤ 1 / 2)
    (hphysical : N04NegativeChartPhysicalPositiveBounds G.W G.X.e₀ b ε) :
    G.Data η₀ (G.Neg η₀) b ε
      (G.atomFamily η₀ (if radial then .chartRadial else .chartAngleDefect))
      (G.atomRef η₀ (if radial then .chartRadial else .chartAngleDefect)) := by
  have hnormalized := G.W.negativeChart_normalized_positive_bounds G.X.e₀ hb hε hphysical
  have ha : atomIsNegativeChart (if radial then .chartRadial else .chartAngleDefect) := by
    cases radial <;> trivial
  have haux : (if radial then Atom.chartRadial else .chartAngleDefect) ≠ .auxiliaryColumn := by
    cases radial <;> decide
  apply G.negativeChart_atomData_of_positive_bounds η₀ b ε hb hεpos hε hεhalf _ ha
  intro n hn
  have hnBounds := hnormalized n hn
  let loss := hnBounds.choose
  refine ⟨loss, fun s => ?_⟩
  have hs := hnBounds.choose_spec s
  let B := hs.choose
  have hB : 0 < B := hs.choose_spec.1
  have hbound := hs.choose_spec.2
  refine ⟨B, hB, fun m hm q hq i j hij J z hz v => ?_⟩
  have hindex := (G.neg_iff_inl η₀ m).mp hm
  let idx := hindex.choose
  have hidx := hindex.choose_spec
  let k := G.negativeIndex idx
  let K := G.W.A G.X.e₀
  let J' : SmoothDirections (sectorNeighborhood G.W.S b ε ε)
      (fun x => mixedDerivative i j
        (atom G.W.D G.W.U G.W.S G.W.C G.W.L K
          (liftSectorParameter G.W.S G.W.C x) k
          (if radial then .chartRadial else .chartAngleDefect)) q) :=
    J.congrOn (fun x _ => congrArg
      (fun f : PolarPoint → ℝ => mixedDerivative i j f q)
      (G.negative_atomFamily η₀ x m idx hidx _ haux))
  have hraw := hbound idx.1 idx.2 radial q hq i j hij J' z hz v
  have hf := G.negative_fields η₀ (G.W.C.referenceState, 0) m idx hidx
  have hcell : (G.V η₀).cell m = K.cell k := hf.2.2.2.2.2.1
  have hE : 0 ≤ G.W.T.E0 (G.W.T.sample (K.cell k)) :=
    zero_le_one.trans (G.W.floor _)
  have hH : 0 ≤ G.W.T.H (G.W.T.sample (K.cell k)) ^ (3 / 4 : ℝ) :=
    Real.rpow_nonneg (G.W.hT.2.1 _
      (materialSample_mem_interval G.W.radial.1 G.W.hT (K.cell k))).2.1.le _
  have hV := oneHighVariationWeight_nonneg (parameterGrading G.W.S) b (s + loss) z v
  have hcost : B * G.W.T.E0 (G.W.T.sample (K.cell k)) ^ B ≤
      B * G.W.U.E0 (G.W.U.sample (K.cell k)) ^ B :=
    mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hE (le_enlargedMaterialData_E0 G.W.T _) hB.le) hB.le
  let cost (l : ℕ) : ℝ := B * G.W.U.E0 (G.W.U.sample l) ^ B *
    G.W.U.H (G.W.U.sample l) ^ (3 / 4 : ℝ) *
      oneHighVariationWeight (parameterGrading G.W.S) b (s + loss) z v
  have hlarge : |J.D n z v| ≤ cost (K.cell k) := hraw.trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcost hH) hV)
  exact hlarge.trans_eq (congrArg cost hcell.symm)

set_option diagnostics true in
theorem negativeChart_data_of_physical_bounds {b : ℕ} {ε : ℝ}
    (hb : G.W.base ≤ b) (hεpos : 0 < ε) (hε : ε ≤ G.W.ε) (hεhalf : ε ≤ 1 / 2)
    (hphysical : N04NegativeChartPhysicalPositiveBounds G.W G.X.e₀ b ε) :
    ∃ b' : ℕ, ∃ ε' : ℝ, b ≤ b' ∧ 0 < ε' ∧ ε' ≤ ε ∧
      ∀ η, G.NegativeAtomData η atomIsNegativeChart b' ε' := by
  let η₀ : (G.W.S.height (3 / 4 : ℝ)).Space := 0
  have hcoord (radial : Bool) := coordinateData_of_physical_bounds G η₀ radial
    hb hεpos hε hεhalf hphysical
  have hchart :=
    G.negativeChart_data_of_coordinates η₀ hb hεpos hε (hcoord true) (hcoord false)
  let b' := hchart.choose
  let ε' := hchart.choose_spec.choose
  have hs := hchart.choose_spec.choose_spec
  exact ⟨b', ε', hs.1, hs.2.1, hs.2.2.1,
    fun η => G.negativeChartData_auxiliary η₀ η b' ε' hs.2.2.2⟩

end ContinuousFlexibility.Analysis.N04RealizationGauge

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationGauge.negativeChart_data_of_physical_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationGauge.negativeChart_data_of_physical_bounds
