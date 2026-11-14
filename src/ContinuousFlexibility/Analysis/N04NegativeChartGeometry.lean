module

public import ContinuousFlexibility.Analysis.N04NegativeChartJacobianIdentities
public import ContinuousFlexibility.Analysis.N04NegativeChartWidths

/-!
# The actual forward determinant on the fixed reference half

The retained negative chart is smooth and nondegenerate on its entire
original component. Consequently its fixed physical unit map is valid
even when the current cut has moved. This identifies the determinant
polynomial and its absolute value with the stored Jacobian atom.
-/

@[expose] public section

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

variable (G : N04RealizationGauge) (η : (G.W.S.height (3 / 4 : ℝ)).Space)

theorem negativeChart_forward_fields
    (z : Parameter G.W.S)
    (hz : z ∈ sectorNeighborhood G.W.S G.W.base G.W.ε G.W.ε)
    (m : ℕ) (hm : G.Neg η m) :
    (G.V η).physicalLeft m < (G.V η).physicalRight m ∧
      (G.V η).left m < (G.V η).right m ∧
      ContDiffOn ℝ ∞ ((G.V η).chart (G.lift η z) m)
        (referencePhysicalPieceOpen (G.S η) (G.V η) m) ∧
      ∀ q ∈ referencePhysicalPieceOpen (G.S η) (G.V η) m,
        planeJacobian ((G.V η).chart (G.lift η z) m) q ≠ 0 := by
  obtain ⟨j, hi⟩ := (G.neg_iff_inl η m).mp hm
  let k := G.negativeIndex j
  let K := G.W.A G.X.e₀
  have hk : G.X.e₀ k = .inl (j.1, j.2) := G.X.e₀.apply_symm_apply _
  have hz' : liftSectorParameter G.W.S G.W.C z ∈
      stateNeighborhood G.W.S G.W.C G.W.base G.W.ε :=
    liftSectorParameter_mem_stateNeighborhood hz le_rfl
  have hs := G.W.through03.1.1.2.2.1.liftSectorParameter_sector z
  have hr := n04NegativeGeometry_referenceHalf_fields
    G.W.hT G.W.hS G.W.through03 G.W.field G.X.e₀ k j.1 j.2 hk hz' hs
  have hA := n04b_actualTypedAtlas_partA
    G.W.hT G.W.hS G.W.through03 G.W.field G.X.e₀
  have hf := G.negative_fields η (liftSectorParameter G.W.S G.W.C z) m j hi
  have hdomain : referencePhysicalPieceOpen (G.S η) (G.V η) m =
      referencePhysicalPieceOpen G.W.S K k := by
    exact congrArg₂ (fun l r : ℝ => Ioo l r ×ˢ (univ : Set ℝ))
      hf.2.2.1 hf.2.2.2.1
  have hchart : (G.V η).chart (G.lift η z) m =
      K.chart (liftSectorParameter G.W.S G.W.C z) k := hf.2.2.2.2.2.2.2.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hf.2.2.1, hf.2.2.2.1]
    exact (hA.referenceBounds k).1
  · rw [hf.1, hf.2.1]
    exact (hA.referenceBounds k).2.1
  · simpa only [hchart, hdomain] using hr.1
  · intro q hq
    rw [hchart]
    exact (hr.2.2.1 q (hdomain ▸ hq)).1

def negativeChartDeterminant : Parameter G.W.S → ℕ → PolarPoint → ℝ :=
  fun z => n04NegativeChartDeterminant (G.negativeChartWidthRatio η)
    (G.atomFamily η .chartRadial z) (G.atomFamily η .chartAngleDefect z)

def negativeChartDeterminantRef : ℕ → PolarPoint → ℝ :=
  n04NegativeChartDeterminant (G.negativeChartWidthRatio η)
    (G.atomRef η .chartRadial) (G.atomRef η .chartAngleDefect)

theorem negativeChartDeterminant_zero :
    G.negativeChartDeterminant η 0 = G.negativeChartDeterminantRef η :=
  congrArg₂ (n04NegativeChartDeterminant (G.negativeChartWidthRatio η))
    (G.atomFamily_zero η .chartRadial) (G.atomFamily_zero η .chartAngleDefect)

theorem negativeChartDeterminant_eq
    (z : Parameter G.W.S)
    (hz : z ∈ sectorNeighborhood G.W.S G.W.base G.W.ε G.W.ε)
    (m : ℕ) (hm : G.Neg η m) {q : PolarPoint} (hq : q ∈ unitStrip) :
    G.negativeChartDeterminant η z m q =
      planeJacobian ((G.V η).chart (G.lift η z) m)
        (physicalUnitPoint (G.V η) m q) := by
  have hF := G.negativeChart_forward_fields η z hz m hm
  have hmap : physicalUnitPoint (G.V η) m q ∈
      referencePhysicalPieceOpen (G.S η) (G.V η) m :=
    (n04NegativeGeometry_affine_unitPoint _ _ hF.1).2.1 hq
  have hd := (hF.2.2.1.contDiffAt
    ((isOpen_Ioo.prod isOpen_univ).mem_nhds hmap)).differentiableAt (by simp)
  exact (n04NegativeChart_jacobian_unit_mixed (G.lift η z) m
    (sub_pos.mpr hF.1).ne' (sub_pos.mpr hF.2.1).ne'
    (G.negative_geometry_spatial η z hz m hm .chartRadial trivial).1
    (G.negative_geometry_spatial η z hz m hm .chartAngleDefect trivial).1 hq hd).symm

theorem negativeChartDeterminant_ne_zero
    (z : Parameter G.W.S)
    (hz : z ∈ sectorNeighborhood G.W.S G.W.base G.W.ε G.W.ε)
    (m : ℕ) (hm : G.Neg η m) {q : PolarPoint} (hq : q ∈ unitStrip) :
    G.negativeChartDeterminant η z m q ≠ 0 := by
  have hF := G.negativeChart_forward_fields η z hz m hm
  rw [G.negativeChartDeterminant_eq η z hz m hm hq]
  exact hF.2.2.2 _ ((n04NegativeGeometry_affine_unitPoint _ _ hF.1).2.1 hq)

theorem negativeChart_jacobian_eq_abs
    (z : Parameter G.W.S)
    (hz : z ∈ sectorNeighborhood G.W.S G.W.base G.W.ε G.W.ε)
    (m : ℕ) (hm : G.Neg η m) {q : PolarPoint} (hq : q ∈ unitStrip) :
    G.atomFamily η .jacobian z m q = |G.negativeChartDeterminant η z m q| :=
  congrArg abs (G.negativeChartDeterminant_eq η z hz m hm hq).symm

theorem negativeChart_jacobian_pos
    (z : Parameter G.W.S)
    (hz : z ∈ sectorNeighborhood G.W.S G.W.base G.W.ε G.W.ε)
    (m : ℕ) (hm : G.Neg η m) {q : PolarPoint} (hq : q ∈ unitStrip) :
    0 < G.atomFamily η .jacobian z m q := by
  rw [G.negativeChart_jacobian_eq_abs η z hz m hm hq]
  exact abs_pos.mpr (G.negativeChartDeterminant_ne_zero η z hz m hm hq)

end ContinuousFlexibility.Analysis.N04RealizationGauge

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationGauge.negativeChart_jacobian_eq_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationGauge.negativeChart_jacobian_eq_abs
