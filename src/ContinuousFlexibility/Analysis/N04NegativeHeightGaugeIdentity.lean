module

public import ContinuousFlexibility.Analysis.N04NegativeHeightUnitIdentity
public import ContinuousFlexibility.Analysis.N04NegativeHeightRadialFamilies

/-!
# The literal negative height atoms as regularized scalar formulas

All inputs are fields already belonging to the same gauge.  The formula
is evaluated on the fixed reference half and holds before selecting the
auxiliary column.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis.N04RealizationGauge

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff

variable (G : N04RealizationGauge)

theorem negativeHeight_sqrt_formula
    (η : (G.W.S.height (3 / 4 : ℝ)).Space) (z : Parameter (G.S η))
    (hz : z ∈ sectorNeighborhood (G.S η) G.W.base G.W.ε G.W.ε)
    (m : ℕ) (hm : G.Neg η m) (q : PolarPoint) (hq : q ∈ unitStrip) :
    0 < G.negativeHeightAngularFamily η z m q ∧
      G.atomFamily η .height z m q = Real.sqrt
        (G.negativeHeightAngularFamily η z m q /
          (G.physicalRadialFamily η z m q * G.atomFamily η .jacobian z m q)) ∧
      G.atomFamily η .heightInverse z m q = Real.sqrt
        ((G.physicalRadialFamily η z m q * G.atomFamily η .jacobian z m q) /
          G.negativeHeightAngularFamily η z m q) := by
  obtain ⟨j, hi⟩ := (G.neg_iff_inl η m).mp hm
  let K := G.W.A G.X.e₀
  let k := G.negativeIndex j
  have hk : G.X.e₀ k = .inl (j.1, j.2) := G.X.e₀.apply_symm_apply _
  have hz' := liftSectorParameter_mem_stateNeighborhood (C := G.W.C) hz le_rfl
  have hs := G.W.through03.1.1.2.2.1.liftSectorParameter_sector z
  have hA := n04b_actualTypedAtlas_partA
    G.W.hT G.W.hS G.W.through03 G.W.field G.X.e₀
  have hp : physicalUnitPoint K k q ∈ referencePhysicalPieceOpen G.W.S K k :=
    (n04NegativeGeometry_affine_unitPoint (K.physicalLeft k) (K.physicalRight k)
      (hA.referenceBounds k).1).2.1 hq
  have hpcomp := n04NegativeGeometry_referenceHalf_subset_component
    G.W.hT G.W.hS G.W.through03 G.W.field G.X.e₀ k j.1 j.2 hk hp
  have hfields := n04NegativeGeometry_referenceHalf_fields
    G.W.hT G.W.hS G.W.through03 G.W.field G.X.e₀ k j.1 j.2 hk hz' hs
  have hF : DifferentiableAt ℝ (K.chart (G.lift η z) k) (physicalUnitPoint K k q) :=
    ((hfields.1 _ hp).contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds hp)).differentiableAt
      (by simp)
  have hnormalized := n04NegativeHeight_angularFactor_eq_unitAtoms
    (D := G.W.D) (T := G.W.U) (C := G.W.C) (L := G.W.L)
    K (G.lift η z) k q (sub_pos.mpr (hA.referenceBounds k).2.1).ne' hF
  have hnegative := G.negative_fields η (G.lift η z) m j hi
  have hpoint : physicalUnitPoint (G.V η) m q = physicalUnitPoint K k q := by
    simp only [physicalUnitPoint, hnegative.2.2.1, hnegative.2.2.2.1]
    rfl
  have hnumerator : G.negativeHeightAngularFamily η z m q =
      n04NegativeHeightAngularFactor (K.chart (G.lift η z) k) (physicalUnitPoint K k q) := by
    unfold negativeHeightAngularFamily
    rw [G.negative_atomFamily η z m j hi .chartRadial (by decide),
      G.negative_atomFamily η z m j hi .chartAngleDefect (by decide),
      hnegative.1, hnegative.2.1]
    exact hnormalized.symm
  have hradial : G.physicalRadialFamily η z m q =
      (G.W.L.coefficients (G.lift η z)).a (physicalUnitPoint K k q) := by
    change (G.W.L.coefficients (G.lift η z)).a (physicalUnitPoint (G.V η) m q) = _
    rw [hpoint]
  have hraw := n04NegativeHeight_actualAtlas_sqrt_eq
    G.W.hT G.W.hS G.W.through03 G.W.field G.X.e₀ hz' hs k j.1 j.2 hk hpcomp
  refine ⟨by rw [hnumerator]; exact hraw.1, ?_, ?_⟩
  · rw [hnumerator, hradial,
      G.negative_atomFamily η z m j hi .height (by decide),
      G.negative_atomFamily η z m j hi .jacobian (by decide)]
    exact hraw.2.1
  · rw [hnumerator, hradial,
      G.negative_atomFamily η z m j hi .heightInverse (by decide),
      G.negative_atomFamily η z m j hi .jacobian (by decide)]
    exact hraw.2.2

end ContinuousFlexibility.Analysis.N04RealizationGauge

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationGauge.negativeHeight_sqrt_formula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationGauge.negativeHeight_sqrt_formula
