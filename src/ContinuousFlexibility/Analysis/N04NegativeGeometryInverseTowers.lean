import ContinuousFlexibility.Analysis.N04NegativeGeometryPlanarInverseDirections
import ContinuousFlexibility.Analysis.N04NegativeGeometryActualInverse
import ContinuousFlexibility.Analysis.N04NegativeGeometryJacobianTowers
import ContinuousFlexibility.Analysis.N01cPhysicalFlowGraph
import ContinuousFlexibility.Analysis.N01SelectorInverse

/-!
# The actual negative inverse and pulled height have joint towers

The full-component forward chart, its nonzero Jacobian, and the actual
inverse continuity and identities supply the parameterized inverse
theorem. Composing its graph with the same actual physical height gives
the pulled height. Both constructions use the original sector
neighborhood and the entire open canonical root strip.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis.N04RealizationStart

open Set ContinuousFlexibility.Statements

variable (W : N04RealizationStart)

/-- One genuine joint tower for the stored negative inverse, with no
regularity assumption on that inverse supplied as an obligation. -/
def negativeInverseJointTower (m : ℕ) (side : Bool) :
    SmoothDirections
      (sectorNeighborhood W.S W.base W.ε W.ε ×ˢ
        (Ioo (0 : ℝ) (n04bRootCutRadius (W.C.travel m)) ×ˢ univ))
      (fun x : (StateDirections W.S × ℝ) × PolarPoint =>
        n04bActualNegativeInverse W.hT W.hS W.through03 W.field
          (liftSectorParameter W.S W.C x.1) m side x.2) :=
  n04NegativeGeometry_parameterized_planar_inverse_jointTower
    (W.negativeChartJointTower m side)
    (sectorNeighborhood_isOpen W.S W.base W.ε W.ε)
    (isOpen_Ioo.prod isOpen_univ) (isOpen_Ioo.prod isOpen_univ)
    (fun x hx => W.negativeJacobian_ne_zero m side hx.1 hx.2)
    (fun z hz => W.negativeChart_injOn m side hz)
    (fun x hx => (W.negativeInverse_maps_right m side hx.1).1 hx.2)
    (fun x hx => (W.negativeInverse_maps_right m side hx.1).2 hx.2)
    (W.negativeInverse_continuousOn m side)

/-- The literal height evaluated at the literal inverse point is smooth
jointly in the original state and canonical target point. -/
def negativePulledHeightRootJointTower (m : ℕ) (side : Bool) :
    SmoothDirections
      (sectorNeighborhood W.S W.base W.ε W.ε ×ˢ
        (Ioo (0 : ℝ) (n04bRootCutRadius (W.C.travel m)) ×ˢ univ))
      (fun x : (StateDirections W.S × ℝ) × PolarPoint =>
        n04bActualNegativeHeight W.hT W.hS W.through03 W.field
          (liftSectorParameter W.S W.C x.1) m side
          (n04bActualNegativeInverse W.hT W.hS W.through03 W.field
            (liftSectorParameter W.S W.C x.1) m side x.2)) := by
  letI : LocallyConvexSpace ℝ (StateDirections W.S × ℝ) :=
    (sectorPairGrading_withSeminorms W.S).toLocallyConvexSpace
  have hO : IsOpen
      (sectorNeighborhood W.S W.base W.ε W.ε ×ˢ
        (Ioo (0 : ℝ) (n04bRootCutRadius (W.C.travel m)) ×ˢ (univ : Set ℝ))) :=
    (sectorNeighborhood_isOpen W.S W.base W.ε W.ε).prod
      (isOpen_Ioo.prod isOpen_univ)
  let Jp := smoothDirectionsLinearOn
    (ContinuousLinearMap.fst ℝ (StateDirections W.S × ℝ) PolarPoint) hO
  let J := smoothDirectionsProd Jp (W.negativeInverseJointTower m side)
  exact smoothDirections_realCompTVS J (W.negativeHeightJointTower m side)
    (fun x hx => ⟨hx.1, (W.negativeInverse_maps_right m side hx.1).1 hx.2⟩)

end ContinuousFlexibility.Analysis.N04RealizationStart

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationStart.negativeInverseJointTower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationStart.negativeInverseJointTower

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationStart.negativePulledHeightRootJointTower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationStart.negativePulledHeightRootJointTower
