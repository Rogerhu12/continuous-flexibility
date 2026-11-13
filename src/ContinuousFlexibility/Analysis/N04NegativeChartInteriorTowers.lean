import ContinuousFlexibility.Analysis.N04NegativeGeometryCoefficientTowers
import ContinuousFlexibility.Analysis.N01ReturnTransportSpatialTowers
import ContinuousFlexibility.Analysis.N04bReferenceActualTravel

/-!
# The three actual fields in the interior transport system

All towers use the original full physical component. The slope and
pulled residual are the retained correction fields. The centered first
integral subtracts its genuine reference value, which is exactly the
reference optical translation plus the angle.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

private def jointTower_referenceDifference
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    {U : Set E} {V : Set PolarPoint} {f : E × PolarPoint → ℝ}
    (J : SmoothDirections (U ×ˢ V) f) (hzero : (0 : E) ∈ U) :
    SmoothDirections (U ×ˢ V) (fun x => f x - f (0, x.2)) := by
  let P : (E × PolarPoint) →L[ℝ] E × PolarPoint :=
    (0 : (E × PolarPoint) →L[ℝ] E).prod (ContinuousLinearMap.snd ℝ E PolarPoint)
  let K : SmoothDirections (U ×ˢ V) (fun x => f (0, x.2)) :=
    (J.compLinear P J.open_domain (fun x hx => ⟨hzero, hx.2⟩)).congrOn
      (fun _ _ => by simp only [P, ContinuousLinearMap.prod_apply,
        ContinuousLinearMap.zero_apply, ContinuousLinearMap.coe_snd'])
  let L : PolarPoint →L[ℝ] ℝ :=
    ContinuousLinearMap.fst ℝ ℝ ℝ - ContinuousLinearMap.snd ℝ ℝ ℝ
  exact (solveSmoothDirectionsPostcomp (smoothDirectionsProd J K) L).congrOn
    (fun _ _ => by simp only [L, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd'])

namespace N04RealizationStart

variable (W : N04RealizationStart)

def negativeInverseSlopeJointTower (m : ℕ) :
    SmoothDirections
      (sectorNeighborhood W.S W.base W.ε W.ε ×ˢ
        (Ioo (W.C.left m) (W.C.right m) ×ˢ univ))
      (fun x : (StateDirections W.S × ℝ) × PolarPoint =>
        returnFlowInverseSlope W.S W.C (liftSectorParameter W.S W.C x.1) m x.2) := by
  apply n04NegativeGeometry_glueComponentTowers
    (sectorNeighborhood_isOpen W.S W.base W.ε W.ε)
  intro l h hl hh
  exact W.through03.1.1.returnFlowInverseSlope_parameterSpatialTower W.hS W.hT m l h hl hh
    (fun z hz p hp => W.negativeOriginalDiscriminant_pos m hz
      ⟨hl.trans hp.1, hp.2.trans hh⟩)

def negativePulledCorrectionJointTower (m : ℕ) :
    SmoothDirections
      (sectorNeighborhood W.S W.base W.ε W.ε ×ˢ
        (Ioo (W.C.left m) (W.C.right m) ×ˢ univ))
      (fun x : (StateDirections W.S × ℝ) × PolarPoint =>
        returnCorrectionPulledDisplacementLinear W.S W.C W.cutoff.cutoff
          (liftSectorParameter W.S W.C x.1) m x.2
            (W.R.residual (liftSectorParameter W.S W.C x.1))) := by
  apply n04NegativeGeometry_glueComponentTowers
    (sectorNeighborhood_isOpen W.S W.base W.ε W.ε)
  intro l h hl hh
  exact W.through03.1.1.returnCorrectionPulledResidual_parameterSpatialTower
    W.hS W.hT m l h hl hh
    (fun z hz p hp => W.negativeOriginalDiscriminant_pos m hz
      ⟨hl.trans hp.1, hp.2.trans hh⟩)
    W.cutoff.cutoff W.cutoff.cutoff_smooth W.cutoff.range_on_component W.through03.1.2

def negativeMinusFirstIntegral (z : StateDirections W.S × ℝ) (m : ℕ)
    (p : PolarPoint) : ℝ :=
  n04bMinusFirstIntegral
    (fun q => W.L.minusFlow (liftSectorParameter W.S W.C z) m q.1 q.2)
    (stateLeftChart W.S (liftSectorParameter W.S W.C z).1 m) p

def negativeMinusFirstIntegralJointTower (m : ℕ) :
    SmoothDirections
      (sectorNeighborhood W.S W.base W.ε W.ε ×ˢ
        (Ioo (W.C.left m) (W.C.right m) ×ˢ univ))
      (fun x : (StateDirections W.S × ℝ) × PolarPoint =>
        W.negativeMinusFirstIntegral x.1 m x.2) := by
  apply n04NegativeGeometry_glueComponentTowers
    (sectorNeighborhood_isOpen W.S W.base W.ε W.ε)
  intro l h hl hh
  exact W.through03.1.1.n04NegativeGeometryActualMinusFirstIntegral_stripJointTower
    W.hS W.hT W.field W.cutoff.cutoff W.cutoff.cutoff_smooth
    W.cutoff.range_on_component W.coefficients_eq W.minusFlow_eq
    W.cutoff.discriminant_on_support m l h hl hh

def negativeFirstIntegralDefect (z : StateDirections W.S × ℝ) (m : ℕ)
    (p : PolarPoint) : ℝ :=
  W.negativeMinusFirstIntegral z m p - (p.2 + opticalTravel W.D.w (W.C.left m) p.1)

theorem negativeFirstIntegral_reference (m : ℕ) {p : PolarPoint}
    (hp : p.1 ∈ Icc (W.C.left m) (W.C.right m)) :
    W.negativeMinusFirstIntegral 0 m p = p.2 + opticalTravel W.D.w (W.C.left m) p.1 := by
  have hz : liftSectorParameter W.S W.C (0 : StateDirections W.S × ℝ) =
      (W.C.referenceState, (0 : ℝ)) := by
    rw [liftSectorParameter_eq_affine, map_zero, add_zero]
  simpa only [negativeMinusFirstIntegral, hz] using
    (n04b_reference_firstIntegrals W.through03.1.1.2.2.1 W.field m hp p.2).1

def negativeFirstIntegralDefectJointTower (m : ℕ) :
    SmoothDirections
      (sectorNeighborhood W.S W.base W.ε W.ε ×ˢ
        (Ioo (W.C.left m) (W.C.right m) ×ˢ univ))
      (fun x : (StateDirections W.S × ℝ) × PolarPoint =>
        W.negativeFirstIntegralDefect x.1 m x.2) := by
  have hzero : (0 : StateDirections W.S × ℝ) ∈
      sectorNeighborhood W.S W.base W.ε W.ε :=
    ⟨(sectorGrading W.S W.base).map_zero'.trans_lt W.ε_pos,
      (abs_zero : |(0 : ℝ)| = 0).trans_lt W.ε_pos⟩
  apply (jointTower_referenceDifference (W.negativeMinusFirstIntegralJointTower m) hzero).congrOn
  intro x hx
  exact congrArg (fun a => W.negativeMinusFirstIntegral x.1 m x.2 - a)
    (W.negativeFirstIntegral_reference m ⟨hx.2.1.1.le, hx.2.1.2.le⟩)

/-- The two projections use the same first-integral defect and its
angular reflection, with the exact reference optical travel. -/
theorem negativeTravel_firstIntegralDefect (z : StateDirections W.S × ℝ)
    (m : ℕ) (p : PolarPoint) :
    n04bActualTravelChart W.S W.C W.L (liftSectorParameter W.S W.C z) m p =
      (opticalTravel W.D.w (W.C.left m) p.1 +
        (W.negativeFirstIntegralDefect z m p +
          W.negativeFirstIntegralDefect z m (p.1, -p.2)) / 2,
        p.2 + (W.negativeFirstIntegralDefect z m p -
          W.negativeFirstIntegralDefect z m (p.1, -p.2)) / 2) := by
  simp only [n04bActualTravelChart, n04bCharacteristicTravelChart, characteristicTravelChart,
    n04bPlusFirstIntegral, negativeFirstIntegralDefect, negativeMinusFirstIntegral]
  apply Prod.ext <;> dsimp only <;> ring

/-- This is the literal stored chart, on the full original component. -/
theorem negativeChart_firstIntegralDefect (z : StateDirections W.S × ℝ)
    (hz : z ∈ sectorNeighborhood W.S W.base W.ε W.ε)
    (m : ℕ) (side : Bool) (p : PolarPoint)
    (hp : p ∈ Ioo (W.C.left m) (W.C.right m) ×ˢ (univ : Set ℝ)) :
    n04bActualNegativeChart W.hT W.hS W.through03 W.field
      (liftSectorParameter W.S W.C z) m side p =
      (n04bRootHalfCoordinate (W.C.travel m) side
        (opticalTravel W.D.w (W.C.left m) p.1 +
          (W.negativeFirstIntegralDefect z m p +
            W.negativeFirstIntegralDefect z m (p.1, -p.2)) / 2),
        p.2 + (W.negativeFirstIntegralDefect z m p -
          W.negativeFirstIntegralDefect z m (p.1, -p.2)) / 2) := by
  have hstored := ((n04bActualNegativeFunctions_spec W.hT W.hS W.through03 W.field
    (liftSectorParameter_mem_stateNeighborhood hz le_rfl)
    (W.through03.1.1.2.2.1.liftSectorParameter_sector z) m side).component_chart_germ hp).self_of_nhds
  exact hstored.trans (congrArg (n04bRootStripChart (W.C.travel m) side)
    (W.negativeTravel_firstIntegralDefect z m p))

end N04RealizationStart
end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationStart.negativeFirstIntegralDefectJointTower'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationStart.negativeFirstIntegralDefectJointTower
