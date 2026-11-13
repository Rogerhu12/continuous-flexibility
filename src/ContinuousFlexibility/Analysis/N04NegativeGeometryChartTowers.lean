import ContinuousFlexibility.Analysis.N04NegativeGeometryTravelTower
import ContinuousFlexibility.Analysis.N04RealizationLeadStart
import ContinuousFlexibility.Analysis.N04RealizationJointMixedRegularity
import ContinuousFlexibility.Analysis.N04RealizationJointSpatialEvaluation
import ContinuousFlexibility.Analysis.SmoothDirectionsGluing
import ContinuousFlexibility.Analysis.SmoothDirectionsNormedComposition
import ContinuousFlexibility.Analysis.N04bOpticalCutoffProperties

/-!
# The actual negative chart jointly in state and physical position

The interior strip towers of the literal travel chart agree on overlaps.
They therefore give one tower on the whole original negative component.
Strict positivity in the travel strip permits the fixed root change of
coordinates, and the prescribed component germ identifies its value with
the stored chart.  This construction does not use the moving half-domain.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

/-- Interior strips cover the full open physical component, with the same
parameter neighborhood and the same function on every overlap. -/
def n04NegativeGeometry_glueComponentTowers
    {X F : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F] [T2Space F]
    {U : Set X} {l h : ℝ} {f : X × PolarPoint → F}
    (hU : IsOpen U)
    (J : ∀ a b : ℝ, l < a → b < h →
      SmoothDirections (U ×ˢ (Ioo a b ×ˢ univ)) f) :
    SmoothDirections (U ×ˢ (Ioo l h ×ˢ univ)) f := by
  let V : Ioo l h → Set (X × PolarPoint) := fun r =>
    U ×ˢ (Ioo ((l + r.val) / 2) ((r.val + h) / 2) ×ˢ univ)
  let K : ∀ r : Ioo l h, SmoothDirections (V r) f := fun r =>
    J ((l + r.val) / 2) ((r.val + h) / 2)
      (by linarith only [r.property.1]) (by linarith only [r.property.2])
  have hsub : ∀ r, V r ⊆ U ×ˢ (Ioo l h ×ˢ (univ : Set ℝ)) := by
    intro r x hx
    refine ⟨hx.1, ⟨?_, ?_⟩, mem_univ _⟩
    · have hr := r.property.1
      have hp := hx.2.1.1
      linarith
    · have hr := r.property.2
      have hp := hx.2.1.2
      linarith
  have hcover : ∀ x ∈ U ×ˢ (Ioo l h ×ˢ (univ : Set ℝ)),
      ∃ r, x ∈ V r := by
    intro x hx
    refine ⟨⟨x.2.1, hx.2.1⟩, hx.1, ⟨?_, ?_⟩, mem_univ _⟩
    · dsimp only [V]
      linarith only [hx.2.1.1]
    · dsimp only [V]
      linarith only [hx.2.1.2]
  exact (exists_smoothDirections_of_open_cover
    (hU.prod (isOpen_Ioo.prod isOpen_univ)) V K hsub hcover).choose

namespace N04RealizationStart

variable (W : N04RealizationStart)

/-- The literal actual travel chart has one joint tower on its entire
original component before any spatial or parameter order is selected. -/
def negativeTravelJointTower (m : ℕ) :
    SmoothDirections
      (sectorNeighborhood W.S W.base W.ε W.ε ×ˢ
        (Ioo (W.C.left m) (W.C.right m) ×ˢ univ))
      (fun x : (StateDirections W.S × ℝ) × PolarPoint =>
        n04bActualTravelChart W.S W.C W.L
          (liftSectorParameter W.S W.C x.1) m x.2) := by
  apply n04NegativeGeometry_glueComponentTowers
    (sectorNeighborhood_isOpen W.S W.base W.ε W.ε)
  intro l h hl hh
  exact W.through03.1.1.n04NegativeGeometryActualTravelChart_stripJointTower
    W.hS W.hT W.field W.cutoff.cutoff W.cutoff.cutoff_smooth
    W.cutoff.range_on_component W.coefficients_eq W.minusFlow_eq
    W.cutoff.discriminant_on_support m l h hl hh

/-- The fixed root reparametrization is smooth at every image point of
the whole open physical component, for both root orientations. -/
def negativeRootChartJointTower (m : ℕ) (side : Bool) :
    SmoothDirections
      (sectorNeighborhood W.S W.base W.ε W.ε ×ˢ
        (Ioo (W.C.left m) (W.C.right m) ×ˢ univ))
      (fun x : (StateDirections W.S × ℝ) × PolarPoint =>
        n04bRootPhysicalChart
          (n04bActualTravelChart W.S W.C W.L (liftSectorParameter W.S W.C x.1) m)
          (W.C.travel m) side x.2) := by
  apply (W.negativeTravelJointTower m).comp_contDiff
    (isOpen_Ioo.prod isOpen_univ)
    (g := n04bRootStripChart (W.C.travel m) side)
    (V := Ioo (0 : ℝ) (W.C.travel m) ×ˢ (univ : Set ℝ))
  · intro p hp
    exact (n04b_contDiffAt_rootStripChart (W.C.travel m) side
      (n04b_travelOrientation_pos_of_fullStrip side hp.1)).contDiffWithinAt
  · intro x hx
    exact (n04b_actualTravelChart_bijOn W.through03 W.hS W.hT W.field
      (liftSectorParameter_mem_stateNeighborhood hx.1 le_rfl)
      (W.through03.1.1.2.2.1.liftSectorParameter_sector x.1) m).mapsTo hx.2

/-- The chosen negative chart is pointwise the root formula throughout
the component, so its actual joint tower is independent of its choice. -/
def negativeChartJointTower (m : ℕ) (side : Bool) :
    SmoothDirections
      (sectorNeighborhood W.S W.base W.ε W.ε ×ˢ
        (Ioo (W.C.left m) (W.C.right m) ×ˢ univ))
      (fun x : (StateDirections W.S × ℝ) × PolarPoint =>
        n04bActualNegativeChart W.hT W.hS W.through03 W.field
          (liftSectorParameter W.S W.C x.1) m side x.2) := by
  apply (W.negativeRootChartJointTower m side).congrOn
  intro x hx
  exact ((n04bActualNegativeFunctions_spec W.hT W.hS W.through03 W.field
    (liftSectorParameter_mem_stateNeighborhood hx.1 le_rfl)
    (W.through03.1.1.2.2.1.liftSectorParameter_sector x.1) m side).component_chart_germ
      hx.2).self_of_nhds.symm

/-- Every scalar projection and every mixed physical derivative of the
same stored chart has its genuine parameter tower on the original sector. -/
def negativeChartMixedRegularity (m : ℕ) (side : Bool)
    (A : PolarPoint →L[ℝ] ℝ) :
    MixedJetRegularity (sectorNeighborhood W.S W.base W.ε W.ε)
      (Ioo (W.C.left m) (W.C.right m) ×ˢ univ)
      (fun z p => A (n04bActualNegativeChart W.hT W.hS W.through03 W.field
        (liftSectorParameter W.S W.C z) m side p)) :=
  n04Realization_jointMixedRegularity
    (solveSmoothDirectionsPostcomp (W.negativeChartJointTower m side) A)
    (sectorNeighborhood_isOpen W.S W.base W.ε W.ε)
    (isOpen_Ioo.prod isOpen_univ)
    ((sectorNeighborhood_convex W.S W.base W.ε W.ε).prod
      ((convex_Ioo _ _).prod convex_univ))

end N04RealizationStart
end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationStart.negativeChartJointTower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationStart.negativeChartJointTower
