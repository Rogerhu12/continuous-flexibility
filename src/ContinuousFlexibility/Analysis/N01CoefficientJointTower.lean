module

public import ContinuousFlexibility.Analysis.N01OriginalCoefficientSpatialJets
public import ContinuousFlexibility.Analysis.N01ReturnVelocitySpatialTower
public import ContinuousFlexibility.Analysis.SmoothDirectionsSpatialJoint

/-!
# Actual original coefficients jointly in state and both spatial variables

The mixed N01 coefficient towers provide the parameter derivatives.
Their original one-high estimates supply the uniform seminorm bounds
needed to join the two physical coordinates. Adding back the actual
reference coefficient gives the full original coefficient, at order
zero as well as every positive parameter order.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Statements

local instance n01CoefficientJointTowerStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

open Set ContinuousFlexibility.Analysis
open scoped ContDiff Topology

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
  (hN : N01Properties D T S C base loss ε)
  (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
  (m j : ℕ) (hcell : Ioo (C.left m) (C.right m) ⊆ D.cells j)
  (i : Fin 3)

include hN in
theorem N01Properties.negativeComponent_subset_annularOpen :
    Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ) ⊆ annularOpen D := by
  intro p hp
  have hends := hN.2.2.2.1.1 m
  exact ⟨⟨hends.1.trans hp.1.1, hp.1.2.trans hends.2.2⟩, mem_univ _⟩

def N01Properties.coefficientIncrement_spatialJointTower :
    SmoothDirections
      ((sectorNeighborhood S base ε ε ×ˢ Ioo (C.left m) (C.right m)) ×ˢ univ)
      (fun x : ((StateDirections S × ℝ) × ℝ) × ℝ =>
        coefficientFamily D S C i 0 0 (x.1.2, x.2) (liftSectorParameter S C x.1.1)) := by
  let J := hN.componentCoefficientTower m j hcell i
  apply mixedScalarSpatialJointDirections J
    (sectorNeighborhood_isOpen S base ε ε) (sectorNeighborhood_convex S base ε ε)
    isOpen_Ioo _ (hN.componentCoefficientTower_uniformBounds hT m j hcell i) _ _
    (convex_Ioo (C.left m) (C.right m))
  · intro a b x hx
    exact (hN.coefficientFamily_contDiffOn hS hT
      (liftSectorParameter_mem_stateNeighborhood hx le_rfl)
      (hN.2.2.1.liftSectorParameter_sector x) i a b).continuousOn.mono
        (hN.negativeComponent_subset_annularOpen m)
  · intro a b p hp x hx
    exact hN.coefficientFamily_hasDerivAt_radial hS hT
      (liftSectorParameter_mem_stateNeighborhood hx le_rfl)
      (hN.2.2.1.liftSectorParameter_sector x) i a b
      (hN.negativeComponent_subset_annularOpen m hp)
  · intro a b p hp x hx
    exact hN.coefficientFamily_hasDerivAt_angular hS hT
      (liftSectorParameter_mem_stateNeighborhood hx le_rfl)
      (hN.2.2.1.liftSectorParameter_sector x) i a b
      (hN.negativeComponent_subset_annularOpen m hp)

def N01Properties.coefficientIncrement_parameterSpatialTower :
    SmoothDirections
      (sectorNeighborhood S base ε ε ×ˢ (Ioo (C.left m) (C.right m) ×ˢ univ))
      (fun x : (StateDirections S × ℝ) × PolarPoint =>
        coefficientFamily D S C i 0 0 x.2 (liftSectorParameter S C x.1)) :=
  (hN.coefficientIncrement_spatialJointTower hS hT m j hcell i).compLinear
    (parameterSpatialAssociation (StateDirections S × ℝ))
    ((sectorNeighborhood_isOpen S base ε ε).prod (isOpen_Ioo.prod isOpen_univ))
    (fun x hx => ⟨⟨hx.1, hx.2.1⟩, hx.2.2⟩)

def N01Properties.originalCoefficient_parameterSpatialTower :
    SmoothDirections
      (sectorNeighborhood S base ε ε ×ˢ (Ioo (C.left m) (C.right m) ×ˢ univ))
      (fun x : (StateDirections S × ℝ) × PolarPoint =>
        originalCoefficientEntry D S C i (liftSectorParameter S C x.1) x.2) := by
  let J := hN.coefficientIncrement_parameterSpatialTower hS hT m j hcell i
  have href : ContDiffOn ℝ ∞ (originalCoefficientEntry D S C i (C.referenceState, 0))
      (Ioo (C.left m) (C.right m) ×ˢ univ) :=
    (hN.original_coefficient_contDiffOn hS hT hN.reference_mem_stateNeighborhood
      hN.2.2.1.stateSector i).mono (hN.negativeComponent_subset_annularOpen m)
  let P : ((StateDirections S × ℝ) × PolarPoint) →L[ℝ] PolarPoint :=
    ContinuousLinearMap.snd ℝ (StateDirections S × ℝ) PolarPoint
  let K := (smoothDirectionsOfContDiffOn (isOpen_Ioo.prod isOpen_univ) href).compLinear P
    ((sectorNeighborhood_isOpen S base ε ε).prod (isOpen_Ioo.prod isOpen_univ))
    (fun x hx => hx.2)
  apply (smoothDirectionsAdd J K).congrOn
  intro x hx
  change coefficientFamily D S C i 0 0 x.2 (liftSectorParameter S C x.1) +
    originalCoefficientEntry D S C i (C.referenceState, 0) x.2 = _
  simp only [coefficientFamily, mixedDerivative, iteratedDeriv_zero,
    originalCoefficientEntry, ite_apply]
  split_ifs <;> ring

end ContinuousFlexibility.Statements
