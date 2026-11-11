import ContinuousFlexibility.Analysis.N01EndpointAngularJets
import ContinuousFlexibility.Analysis.N01FlowSmallness
import ContinuousFlexibility.Analysis.SmoothDirectionsJointAngular
import ContinuousFlexibility.Analysis.TameElementaryCalculus

/-!
# Genuine joint N01 parameter and angular towers at closed radii

The original closed-radius scalar towers have compatible angular jets.
Their finite joint expansion gives the actual flow increment, and the
explicit reference flow restores the original flow. This construction
applies to every radius in the closed flow interval.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

local instance n01FlowJointParameterTowerStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul
local instance n01FlowJointParameterTowerParameterSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S × ℝ) := Prod.instSMul
local instance n01FlowJointParameterTowerRealNormedSpace : NormedSpace ℝ ℝ :=
  NormedField.toNormedSpace

open Set Filter ContinuousFlexibility.Analysis
open scoped Topology

private def restoreAffineScalarTower
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    {U : Set E} {f g : E → ℝ} (J : SmoothDirections U f)
    (L : E →L[ℝ] ℝ) (c : ℝ)
    (heq : ∀ x ∈ U, f x + (c + L x) = g x) : SmoothDirections U g := by
  let K : SmoothDirections U (fun x => c + L x) :=
    (smoothDirectionsLinear (ContinuousLinearMap.id ℝ ℝ)).compAffine L c J.open_domain
      (fun _ _ => mem_univ _)
  exact (smoothDirectionsAdd J K).congrOn (fun x hx => heq x hx)

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

def N01Properties.sectorFlow_closed_jointTower
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (m : ℕ) (r : ℝ) (hr : r ∈ Icc (C.left m) (C.right m)) :
    SmoothDirections (sectorNeighborhood S base ε ε ×ˢ univ)
      (fun z : (StateDirections S × ℝ) × ℝ =>
        ordinaryFlowFamily S C m 0 0 (r, z.2) (liftSectorParameter S C z.1)) :=
  angularTowerJointDirections (hN.sectorFlow_closed_angularTower hS hT m r hr)
    (hN.sectorFlow_closed_angularTower_joint_continuous hS hT m r hr)
    (hN.sectorFlow_closed_angularTower_hasDerivAt hS hT m r hr)

theorem N01Properties.sectorFlow_closed_jointTower_apply
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (m : ℕ) (r : ℝ) (hr : r ∈ Icc (C.left m) (C.right m))
    (n : ℕ) (z : (StateDirections S × ℝ) × ℝ)
    (v : Fin n → (StateDirections S × ℝ) × ℝ) :
    (hN.sectorFlow_closed_jointTower hS hT m r hr).D n z v =
      scalarAngularExpansion n (fun b k =>
        ((hN.sectorFlow_closed_angularTower hS hT m r hr b z.2).D k z.1).toMultilinearMap) v := rfl

attribute [local irreducible] N01Properties.sectorFlow_closed_jointTower

def N01Properties.minusFlow_jointTower
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (m : ℕ) (r : ℝ) (hr : r ∈ Icc (C.left m) (C.right m)) :
    SmoothDirections (sectorNeighborhood S base ε ε ×ˢ univ)
      (fun z : (StateDirections S × ℝ) × ℝ =>
        C.minusFlow (liftSectorParameter S C z.1) m r z.2) := by
  refine restoreAffineScalarTower
    (E := (StateDirections S × ℝ) × ℝ)
    (U := sectorNeighborhood S base ε ε ×ˢ univ)
    (f := fun z : (StateDirections S × ℝ) × ℝ =>
      ordinaryFlowFamily S C m 0 0 (r, z.2) (liftSectorParameter S C z.1))
    (g := fun z : (StateDirections S × ℝ) × ℝ =>
      C.minusFlow (liftSectorParameter S C z.1) m r z.2)
    (hN.sectorFlow_closed_jointTower hS hT m r hr)
    (ContinuousLinearMap.snd ℝ (StateDirections S × ℝ) ℝ)
    (-opticalTravel D.w (C.left m) r) ?_
  intro z hz
  change ordinaryFlowFamily S C m 0 0 (r, z.2) (liftSectorParameter S C z.1) +
    (-opticalTravel D.w (C.left m) r + z.2) = _
  simp only [ordinaryFlowFamily, mixedDerivative, iteratedDeriv_zero]
  have href := hN.minusFlow_reference_eq hS hT m hr z.2
  linarith only [href]

end ContinuousFlexibility.Statements
