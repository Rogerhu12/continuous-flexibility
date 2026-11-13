import ContinuousFlexibility.Analysis.N04PulledFieldsActualPolynomialGrowth
import ContinuousFlexibility.Analysis.N04PulledFieldsActualVelocityMixedGrowth
import ContinuousFlexibility.Analysis.N04PulledFieldsErrorJoint

/-!
# Actual coefficient-error growth on the retained optical strips

The canonical actual-residual velocity tower supplies the fixed-base
transport estimate. The literal correction polynomial then gives the
two error coefficients. All primitive data come from the retained
optical cutoff; no coefficient estimate is assumed in this assembly.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

local instance n04PulledFieldsActualErrorStripStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {base loss : ℕ} {ε : ℝ}
  (Q : N04bOpticalCutoffData D S C base ε)
  (hN : N01Properties D T S C base loss ε)
  (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
  (hR : N02Properties D T S C R base ε)

/-- The two scalar whole-annulus towers form the actual pair-valued
error tower, before any quantitative bound is attached to it. -/
def n04PulledFields_actualErrorPairJointDirections :
    SmoothDirections (sectorNeighborhood S base ε ε ×ˢ annularOpen D)
      (fun x : (StateDirections S × ℝ) × PolarPoint =>
        returnCorrectionCoefficientError D S C R Q.cutoff
          (liftSectorParameter S C x.1) x.2
            (R.residual (liftSectorParameter S C x.1))) :=
  (smoothDirectionsProd
    (n04PulledFields_actualErrorJointDirections Q hN hS hT hR (ContinuousLinearMap.fst ℝ ℝ ℝ))
    (n04PulledFields_actualErrorJointDirections Q hN hS hT hR (ContinuousLinearMap.snd ℝ ℝ ℝ))).congrOn
      (fun _ _ => rfl)

include hN in
private theorem n04PulledFields_opticalStrip_subset_annulus (m : ℕ) :
    (Ioo (Q.stripLeft m) (Q.stripRight m) ×ˢ (univ : Set ℝ)) ⊆ annularOpen D := by
  intro y hy
  exact ⟨hN.1.1.choose_spec.2.1.2.2.2.1 (Q.cell m)
    (Q.component_cell m (Q.strip_subset m hy.1)), mem_univ _⟩

/-- Restricting the actual pair tower changes none of its derivatives. -/
def n04PulledFields_actualErrorStripDirections (m : ℕ) :
    SmoothDirections
      (sectorNeighborhood S base ε ε ×ˢ (Ioo (Q.stripLeft m) (Q.stripRight m) ×ˢ univ))
      (fun x : (StateDirections S × ℝ) × PolarPoint =>
        returnCorrectionCoefficientError D S C R Q.cutoff
          (liftSectorParameter S C x.1) x.2
            (R.residual (liftSectorParameter S C x.1))) :=
  (n04PulledFields_actualErrorPairJointDirections Q hN hS hT hR).restrict
    ((sectorNeighborhood_isOpen S base ε ε).prod (isOpen_Ioo.prod isOpen_univ))
    (fun _ hx => ⟨hx.1, n04PulledFields_opticalStrip_subset_annulus Q hN m hx.2⟩)

include hN hS hT hR in
/-- Both actual error components have a fixed low base on all strips.
The positive height factor is retained at every parameter order. -/
theorem n04PulledFields_actualErrorStrip_fixedBaseMixedGrowth
    (Jout : ∀ m, SmoothDirections
      (sectorNeighborhood S base ε ε ×ˢ (Ioo (Q.stripLeft m) (Q.stripRight m) ×ˢ univ))
      (fun x : (StateDirections S × ℝ) × PolarPoint =>
        returnCorrectionCoefficientError D S C R Q.cutoff
          (liftSectorParameter S C x.1) x.2
            (R.residual (liftSectorParameter S C x.1)))) :
    let p := pairGrading (sectorGrading S) realGrading
    let W := fun m => radialE (D.cellIndex (Q.cell m))
    let F := fun m => T.H (T.sample m) ^ (3 / 4 : ℝ)
    N04PulledFieldsFixedBaseMixedGrowth p W F
      (fun m => solveSmoothDirectionsPostcomp (Jout m) (ContinuousLinearMap.fst ℝ ℝ ℝ)) ∧
    N04PulledFieldsFixedBaseMixedGrowth p W F
      (fun m => solveSmoothDirectionsPostcomp (Jout m) (ContinuousLinearMap.snd ℝ ℝ ℝ)) := by
  let JV : ∀ m, SmoothDirections
      (sectorNeighborhood S base ε ε ×ˢ (Ioo (Q.stripLeft m) (Q.stripRight m) ×ˢ univ))
      (fun x : (StateDirections S × ℝ) × PolarPoint =>
        returnCorrectionVelocityLinear D S C Q.cutoff (liftSectorParameter S C x.1) m x.2
          (R.residual (liftSectorParameter S C x.1))) := fun m =>
    hN.returnCorrectionVelocity_actual_parameterSpatialTower hS hT
      Q.cutoff Q.range_on_component Q.cutoff_smooth
      m (Q.stripLeft m) (Q.stripRight m) (Q.stripLeft_gt m) (Q.stripRight_lt m)
      (fun z hz y hy => Q.strip_discriminant hN hS hT z hz m y hy) hR
  have hv := hN.n04PulledFields_actualVelocity_fixedBaseMixedGrowth hS hT hR
    (Q.sector_flow_slope hN) Q.cell Q.component_cell
    Q.stripLeft Q.stripRight Q.stripLeft_gt Q.stripRight_lt
    Q.discScale_pos Q.discPower_pos.le Q.strip_positive
    Q.cutoff Q.cutoff_smooth Q.range_on_component Q.derivative_bounds JV
  exact hN.n04PulledFields_actualError_fixedBase_of_velocity hS hT
    Q.cell Q.component_cell Q.cutoff Q.stripLeft Q.stripRight Q.stripLeft_gt Q.stripRight_lt
    Q.discScale_pos Q.discPower_pos.le Q.strip_positive JV Jout hv

end ContinuousFlexibility.Analysis
