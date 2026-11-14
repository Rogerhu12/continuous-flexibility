import ContinuousFlexibility.Analysis.ReturnCorrectionTransportEquations
import ContinuousFlexibility.Analysis.SolveReturnEquations

/-!
# Actual transport identities on the original sector parameter

The original N01 slope and the N02 residual-substituted displacement
satisfy the same radial system. These identities keep the actual sector
lift and the supplied residual, without adding a residual parameter.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped ContDiff

local instance n04PulledFieldsActualTransportStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

theorem N01Properties.n04PulledFields_slope_radialEquation
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (m : ℕ) (x : StateDirections S × ℝ) (hx : x ∈ sectorNeighborhood S base ε ε)
    (y : PolarPoint) (hy : y.1 ∈ Ioo (C.left m) (C.right m))
    (hdisc : 0 < (originalCoefficients D S C (liftSectorParameter S C x)).b y ^ 2 -
      (originalCoefficients D S C (liftSectorParameter S C x)).a y *
        (originalCoefficients D S C (liftSectorParameter S C x)).c y) :
    radialPartial (returnFlowInverseSlope S C (liftSectorParameter S C x) m) y =
      angularPartial (minusCharacteristicSpeed
        (originalCoefficients D S C (liftSectorParameter S C x))) y *
          returnFlowInverseSlope S C (liftSectorParameter S C x) m y -
      minusCharacteristicSpeed (originalCoefficients D S C (liftSectorParameter S C x)) y *
        angularPartial (returnFlowInverseSlope S C (liftSectorParameter S C x) m) y :=
  hN.returnFlowInverseSlope_transport_of_discriminant
    (D := D) (T := T) (S := S) (C := C) (base := base) (loss := loss) (ε := ε)
    (z := liftSectorParameter S C x) hS hT
    (liftSectorParameter_mem_stateNeighborhood hx le_rfl)
    (hN.2.2.1.liftSectorParameter_sector x) m y hy hdisc

theorem N01Properties.n04PulledFields_actualDisplacement_radialEquation
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    {R : ReturnEquationData S} (hR : N02Properties D T S C R base ε)
    (χ : ℕ → ℝ → ℝ) (m : ℕ) (hχ : ContDiff ℝ ∞ (χ m))
    (hχrange : ∀ r ∈ Icc (C.left m) (C.right m), χ m r ∈ Icc (0 : ℝ) 1)
    (x : StateDirections S × ℝ) (hx : x ∈ sectorNeighborhood S base ε ε)
    (y : PolarPoint) (hy : y.1 ∈ Ioo (C.left m) (C.right m)) :
    radialPartial (fun q => returnCorrectionPulledDisplacementLinear S C χ
      (liftSectorParameter S C x) m q (R.residual (liftSectorParameter S C x))) y =
      -((minusCharacteristicSpeed (originalCoefficients D S C (liftSectorParameter S C x)) y +
          deriv (χ m) y.1 * returnFlowInverseSlope S C (liftSectorParameter S C x) m y *
            returnCorrectionPulledDisplacementLinear S C χ (liftSectorParameter S C x) m y
              (R.residual (liftSectorParameter S C x))) *
        angularPartial (fun q => returnCorrectionPulledDisplacementLinear S C χ
          (liftSectorParameter S C x) m q (R.residual (liftSectorParameter S C x))) y) := by
  simpa only [neg_mul] using hN.returnCorrectionPulledDisplacementLinear_transport_actual
    (D := D) (T := T) (S := S) (C := C) (R := R)
    (base := base) (loss := loss) (ε := ε) (z := liftSectorParameter S C x)
    hS hT (liftSectorParameter_mem_stateNeighborhood hx le_rfl)
    (hN.2.2.1.liftSectorParameter_sector x) hR χ m hχ hχrange
    (R.residual (liftSectorParameter S C x)) y hy

end ContinuousFlexibility.Statements
