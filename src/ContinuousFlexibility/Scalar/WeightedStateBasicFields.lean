module

public import ContinuousFlexibility.Scalar.WeightedStatePrimitives
public import ContinuousFlexibility.Scalar.WeightedOddHeightAlgebra
public import ContinuousFlexibility.Scalar.WeightedScalarPowerMap

/-!
# Actual weighted basic fields of the scalar state

The reference profile acts on decaying heights and odd primitives. The
discriminant and normalized Q defects are genuine elements of the given
height space, expressed only through actual finite spatial derivatives.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
variable (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
  (hS : IsPhysicalSpaces D T S)

def scalarStateWAct (x : ScalarWeightedState S) (u : ScalarHeightSpace S) :
    ScalarHeightSpace S :=
  scalarReferenceWCLM hD hT hS
    (scalarHeightUnitalAct hT hS (scalarStateMeanCLM hD hT hS x) u)

def scalarStateWOddAct (x : ScalarWeightedState S) (u : ScalarHeightSpace S) :
    ScalarHeightSpace S :=
  scalarReferenceWCLM hD hT hS
    (scalarHeightOddUnitalAct hT hS (scalarStateMeanCLM hD hT hS x) u)

def scalarStateEnergyAct (x : ScalarWeightedState S) (u : ScalarHeightSpace S) :
    ScalarHeightSpace S :=
  u + scalarStateWAct hD hT hS x (scalarStateWAct hD hT hS x u)

def scalarStateEnergyOddAct (x : ScalarWeightedState S) (u : ScalarHeightSpace S) :
    ScalarHeightSpace S :=
  u + scalarStateWOddAct hD hT hS x (scalarStateWOddAct hD hT hS x u)

def scalarStateRadialHeight (x : ScalarWeightedState S) : ScalarHeightSpace S :=
  x.2 • scalarStateRadialCLM hD hT hS x

def scalarStateAngularPrimitive (x : ScalarWeightedState S) : ScalarHeightSpace S :=
  x.2 • scalarStateAngularPrimitiveCLM hD hT hS x

def scalarStateMixedPrimitive (x : ScalarWeightedState S) : ScalarHeightSpace S :=
  x.2 • scalarStateAngularRadialPrimitiveCLM hD hT hS x

def scalarStateAngularHeight (x : ScalarWeightedState S) : ScalarHeightSpace S :=
  x.2 • scalarStateAngularSecondCLM hD hT hS x

def scalarStateAngularSquare (x : ScalarWeightedState S) : ScalarHeightSpace S :=
  scalarHeightAngularMul hT hS (scalarStateAngularPrimitive hD hT hS x)
    (scalarStateAngularPrimitive hD hT hS x)

def scalarStateDiscriminantHeight (x : ScalarWeightedState S) : ScalarHeightSpace S :=
  (-2 : ℝ) • scalarStateWAct hD hT hS x (scalarStateRadialHeight hD hT hS x) -
    scalarHeightMul hT hS (scalarStateRadialHeight hD hT hS x)
      (scalarStateRadialHeight hD hT hS x) -
    scalarStateEnergyAct hD hT hS x (scalarStateAngularSquare hD hT hS x)

def scalarStateInverseMeanHeight (x : ScalarWeightedState S) : ScalarHeightSpace S :=
  scalarHeightPower hT hS (-1) (scalarStateMeanCLM hD hT hS x)

def scalarStateQuotientHeight (x : ScalarWeightedState S) : ScalarHeightSpace S :=
  scalarReferenceInvWCLM hD hT hS
    (scalarHeightUnitalAct hT hS (scalarStateInverseMeanHeight hD hT hS x)
      (scalarStateRadialHeight hD hT hS x +
        scalarStateEnergyAct hD hT hS x (scalarStateAngularHeight hD hT hS x)))

theorem decode_scalarStateWAct (x : ScalarWeightedState S) (u : ScalarHeightSpace S)
    (p : PolarPoint) :
    (S.height scalarBeta).decode (scalarStateWAct hD hT hS x u) p =
      scalarStateProfile D S x p.1 * (S.height scalarBeta).decode u p := by
  simp only [scalarStateWAct, decode_scalarReferenceWCLM, decode_scalarHeightUnitalAct,
    decode_scalarStateMeanCLM, scalarStateProfile_eq_mean]
  ring

theorem angularPartial_decode_scalarStateWOddAct
    (x : ScalarWeightedState S) (u : ScalarHeightSpace S) (p : PolarPoint) :
    angularPartial ((S.height scalarBeta).decode (scalarStateWOddAct hD hT hS x u)) p =
      scalarStateProfile D S x p.1 * angularPartial ((S.height scalarBeta).decode u) p := by
  simp only [scalarStateWOddAct, angularPartial_decode_scalarReferenceWCLM,
    angularPartial_decode_scalarHeightOddUnitalAct, decode_scalarStateMeanCLM,
    scalarStateProfile_eq_mean]
  ring

theorem decode_scalarStateEnergyAct (x : ScalarWeightedState S) (u : ScalarHeightSpace S)
    (p : PolarPoint) :
    (S.height scalarBeta).decode (scalarStateEnergyAct hD hT hS x u) p =
      (1 + scalarStateProfile D S x p.1 ^ 2) * (S.height scalarBeta).decode u p := by
  simp only [scalarStateEnergyAct, map_add, Pi.add_apply, decode_scalarStateWAct]
  ring

theorem angularPartial_decode_scalarStateEnergyOddAct
    (x : ScalarWeightedState S) (u : ScalarHeightSpace S) (p : PolarPoint) :
    angularPartial ((S.height scalarBeta).decode (scalarStateEnergyOddAct hD hT hS x u)) p =
      (1 + scalarStateProfile D S x p.1 ^ 2) *
        angularPartial ((S.height scalarBeta).decode u) p := by
  simp only [scalarStateEnergyOddAct, angularPartial_decode_height_add hT hS,
    angularPartial_decode_scalarStateWOddAct]
  ring

theorem decode_scalarStateRadialHeight (x : ScalarWeightedState S) (p : PolarPoint) :
    (S.height scalarBeta).decode (scalarStateRadialHeight hD hT hS x) p =
      x.2 * radialPartial (scalarStateIncrement S x) p := by
  simp only [scalarStateRadialHeight, map_smul, Pi.smul_apply, smul_eq_mul,
    decode_scalarStateRadialCLM]

theorem angularPartial_decode_scalarStateAngularPrimitive
    (x : ScalarWeightedState S) (p : PolarPoint) :
    angularPartial ((S.height scalarBeta).decode (scalarStateAngularPrimitive hD hT hS x)) p =
      x.2 * heightAngular (scalarStateIncrement S x) p := by
  simp only [scalarStateAngularPrimitive, angularPartial_decode_height_smul hT hS,
    angularPartial_decode_scalarStateAngularPrimitiveCLM]

theorem angularPartial_decode_scalarStateMixedPrimitive
    (x : ScalarWeightedState S) (p : PolarPoint) :
    angularPartial ((S.height scalarBeta).decode (scalarStateMixedPrimitive hD hT hS x)) p =
      x.2 * radialPartial (heightAngular (scalarStateIncrement S x)) p := by
  simp only [scalarStateMixedPrimitive, angularPartial_decode_height_smul hT hS,
    angularPartial_decode_scalarStateAngularRadialPrimitiveCLM]

theorem decode_scalarStateAngularHeight (x : ScalarWeightedState S) (p : PolarPoint) :
    (S.height scalarBeta).decode (scalarStateAngularHeight hD hT hS x) p =
      x.2 * angularPartial (heightAngular (scalarStateIncrement S x)) p := by
  simp only [scalarStateAngularHeight, map_smul, Pi.smul_apply, smul_eq_mul,
    decode_scalarStateAngularSecondCLM]

theorem decode_scalarStateAngularSquare (x : ScalarWeightedState S) (p : PolarPoint) :
    (S.height scalarBeta).decode (scalarStateAngularSquare hD hT hS x) p =
      (x.2 * heightAngular (scalarStateIncrement S x) p) ^ 2 := by
  simp only [scalarStateAngularSquare, decode_scalarHeightAngularMul,
    angularPartial_decode_scalarStateAngularPrimitive]
  ring

theorem decode_scalarStateDiscriminantHeight (x : ScalarWeightedState S) (p : PolarPoint) :
    (S.height scalarBeta).decode (scalarStateDiscriminantHeight hD hT hS x) p =
      scalarStateDDefect D S x p := by
  simp only [scalarStateDiscriminantHeight, map_sub, map_smul, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul, decode_scalarStateWAct, decode_scalarHeightMul,
    decode_scalarStateEnergyAct, decode_scalarStateRadialHeight,
    decode_scalarStateAngularSquare, scalarStateDDefect]
  ring

theorem decode_scalarStateQuotientHeight (x : ScalarWeightedState S) (p : PolarPoint)
    (hm : |(S.height scalarBeta).decode (scalarStateMeanCLM hD hT hS x) p| ≤ 1 / 2) :
    (S.height scalarBeta).decode (scalarStateQuotientHeight hD hT hS x) p =
      scalarStateQDefect D S x p := by
  simp only [scalarStateQuotientHeight, scalarStateInverseMeanHeight,
    decode_scalarReferenceInvWCLM, decode_scalarHeightUnitalAct,
    decode_scalarHeightPower_neg_one hT hS _ hm, map_add, Pi.add_apply,
    decode_scalarStateMeanCLM, decode_scalarStateRadialHeight,
    decode_scalarStateEnergyAct, decode_scalarStateAngularHeight]
  simp only [scalarStateQDefect, scalarStateProfile_eq_mean, div_eq_mul_inv, mul_inv_rev]
  ring

theorem scalarStateWAct_zero (x : ScalarWeightedState S) :
    scalarStateWAct hD hT hS x 0 = 0 := by
  simpa only [scalarStateWAct, scalarHeightUnitalAct, scalarHeightMul_zero_right,
    zero_add] using (scalarReferenceWCLM hD hT hS).map_zero

theorem scalarStateEnergyAct_zero (x : ScalarWeightedState S) :
    scalarStateEnergyAct hD hT hS x 0 = 0 := by
  simp only [scalarStateEnergyAct, scalarStateWAct_zero, zero_add]

theorem scalarStateMeanCLM_center (v0 : ScalarHeightSpace S) :
    scalarStateMeanCLM hD hT hS (scalarStateCenter S v0) = 0 := by
  change SobolevModelData.angularMeanCLM hT (hS.1 scalarBeta) 0 = 0
  exact (SobolevModelData.angularMeanCLM hT (hS.1 scalarBeta)).map_zero

theorem scalarStateRadialHeight_center (v0 : ScalarHeightSpace S) :
    scalarStateRadialHeight hD hT hS (scalarStateCenter S v0) = 0 := by
  simp only [scalarStateRadialHeight, scalarStateCenter, zero_smul]

theorem scalarStateAngularPrimitive_center (v0 : ScalarHeightSpace S) :
    scalarStateAngularPrimitive hD hT hS (scalarStateCenter S v0) = 0 := by
  simp only [scalarStateAngularPrimitive, scalarStateCenter, zero_smul]

theorem scalarStateAngularHeight_center (v0 : ScalarHeightSpace S) :
    scalarStateAngularHeight hD hT hS (scalarStateCenter S v0) = 0 := by
  simp only [scalarStateAngularHeight, scalarStateCenter, zero_smul]

theorem scalarStateAngularSquare_center (v0 : ScalarHeightSpace S) :
    scalarStateAngularSquare hD hT hS (scalarStateCenter S v0) = 0 := by
  rw [scalarStateAngularSquare, scalarStateAngularPrimitive_center,
    scalarHeightAngularMul_zero_left]

theorem scalarStateDiscriminantHeight_center (v0 : ScalarHeightSpace S) :
    scalarStateDiscriminantHeight hD hT hS (scalarStateCenter S v0) = 0 := by
  simp only [scalarStateDiscriminantHeight, scalarStateRadialHeight_center,
    scalarStateAngularSquare_center, scalarStateWAct_zero, scalarHeightMul_zero_left,
    scalarStateEnergyAct_zero, smul_zero, sub_zero]

theorem scalarStateQuotientHeight_center (v0 : ScalarHeightSpace S) :
    scalarStateQuotientHeight hD hT hS (scalarStateCenter S v0) = 0 := by
  simpa only [scalarStateQuotientHeight, scalarStateRadialHeight_center,
    scalarStateAngularHeight_center, scalarStateEnergyAct_zero, add_zero,
    scalarHeightUnitalAct, scalarHeightMul_zero_right, zero_add] using
      (scalarReferenceInvWCLM hD hT hS).map_zero

/-- Four actual height ranges suffice for all scalar power identities.
They will be made small simultaneously on one state neighborhood. -/
def ScalarCandidatePowerBounds (x : ScalarWeightedState S) : Prop :=
  (∀ p, |(S.height scalarBeta).decode (scalarStateMeanCLM hD hT hS x) p| ≤ 1 / 2) ∧
  (∀ p, |(S.height scalarBeta).decode (scalarStateDiscriminantHeight hD hT hS x) p| ≤ 1 / 2) ∧
  (∀ p, |(S.height scalarBeta).decode (scalarStateAngularSquare hD hT hS x) p| ≤ 1 / 2) ∧
  ∀ p, |(S.height scalarBeta).decode (scalarStateQuotientHeight hD hT hS x) p| ≤ 1 / 2

end ContinuousFlexibility.Statements
