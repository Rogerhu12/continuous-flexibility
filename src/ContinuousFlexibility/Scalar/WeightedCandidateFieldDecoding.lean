import ContinuousFlexibility.Scalar.WeightedScalarCandidates
import ContinuousFlexibility.Scalar.WeightedStateCoefficientFormulas
import ContinuousFlexibility.Scalar.WeightedResidualFormulas

/-!
# Literal decoders of the finite scalar candidate fields

The four actual range bounds are used only to identify the globally smooth
power extensions with the required roots and reciprocals. All other
identities are global algebraic identities of the actual decoders.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
variable (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
  (hS : IsPhysicalSpaces D T S) (x : ScalarWeightedState S)
  (hb : ScalarCandidatePowerBounds hD hT hS x)

theorem decode_scalarStateDPower_half (p : PolarPoint) :
    (S.height scalarBeta).decode (scalarStateDPower hD hT hS (1 / 2 : ℝ) x) p =
      Real.sqrt (1 + scalarStateDDefect D S x p) - 1 := by
  rw [scalarStateDPower, decode_scalarHeightPower_half hT hS _ (hb.2.1 p),
    decode_scalarStateDiscriminantHeight]

theorem decode_scalarStateDPower_neg_half (p : PolarPoint) :
    (S.height scalarBeta).decode (scalarStateDPower hD hT hS (-(1 / 2) : ℝ) x) p =
      (Real.sqrt (1 + scalarStateDDefect D S x p))⁻¹ - 1 := by
  rw [scalarStateDPower, decode_scalarHeightPower_neg_half hT hS _ (hb.2.1 p),
    decode_scalarStateDiscriminantHeight]

theorem decode_scalarStateDPower_neg_three_halves (p : PolarPoint) :
    (S.height scalarBeta).decode (scalarStateDPower hD hT hS (-(3 / 2) : ℝ) x) p =
      inverseDThreeHalves (1 + scalarStateDDefect D S x p) - 1 := by
  rw [scalarStateDPower, decode_scalarHeightPower_neg_three_halves hT hS _ (hb.2.1 p),
    decode_scalarStateDiscriminantHeight]

private theorem scalarState_neg_angularSquare_bound (p : PolarPoint) :
    |(S.height scalarBeta).decode (-scalarStateAngularSquare hD hT hS x) p| ≤ 1 / 2 := by
  simpa only [map_neg, Pi.neg_apply, abs_neg] using hb.2.2.1 p

theorem decode_scalarStateAngularPower_half (p : PolarPoint) :
    (S.height scalarBeta).decode (scalarStateAngularPower hD hT hS (1 / 2 : ℝ) x) p =
      Real.sqrt (1 - (x.2 * heightAngular (scalarStateIncrement S x) p) ^ 2) - 1 := by
  rw [scalarStateAngularPower, decode_scalarHeightPower_half hT hS _
    (scalarState_neg_angularSquare_bound hD hT hS x hb p),
    map_neg, Pi.neg_apply, decode_scalarStateAngularSquare]
  <;> simp only [sub_eq_add_neg]

theorem decode_scalarStateAngularPower_neg_half (p : PolarPoint) :
    (S.height scalarBeta).decode (scalarStateAngularPower hD hT hS (-(1 / 2) : ℝ) x) p =
      (Real.sqrt (1 - (x.2 * heightAngular (scalarStateIncrement S x) p) ^ 2))⁻¹ - 1 := by
  rw [scalarStateAngularPower, decode_scalarHeightPower_neg_half hT hS _
    (scalarState_neg_angularSquare_bound hD hT hS x hb p),
    map_neg, Pi.neg_apply, decode_scalarStateAngularSquare]
  <;> simp only [sub_eq_add_neg]

theorem decode_scalarStateAngularPower_neg_one (p : PolarPoint) :
    (S.height scalarBeta).decode (scalarStateAngularPower hD hT hS (-1) x) p =
      (1 - (x.2 * heightAngular (scalarStateIncrement S x) p) ^ 2)⁻¹ - 1 := by
  rw [scalarStateAngularPower, decode_scalarHeightPower_neg_one hT hS _
    (scalarState_neg_angularSquare_bound hD hT hS x hb p),
    map_neg, Pi.neg_apply, decode_scalarStateAngularSquare]
  <;> simp only [sub_eq_add_neg]

theorem decode_scalarStateQPower_neg_one (p : PolarPoint) :
    (S.height scalarBeta).decode (scalarStateQPower hD hT hS (-1) x) p =
      (1 + scalarStateQDefect D S x p)⁻¹ - 1 := by
  rw [scalarStateQPower, decode_scalarHeightPower_neg_one hT hS _ (hb.2.2.2 p),
    decode_scalarStateQuotientHeight hD hT hS x p (hb.1 p)]

theorem decode_scalarStateInverseMeanHeight (p : PolarPoint) :
    (S.height scalarBeta).decode (scalarStateInverseMeanHeight hD hT hS x) p =
      (1 + scalarStateProfileMean S x p.1)⁻¹ - 1 := by
  rw [scalarStateInverseMeanHeight, decode_scalarHeightPower_neg_one hT hS _ (hb.1 p),
    decode_scalarStateMeanCLM]

theorem decode_scalarStateSlopeAct (u : ScalarHeightSpace S) (p : PolarPoint) :
    (S.height scalarBeta).decode (scalarStateSlopeAct hD hT hS x u) p =
      (scalarStateProfile D S x p.1 + x.2 * radialPartial (scalarStateIncrement S x) p) *
        (S.height scalarBeta).decode u p := by
  simp only [scalarStateSlopeAct, map_add, Pi.add_apply, decode_scalarStateWAct,
    decode_scalarHeightMul, decode_scalarStateRadialHeight]
  ring

theorem angularPartial_decode_scalarStateSlopeOddAct
    (u : ScalarHeightSpace S) (p : PolarPoint) :
    angularPartial ((S.height scalarBeta).decode (scalarStateSlopeOddAct hD hT hS x u)) p =
      (scalarStateProfile D S x p.1 + x.2 * radialPartial (scalarStateIncrement S x) p) *
        angularPartial ((S.height scalarBeta).decode u) p := by
  simp only [scalarStateSlopeOddAct, angularPartial_decode_height_add,
    angularPartial_decode_scalarStateWOddAct, angularPartial_decode_scalarHeightOddMul,
    decode_scalarStateRadialHeight]
  ring

theorem decode_scalarStateWDerivAct (u : ScalarHeightSpace S) (p : PolarPoint) :
    (S.height scalarBeta).decode (scalarStateWDerivAct hD hT hS x u) p =
      deriv (scalarStateProfile D S x) p.1 * (S.height scalarBeta).decode u p := by
  simp only [scalarStateWDerivAct, map_add, Pi.add_apply, decode_scalarReferenceWDerivCLM,
    decode_scalarReferenceWCLM, decode_scalarHeightUnitalAct, decode_scalarHeightMul,
    decode_scalarStateMeanCLM, decode_scalarStateMeanDerivCLM,
    scalarStateProfile_deriv_expansion hD hT hS]
  ring

theorem decode_scalarStateConnectionFactor (p : PolarPoint) :
    (S.height scalarBeta).decode (scalarStateConnectionFactor hD hT hS x) p =
      (1 - (x.2 * heightAngular (scalarStateIncrement S x) p) ^ 2)⁻¹ *
        (Real.sqrt (1 + scalarStateDDefect D S x p))⁻¹ - 1 := by
  simp only [scalarStateConnectionFactor, decode_scalarHeightUnitalMul,
    decode_scalarStateAngularPower_neg_one hD hT hS x hb,
    decode_scalarStateDPower_neg_half hD hT hS x hb]
  ring

theorem decode_scalarStateMeanSquare (p : PolarPoint) :
    (S.height scalarBeta).decode (scalarStateMeanSquare hD hT hS x) p =
      (1 + scalarStateProfileMean S x p.1) ^ 2 - 1 := by
  simp only [scalarStateMeanSquare, decode_scalarHeightUnitalMul, decode_scalarStateMeanCLM]
  ring

theorem decode_scalarStateMeanFourth (p : PolarPoint) :
    (S.height scalarBeta).decode (scalarStateMeanFourth hD hT hS x) p =
      (1 + scalarStateProfileMean S x p.1) ^ 4 - 1 := by
  simp only [scalarStateMeanFourth, decode_scalarHeightUnitalMul, decode_scalarStateMeanSquare]
  ring

theorem decode_scalarStateSigma (p : PolarPoint) :
    (S.height scalarBeta).decode (scalarStateSigma hD hT hS x) p =
      (1 + scalarStateQDefect D S x p)⁻¹ *
        (Real.sqrt (1 + scalarStateDDefect D S x p))⁻¹ - 1 := by
  simp only [scalarStateSigma, decode_scalarHeightUnitalMul,
    decode_scalarStateQPower_neg_one hD hT hS x hb,
    decode_scalarStateDPower_neg_half hD hT hS x hb]
  ring

theorem decode_scalarCoefficientAHeight_finite (p : PolarPoint) :
    (S.height scalarBeta).decode (scalarCoefficientAHeight hD hT hS x) p =
      scalarCoefficientFiniteFormula D S x 0 p := by
  simp only [scalarCoefficientAHeight, decode_scalarReferenceWCLM,
    decode_scalarHeightUnitalMul, decode_scalarStateMeanCLM,
    decode_scalarStateQuotientHeight hD hT hS x p (hb.1 p),
    decode_scalarStateDPower_neg_three_halves hD hT hS x hb,
    scalarCoefficientFiniteFormula]
  ring

theorem angularPartial_decode_scalarCoefficientBPrimitive_finite (p : PolarPoint) :
    angularPartial ((S.height scalarBeta).decode (scalarCoefficientBPrimitive hD hT hS x)) p =
      scalarCoefficientFiniteFormula D S x 1 p := by
  simp only [scalarCoefficientBPrimitive, angularPartial_decode_height_neg,
    angularPartial_decode_scalarHeightOddUnitalAct,
    decode_scalarStateDPower_neg_three_halves hD hT hS x hb,
    angularPartial_decode_scalarStateEnergyOddAct,
    angularPartial_decode_scalarStateMixedPrimitive,
    scalarCoefficientFiniteFormula, scalarStateProfile_eq_mean]
  ring

theorem decode_scalarCoefficientQuadraticHeight (p : PolarPoint) :
    (S.height scalarBeta).decode (scalarCoefficientQuadraticHeight hD hT hS x) p =
      ((D.w p.1)⁻¹ + 2 * D.w p.1 * (1 + scalarStateProfileMean S x p.1) ^ 2 +
        D.w p.1 ^ 3 * (1 + scalarStateProfileMean S x p.1) ^ 4) *
          (x.2 * radialPartial (heightAngular (scalarStateIncrement S x)) p) ^ 2 := by
  simp only [scalarCoefficientQuadraticHeight, map_add, map_smul, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, decode_scalarReferenceInvWCLM, decode_scalarReferenceWCLM,
    decode_scalarHeightUnitalAct, decode_scalarStateMeanSquare, decode_scalarStateMeanFourth,
    decode_scalarHeightAngularMul, angularPartial_decode_scalarStateMixedPrimitive]
  ring

theorem decode_scalarCoefficientCHeight_finite (p : PolarPoint) :
    (S.height scalarBeta).decode (scalarCoefficientCHeight hD hT hS x) p =
      scalarCoefficientFiniteFormula D S x 2 p := by
  simp only [scalarCoefficientCHeight, map_add, Pi.add_apply,
    decode_scalarReferenceInvRadiusCLM, decode_scalarReferenceWDerivCLM,
    decode_scalarReferenceWCLM, decode_scalarHeightUnitalMul, decode_scalarHeightUnitalAct,
    decode_scalarStateMeanCLM, decode_scalarStateMeanDerivCLM,
    decode_scalarStateSigma hD hT hS x hb, decode_scalarStateInverseMeanHeight hD hT hS x hb,
    decode_scalarStateQPower_neg_one hD hT hS x hb,
    decode_scalarStateDPower_neg_three_halves hD hT hS x hb,
    decode_scalarCoefficientQuadraticHeight, scalarCoefficientFiniteFormula, div_eq_mul_inv]
  ring

theorem decode_scalarCandidateResidual_finite (p : PolarPoint) :
    (S.height scalarBeta).decode (scalarCandidateResidual hD hT hS x) p =
      scalarResidualFiniteFormula D S x p := by
  simp only [scalarCandidateResidual, scalarResidualNumeratorHeight,
    decode_scalarHeightUnitalAct, decode_scalarStateDPower_neg_three_halves hD hT hS x hb,
    map_add, map_sub, map_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    decode_scalarStateWDerivAct, decode_scalarStateWAct, decode_scalarHeightMul,
    decode_scalarStateEnergyAct, decode_scalarReferenceRadiusCLM, decode_scalarHeightAngularMul,
    decode_scalarStateRadialCLM, decode_scalarStateRadialSecondCLM,
    decode_scalarStateAngularSecondCLM, angularPartial_decode_scalarStateAngularPrimitiveCLM,
    angularPartial_decode_scalarStateAngularRadialPrimitiveCLM,
    scalarResidualFiniteFormula, scalarStateProfile_eq_mean,
    scalarStateProfile_deriv_expansion hD hT hS]
  ring

end ContinuousFlexibility.Statements
