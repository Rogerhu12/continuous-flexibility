import ContinuousFlexibility.Scalar.WeightedStateBasicFields

/-!
# Concrete candidate maps for every scalar output

Every output is built from the actual weighted linear maps, products, odd
primitive products, and canonical scalar compositions. Constant reference
backgrounds enter through radial multiplier maps and unital actions. No
candidate uses division by the construction parameter.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
variable (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
  (hS : IsPhysicalSpaces D T S)

def scalarStateDPower (α : ℝ) (x : ScalarWeightedState S) : ScalarHeightSpace S :=
  scalarHeightPower hT hS α (scalarStateDiscriminantHeight hD hT hS x)

def scalarStateAngularPower (α : ℝ) (x : ScalarWeightedState S) : ScalarHeightSpace S :=
  scalarHeightPower hT hS α (-scalarStateAngularSquare hD hT hS x)

def scalarStateQPower (α : ℝ) (x : ScalarWeightedState S) : ScalarHeightSpace S :=
  scalarHeightPower hT hS α (scalarStateQuotientHeight hD hT hS x)

def scalarStateSlopeAct (x : ScalarWeightedState S) (u : ScalarHeightSpace S) :
    ScalarHeightSpace S :=
  scalarStateWAct hD hT hS x u +
    scalarHeightMul hT hS (scalarStateRadialHeight hD hT hS x) u

def scalarStateSlopeOddAct (x : ScalarWeightedState S) (u : ScalarHeightSpace S) :
    ScalarHeightSpace S :=
  scalarStateWOddAct hD hT hS x u +
    scalarHeightOddMul hT hS (scalarStateRadialHeight hD hT hS x) u

def scalarStateWDerivAct (x : ScalarWeightedState S) (u : ScalarHeightSpace S) :
    ScalarHeightSpace S :=
  scalarReferenceWDerivCLM hD hT hS
      (scalarHeightUnitalAct hT hS (scalarStateMeanCLM hD hT hS x) u) +
    scalarReferenceWCLM hD hT hS
      (scalarHeightMul hT hS (scalarStateMeanDerivCLM hD hT hS x) u)

def scalarStateConnectionFactor (x : ScalarWeightedState S) : ScalarHeightSpace S :=
  scalarHeightUnitalMul hT hS (scalarStateAngularPower hD hT hS (-1) x)
    (scalarStateDPower hD hT hS (-(1 / 2) : ℝ) x)

def scalarJetCoframeRadialHeight (x : ScalarWeightedState S) : ScalarHeightSpace S :=
  scalarHeightUnitalMul hT hS (scalarStateDPower hD hT hS (1 / 2 : ℝ) x)
    (scalarStateAngularPower hD hT hS (-(1 / 2) : ℝ) x)

def scalarJetCoframeMixedPrimitive (x : ScalarWeightedState S) : ScalarHeightSpace S :=
  -(scalarHeightOddUnitalAct hT hS (scalarStateAngularPower hD hT hS (-(1 / 2) : ℝ) x)
    (scalarStateSlopeOddAct hD hT hS x (scalarStateAngularPrimitive hD hT hS x)))

def scalarJetCoframeAngularHeight (x : ScalarWeightedState S) : ScalarHeightSpace S :=
  scalarReferenceRadiusCLM hD hT hS (scalarStateAngularPower hD hT hS (1 / 2 : ℝ) x)

def scalarJetConnectionRadialPrimitive (x : ScalarWeightedState S) : ScalarHeightSpace S :=
  scalarHeightOddUnitalAct hT hS (scalarStateConnectionFactor hD hT hS x)
    (scalarStateSlopeOddAct hD hT hS x (scalarStateMixedPrimitive hD hT hS x))

def scalarJetConnectionAngularHeight (x : ScalarWeightedState S) : ScalarHeightSpace S :=
  scalarStateDPower hD hT hS (-(1 / 2) : ℝ) x +
    scalarHeightUnitalAct hT hS (scalarStateConnectionFactor hD hT hS x)
      (scalarStateSlopeAct hD hT hS x (scalarStateAngularHeight hD hT hS x))

def scalarCandidateJets (x : ScalarWeightedState S) : ScalarFieldOutputs S 7 :=
  ![(scalarStateRadialHeight hD hT hS x, 0),
    (0, scalarStateAngularPrimitive hD hT hS x),
    (scalarJetCoframeRadialHeight hD hT hS x, 0),
    (0, scalarJetCoframeMixedPrimitive hD hT hS x),
    (scalarJetCoframeAngularHeight hD hT hS x, 0),
    (0, scalarJetConnectionRadialPrimitive hD hT hS x),
    (scalarJetConnectionAngularHeight hD hT hS x, 0)]

def scalarStateMeanSquare (x : ScalarWeightedState S) : ScalarHeightSpace S :=
  scalarHeightUnitalMul hT hS (scalarStateMeanCLM hD hT hS x) (scalarStateMeanCLM hD hT hS x)

def scalarStateMeanFourth (x : ScalarWeightedState S) : ScalarHeightSpace S :=
  scalarHeightUnitalMul hT hS (scalarStateMeanSquare hD hT hS x) (scalarStateMeanSquare hD hT hS x)

def scalarStateSigma (x : ScalarWeightedState S) : ScalarHeightSpace S :=
  scalarHeightUnitalMul hT hS (scalarStateQPower hD hT hS (-1) x)
    (scalarStateDPower hD hT hS (-(1 / 2) : ℝ) x)

def scalarCoefficientAHeight (x : ScalarWeightedState S) : ScalarHeightSpace S :=
  scalarReferenceWCLM hD hT hS
    (scalarHeightUnitalMul hT hS
      (scalarHeightUnitalMul hT hS (scalarStateMeanCLM hD hT hS x)
        (scalarStateQuotientHeight hD hT hS x))
      (scalarStateDPower hD hT hS (-(3 / 2) : ℝ) x))

def scalarCoefficientBPrimitive (x : ScalarWeightedState S) : ScalarHeightSpace S :=
  -(scalarHeightOddUnitalAct hT hS (scalarStateDPower hD hT hS (-(3 / 2) : ℝ) x)
    (scalarStateEnergyOddAct hD hT hS x (scalarStateMixedPrimitive hD hT hS x)))

def scalarCoefficientQuadraticHeight (x : ScalarWeightedState S) : ScalarHeightSpace S :=
  let c2 := scalarHeightAngularMul hT hS (scalarStateMixedPrimitive hD hT hS x)
    (scalarStateMixedPrimitive hD hT hS x)
  scalarReferenceInvWCLM hD hT hS c2 +
    (2 : ℝ) • scalarReferenceWCLM hD hT hS
      (scalarHeightUnitalAct hT hS (scalarStateMeanSquare hD hT hS x) c2) +
    scalarReferenceWCLM hD hT hS (scalarReferenceWCLM hD hT hS
      (scalarReferenceWCLM hD hT hS
        (scalarHeightUnitalAct hT hS (scalarStateMeanFourth hD hT hS x) c2)))

def scalarCoefficientCHeight (x : ScalarWeightedState S) : ScalarHeightSpace S :=
  scalarReferenceInvRadiusCLM hD hT hS
      (scalarReferenceWDerivCLM hD hT hS
        (scalarHeightUnitalMul hT hS (scalarStateMeanCLM hD hT hS x) (scalarStateSigma hD hT hS x))) +
    scalarReferenceInvRadiusCLM hD hT hS
      (scalarReferenceWCLM hD hT hS
        (scalarHeightUnitalAct hT hS (scalarStateSigma hD hT hS x) (scalarStateMeanDerivCLM hD hT hS x))) +
    scalarHeightUnitalAct hT hS (scalarStateInverseMeanHeight hD hT hS x)
      (scalarHeightUnitalAct hT hS (scalarStateQPower hD hT hS (-1) x)
        (scalarHeightUnitalAct hT hS (scalarStateDPower hD hT hS (-(3 / 2) : ℝ) x)
          (scalarCoefficientQuadraticHeight hD hT hS x)))

def scalarCandidateCoefficients (x : ScalarWeightedState S) : ScalarFieldOutputs S 3 :=
  ![(scalarCoefficientAHeight hD hT hS x, 0),
    (0, scalarCoefficientBPrimitive hD hT hS x),
    (scalarCoefficientCHeight hD hT hS x, 0)]

/-- The decaying perturbation of w_ref times the type coefficient. Its
physical identity is required only in the open annulus. -/
def scalarTypePerturbationHeight (x : ScalarWeightedState S) : ScalarHeightSpace S :=
  let σ := scalarHeightUnitalMul hT hS (scalarStateInverseMeanHeight hD hT hS x)
    (scalarStateQPower hD hT hS (-1) x)
  scalarReferenceInvRadiusCLM hD hT hS
    (σ + scalarReferenceWCLM hD hT hS (scalarReferenceWCLM hD hT hS
      (scalarHeightUnitalMul hT hS (scalarStateMeanSquare hD hT hS x) σ)))

def scalarResidualNumeratorHeight (x : ScalarWeightedState S) : ScalarHeightSpace S :=
  let a := scalarStateRadialCLM hD hT hS x
  let b := scalarStateRadialSecondCLM hD hT hS x
  let c := scalarStateAngularPrimitiveCLM hD hT hS x
  let d := scalarStateAngularRadialPrimitiveCLM hD hT hS x
  let e := scalarStateAngularSecondCLM hD hT hS x
  scalarStateWDerivAct hD hT hS x (a + e) + scalarStateWAct hD hT hS x b +
    x.2 •
      (scalarHeightMul hT hS (a + scalarStateEnergyAct hD hT hS x e) b -
        scalarReferenceRadiusCLM hD hT hS
          (scalarStateEnergyAct hD hT hS x (scalarHeightAngularMul hT hS d d)) +
        scalarStateWAct hD hT hS x
          (scalarStateWDerivAct hD hT hS x
            (scalarHeightAngularMul hT hS c c - scalarHeightMul hT hS a e)))

def scalarCandidateResidual (x : ScalarWeightedState S) : ScalarHeightSpace S :=
  scalarHeightUnitalAct hT hS (scalarStateDPower hD hT hS (-(3 / 2) : ℝ) x)
    (scalarResidualNumeratorHeight hD hT hS x)

end ContinuousFlexibility.Statements
