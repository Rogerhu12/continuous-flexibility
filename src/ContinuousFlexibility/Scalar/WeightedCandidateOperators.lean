module

public import ContinuousFlexibility.Scalar.WeightedCandidateDecoding
public import ContinuousFlexibility.Scalar.WeightedScalarError

/-!
# Concrete operator and error candidates with exact physical decoders

The three coefficient heights determine the actual corrected operator on the
common height space. The normalized type perturbation determines the correction
error as a linear map in each of its two independent height arguments.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}

def scalarCandidateLinear
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (x : ScalarWeightedState S) :
    ScalarCommonHeight S →ₗ[ℝ] ScalarHeightSpace S :=
  (scalarCoefficientOperatorCLM hD hT hS
    (scalarCoefficientAHeight hD hT hS x)
    (scalarCoefficientBPrimitive hD hT hS x)
    (scalarCoefficientCHeight hD hT hS x)).toLinearMap

def scalarCandidateError
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (x : ScalarWeightedState S) :
    ScalarHeightSpace S →ₗ[ℝ] ScalarCommonHeight S →ₗ[ℝ] ScalarHeightSpace S :=
  scalarTypeErrorLinear hD hT hS (scalarTypePerturbationHeight hD hT hS x)

theorem decode_scalarCandidateLinear_fun
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (x : ScalarWeightedState S)
    (hb : ScalarCandidatePowerBounds hD hT hS x) (hg : ScalarStateGeometry D S x)
    (u : ScalarCommonHeight S) :
    (S.height scalarBeta).decode (scalarCandidateLinear hD hT hS x u) =
      scalarStateOperator D S x u := by
  exact decode_scalarCoefficientOperatorCLM_of_actual hD hT hS x
    (scalarCoefficientAHeight hD hT hS x)
    (scalarCoefficientBPrimitive hD hT hS x)
    (scalarCoefficientCHeight hD hT hS x)
    (decode_scalarCoefficientAHeight hD hT hS x hb hg)
    (angularPartial_decode_scalarCoefficientBPrimitive hD hT hS x hb hg)
    (decode_scalarCoefficientCHeight hD hT hS x hb hg) u

theorem decode_scalarCandidateLinear
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (x : ScalarWeightedState S)
    (hb : ScalarCandidatePowerBounds hD hT hS x) (hg : ScalarStateGeometry D S x)
    (u : ScalarCommonHeight S) (p : PolarPoint) :
    (S.height scalarBeta).decode (scalarCandidateLinear hD hT hS x u) p =
      scalarStateOperator D S x u p :=
  congrFun (decode_scalarCandidateLinear_fun hD hT hS x hb hg u) p

theorem decode_scalarCandidateError_fun
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (x : ScalarWeightedState S)
    (hb : ScalarCandidatePowerBounds hD hT hS x) (hg : ScalarStateGeometry D S x)
    (R : ScalarHeightSpace S) (u : ScalarCommonHeight S) :
    (S.height scalarBeta).decode (scalarCandidateError hD hT hS x R u) =
      scalarCorrectionError (scalarStateTypeB D S x) ((S.height scalarBeta).decode R)
        (scalarCommonHeightDecode S u) := by
  exact decode_scalarTypeErrorLinear_of_actual hD hT hS
    (scalarTypePerturbationHeight hD hT hS x) (scalarStateTypeB D S x)
    (fun _ hp => decode_scalarTypePerturbationHeight hD hT hS x hb hg hp) R u

theorem decode_scalarCandidateError
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (x : ScalarWeightedState S)
    (hb : ScalarCandidatePowerBounds hD hT hS x) (hg : ScalarStateGeometry D S x)
    (R : ScalarHeightSpace S) (u : ScalarCommonHeight S) (p : PolarPoint) :
    (S.height scalarBeta).decode (scalarCandidateError hD hT hS x R u) p =
      scalarCorrectionError (scalarStateTypeB D S x) ((S.height scalarBeta).decode R)
        (scalarCommonHeightDecode S u) p :=
  congrFun (decode_scalarCandidateError_fun hD hT hS x hb hg R u) p

end ContinuousFlexibility.Statements
