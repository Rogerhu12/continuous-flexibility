module

public import ContinuousFlexibility.Scalar.WeightedConservation
public import ContinuousFlexibility.Scalar.WeightedSourceIntegral
public import ContinuousFlexibility.Scalar.WeightedResidualFormulas
public import ContinuousFlexibility.Scalar.WeightedTypeBound
public import ContinuousFlexibility.Scalar.WeightedGraphSeparation
public import ContinuousFlexibility.Scalar.WeightedGreen
public import ContinuousFlexibility.Scalar.WeightedLinearConservation
public import ContinuousFlexibility.Scalar.WeightedErrorConservation
public import ContinuousFlexibility.Scalar.WeightedStateDerivative

/-!
# Analytic consequences of the actual scalar realizations

Once the actual decoded maps and their uniform estimates have been
constructed, conservation of all derivatives, the height derivative
identity, maximality of the weak graph, and the endpoint Green statements
follow on the same chosen neighborhood. This module assembles those proved
consequences without adding fields to the frozen candidate data.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}

theorem weightedScalar_S04_of_residual
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (v₀ : ScalarHeightSpace S) (W : WeightedScalarData S)
    (hgeometry : ∀ x ∈ scalarStateBall S v₀ W.base W.epsilon, ScalarStateGeometry D S x)
    (hdecode : ∀ x ∈ scalarStateBall S v₀ W.base W.epsilon, ∀ p,
      (S.height scalarBeta).decode (W.residual x) p = scalarStateResidual D S x p)
    (htame : FixedNeighborhoodSmoothTame (scalarStateGrading S) (scalarHeightGrading S)
      (scalarStateBall S v₀ W.base W.epsilon) W.base W.loss W.residual) :
    IsWeightedS04 D S v₀ W := by
  obtain ⟨J, hJ⟩ := htame.2
  refine ⟨hdecode, htame.1, J, hJ, ?_, ?_, ?_⟩
  · exact scalarStateResidualTower_conservation hT hS J hdecode
      (fun x hx => (hgeometry x hx).physicalSourceIntegral_eq_zero hD hS)
  · intro k x hx directions h p
    exact scalarHeightTower_decode_derivative hS J k x hx directions h p
  · intro x hx hq p
    exact (hdecode x hx p).trans
      (scalarStateResidual_zero_parameter_eq_radialPDE hD hT hS x hq p)

/-- The operator estimates and the literal decoding identities supply the
remaining S05 clauses by the already proved physical conservation, graph
and Green identities. The candidate remains the frozen data structure. -/
theorem weightedScalar_S05_of_operators
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (v₀ : ScalarHeightSpace S) (W : WeightedScalarData S)
    (hbase : 4 ≤ W.base)
    (h03 : IsWeightedS03 D S v₀ W) (h04 : IsWeightedS04 D S v₀ W)
    (hcoeff : ∀ x ∈ scalarStateBall S v₀ W.base W.epsilon, ∀ i p,
      scalarFieldDecode S (W.coefficients x i) p = scalarCoefficientComponent D S x i p)
    (hctame : FixedNeighborhoodSmoothTame (scalarStateGrading S) (scalarOutputsGrading S 3)
      (scalarStateBall S v₀ W.base W.epsilon) W.base W.loss W.coefficients)
    (hlinear : ∀ x ∈ scalarStateBall S v₀ W.base W.epsilon, ∀ u p,
      (S.height scalarBeta).decode (W.linear x u) p = scalarStateOperator D S x u p)
    (herror : ∀ x ∈ scalarStateBall S v₀ W.base W.epsilon, ∀ R u p,
      (S.height scalarBeta).decode (W.error x R u) p =
        scalarCorrectionError (scalarStateTypeB D S x) ((S.height scalarBeta).decode R)
          (scalarCommonHeightDecode S u) p)
    (hltame : SmoothTameOn (pairGrading (scalarStateGrading S) (scalarCommonHeightGrading S))
      (scalarHeightGrading S) (scalarStateBall S v₀ W.base W.epsilon ×ˢ univ)
      (fun z : ScalarWeightedState S × ScalarCommonHeight S => W.linear z.1 z.2))
    (hetame : SmoothTameOn
      (pairGrading (pairGrading (scalarStateGrading S) (scalarHeightGrading S))
        (scalarCommonHeightGrading S)) (scalarHeightGrading S)
      ((scalarStateBall S v₀ W.base W.epsilon ×ˢ univ) ×ˢ univ)
      (fun z : (ScalarWeightedState S × ScalarHeightSpace S) × ScalarCommonHeight S =>
        W.error z.1.1 z.1.2 z.2))
    (hlbound : ∀ s : ℕ, W.base ≤ s → ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ scalarStateBall S v₀ W.base W.epsilon, ∀ u,
        scalarHeightGrading S s (W.linear x u) ≤ C *
          (scalarCommonHeightGrading S (s + W.loss) u +
            (1 + scalarStateGrading S (s + W.loss) x) *
              scalarCommonHeightGrading S W.base u))
    (hebound : ∀ s : ℕ, W.base ≤ s → ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ scalarStateBall S v₀ W.base W.epsilon, ∀ R u,
        scalarHeightGrading S s (W.error x R u) ≤ C *
          (scalarHeightGrading S (s + W.loss) R * scalarCommonHeightGrading S W.base u +
            scalarHeightGrading S W.base R * scalarCommonHeightGrading S (s + W.loss) u +
            (1 + scalarStateGrading S (s + W.loss) x) * scalarHeightGrading S W.base R *
              scalarCommonHeightGrading S W.base u)) :
    IsWeightedS05 D S v₀ W := by
  let U := scalarStateBall S v₀ W.base W.epsilon
  have hgeometry : ∀ x ∈ U, ScalarStateGeometry D S x := h03.2.2.2.2.1
  have hregular : ∀ x ∈ U, ∀ coefficient ∈
      ({scalarStateA D S x, scalarStateB D S x, scalarStateCorrectedC D S x} :
        Set (PolarPoint → ℝ)),
      ContDiff ℝ ∞ coefficient ∧ UniformFlatJets D coefficient :=
    fun x hx => scalarStateCoefficients_contDiff_and_flatJets_of_decode
      hD hT hS x (W.coefficients x) (hcoeff x hx)
  have hsmooth : ∀ x ∈ U,
      ContDiff ℝ ∞ (scalarStateA D S x) ∧ ContDiff ℝ ∞ (scalarStateB D S x) ∧
        ContDiff ℝ ∞ (scalarStateCorrectedC D S x) := by
    intro x hx
    exact ⟨(hregular x hx _ (by simp)).1,
      (hregular x hx _ (by simp)).1, (hregular x hx _ (by simp)).1⟩
  obtain ⟨J, _, _, _, _⟩ := h04.2.2
  have hgreen := weightedScalar_green_clauses hD hT hS U W.coefficients hcoeff
  refine ⟨hcoeff, hctame, hregular,
    scalarStateTypeB_uniform_bound hD hT hS v₀ hbase h03.2.1.le hgeometry,
    hlinear, herror, hltame, hetame, hlbound, hebound, ?_, ?_, ?_, ?_, hgreen.1, hgreen.2⟩
  · exact weightedScalar_linear_conservation_clause hD hT hS W hcoeff hlinear
  · exact weightedScalar_error_conservation_clause hD hT hS W hgeometry herror
  · exact weightedScalar_stateDerivative_clause hD hT hS W J hgeometry h04.1 hlinear herror
  · exact weightedScalar_weakGraph_clause hD hT hS W U hsmooth hlinear hltame

/-- One S05 witness at every datum supplies all three frozen weighted
milestones, retaining the same maps whenever the smaller interface is used. -/
theorem scalarWeighted_of_S05 (h05 : S05WeightedStatement) :
    S03WeightedStatement ∧ S04WeightedStatement ∧ S05WeightedStatement := by
  refine ⟨?_, ?_, h05⟩
  · intro D T S hD hT hS v₀
    obtain ⟨W, h03, _, _⟩ := h05 D T S hD hT hS v₀
    exact ⟨W, h03⟩
  · intro D T S hD hT hS v₀
    obtain ⟨W, h03, h04, _⟩ := h05 D T S hD hT hS v₀
    exact ⟨W, h03, h04⟩

end ContinuousFlexibility.Statements
