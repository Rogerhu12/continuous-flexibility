# N04b construction work

## Exact endpoint

The task remains `N04b : N04aStatement → N04bStatement`. The frozen statement and assembly are unchanged.

## Reused coordinate calculus

The first checkpoint reuses these complete modules verbatim from
`line/N04Coordinates`, commit
`fe5009423b9ffc766438b51d75377229b1fbc938` (PR #18):

- `src/ContinuousFlexibility/Scalar/SecondProduct.lean`
- `src/ContinuousFlexibility/Analysis/PrincipalCoefficientPullback.lean`
- `src/ContinuousFlexibility/Analysis/DivergenceConjugation.lean`
- `src/ContinuousFlexibility/Analysis/DivergenceFluxPullback.lean`
- `src/ContinuousFlexibility/Analysis/CoordinateDivergenceIdentity.lean`
- `src/ContinuousFlexibility/Analysis/BoundaryTaylorExtension.lean`
- `src/ContinuousFlexibility/Analysis/BoundaryMixedJets.lean`
- `src/ContinuousFlexibility/Analysis/FiniteRadialJets.lean`
- `src/ContinuousFlexibility/Analysis/PrincipalDensityBoundaryJets.lean`
- `src/ContinuousFlexibility/Analysis/CoordinateOperatorConstruction.lean`
- `src/ContinuousFlexibility/Analysis/CharacteristicPrincipalDensity.lean`
- `src/ContinuousFlexibility/Analysis/ScaledRadialPrincipalDensity.lean`
- `src/ContinuousFlexibility/Analysis/CharacteristicRootDensity.lean`
- `src/ContinuousFlexibility/Analysis/RadialAffineDensity.lean`

The modules contain actual product, flux-pullback, coordinate-divergence and principal-density proofs. In particular, `coordinateOperator_explicit_fields` derives the full transformed operator from the local inverse identity, actual smoothness and nonzero Jacobian. The characteristic-density theorems derive the diagonal wave density and root normalization from actual characteristic equations and differentials. They do not assume N04PartB.

This dependency closure is checked again by this branch's full CI. Copying a module is not evidence that the N04b endpoint is complete.

## Construction obligations

The positive-piece cubic clause is an interior identity; its quotient field can be constructed without a boundary estimate. Endpoint smoothness and all-order quantitative estimates are later obligations.

The main remaining construction is a legitimate choice of the cumulative data and canonical atlas, including the negative-piece charts and genuine cut transmission. The manuscript cuts at the level `σ = T/2`; the frozen physical pieces are fixed radial strips. A full-strip inverse by itself does not identify those two cuts. This is an issue to resolve, not a claimed counterexample to the existential endpoint.

No statement repair is asserted at this checkpoint.

## New proof interfaces

- `N04bPositiveDivision` constructs the actual interior divided coefficients and proves the exact positive-piece clause, preserving the other canonical data.
- `N04bCanonicalOperator` applies the coordinate calculus to the exact frozen canonical operator, from PartA and actual local physical-coefficient smoothness.
- `N04bCutPullback` proves one signed chain rule and the genuine first-derivative transmission matrix for a shared travel pullback with the reciprocal fourth-root gauge.

These are complete helper proofs. They do not assert the outstanding global atlas existence.

The first reuse checkpoint `8f742e1` passed [full CI run 43043096297](https://github.com/Rogerhu12/continuous-flexibility/actions/runs/43043096297): 5,226 jobs; 1,259 / 1,261 modules compiled; 26 / 42 blueprint statements proved and 16 open.
