module

public import ContinuousFlexibility.Analysis.N06NormalizerConstruction
public import ContinuousFlexibility.Analysis.N06FiniteSourceNormalization

/-!
# The reselected actual normalizer has no canonical source variation

The normalizer comes from the supported Through05 construction. N04
fixes the chart, height and actual Jacobian on this already existing
region. Thus its actual current and reference canonical sources agree,
and every mixed jet of their difference vanishes. No support condition
is required of the input normalizer.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency true

/-- The actual normalizing column is constant in the current canonical
coordinates, pointwise and at every mixed spatial derivative order. -/
def N06NormalizerSourceFixed (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (K : CanonicalData S) (base : ℕ) (ε : ℝ) : Prop :=
  ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 → ∀ m,
    (∀ p ∈ canonicalOpen S K m,
      canonicalSource S K z m ((S.height (3 / 4 : ℝ)).decode S.psi) p =
        canonicalSource S K (C.referenceState, 0) m ((S.height (3 / 4 : ℝ)).decode S.psi) p) ∧
    ∀ a b : ℕ, ∀ p ∈ canonicalOpen S K m,
      mixedDerivative a b (fun q =>
        canonicalSource S K z m ((S.height (3 / 4 : ℝ)).decode S.psi) q -
          canonicalSource S K (C.referenceState, 0) m
            ((S.height (3 / 4 : ℝ)).decode S.psi) q) p = 0

/- The cumulative arbitrary-normalizer transport is intentionally retired.
The shared primitive geometry constrains the actual chosen psi through its
auxiliary-column gauge and jets. Those facts are not preserved by an arbitrary
replacement. The original-K proof retains psi; the independent data and N05
graph transports in this module remain available. -/

end ContinuousFlexibility.Statements
