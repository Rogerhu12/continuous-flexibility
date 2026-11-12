import ContinuousFlexibility.Analysis.N06CurrentScalarPairing
import ContinuousFlexibility.Analysis.N06FiniteReferenceColumns

/-!
# The actual finite jet input for the N06 relative operator

These definitions are extracted verbatim from the relative assembly. They
refer only to the existing coefficient and scalar-column fields, and carry
no inverse, geometry-reconstruction, or final operator estimate assumption.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis
open scoped ContDiff

set_option backward.isDefEq.respectTransparency true

/-- The actual current-minus-reference scalar source field, including the
coordinate change of the compatibility column. -/
def n06ActualCanonicalColumnDifference (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (L : ReturnCorrectionData S) (K : CanonicalData S)
    (z : AnnularState S × ℝ) (i : Fin 3) (m : ℕ) (p : PolarPoint) : ℝ :=
  canonicalSource S K z m (n06CurrentScalarField D S C L z i) p -
    canonicalSource S K (C.referenceState, 0) m (n06ReferenceScalarField D S i) p

/-- Only finite ordinary jets of the actual divided coefficients, actual
potential difference and actual three transformed columns occur here. -/
structure N06ActualRelativeJetBounds
    (D : ReferenceData) (T : MaterialData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (L : ReturnCorrectionData S) (K : CanonicalData S)
    (b : ℕ) (A : ℝ) (I : Finset ℕ) (δ : ℝ) (z : AnnularState S × ℝ) : Prop where
  cubic : ∀ m, K.positive m = true → ∀ a j, a + j ≤ b + 1 →
    ∀ p ∈ canonicalOpen S K m,
      |mixedDerivative a j (K.dividedDifference z m).a p| ≤
        δ * (T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ) *
          T.E0 (T.sample (K.cell m)) ^ A) ∧
      |mixedDerivative a j (K.dividedDifference z m).b p| ≤
        δ * (T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ) *
          T.E0 (T.sample (K.cell m)) ^ A) ∧
      |mixedDerivative a j (K.dividedDifference z m).c p| ≤
        δ * (T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ) *
          T.E0 (T.sample (K.cell m)) ^ A)
  potential : ∀ m j, j ≤ b → ∀ p ∈ canonicalOpen S K m,
    |mixedDerivative 0 j
      (fun q => K.potential z m q - K.potential (C.referenceState, 0) m q) p| ≤
      δ * T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ) *
        T.E0 (T.sample (K.cell m)) ^ A
  columns : ∀ i : Fin 3, ∀ m ∈ I, ∀ j, j ≤ b → ∀ p ∈ canonicalOpen S K m,
    |mixedDerivative 0 j (n06ActualCanonicalColumnDifference D S C L K z i m) p| ≤ δ


end ContinuousFlexibility.Statements
