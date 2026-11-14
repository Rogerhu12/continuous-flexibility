module

public import ContinuousFlexibility.Analysis.N07aCurrentQualitativeRegularity
public import ContinuousFlexibility.Analysis.N07aScalarSourceTerminal

/-!
# The two equations retained by the actual reconstructed unknown

These abbreviations retain the original reference graph and the classical
canonical equation already proved for the smooth decoder. They record
provenance of that same unknown; neither contains physical regularity or
transmission conclusions.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

/-- Membership of the original reference weak graph, with its original
canonical representation and the explicit auxiliary scalar column. -/
def N07aReferenceGraphRepresentation
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (K : CanonicalData S) (U : CanonicalUnknown S K) : Prop :=
  ∃ γ M₀ M₁ : ℝ, ∃ Fref : CanonicalSequence S K, ∃ ηref fref : PolarPoint → ℝ,
    HasCanonicalRepresentation D S C K (C.referenceState, 0) U Fref ηref fref ∧
      ReferenceGraph D γ M₀ M₁ (ηref, U.2.2.1)
        ((fun p => fref p - U.2.2.2 * (S.height (3 / 4 : ℝ)).decode S.psi p), 0)

/-- The exact normal equation stored by the actual canonical solution data. -/
def N07aActualNormalEquation
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (L : ReturnCorrectionData S) (K : CanonicalData S)
    (z : CanonicalGeometry.Parameter S) (U : CanonicalUnknown S K)
    (f : S.Source) (v : ℕ → PolarPoint → ℝ) : Prop :=
  ∀ m, EqOn (mixedDerivative 2 0 (v m))
    (n07aNormalRhs
      (fun i => n07aNormalCoefficientFamily
        (fun k z m => n07aPrincipalField K (liftSectorParameter S C z) m k)
        (fun m => if K.positive m then -1 else 1) i z m)
      (v m)
      (n07aCanonicalSourceWithoutColumns D S C L K
        (fun _ _ => n07aUnknownScalar U) z f m))
    (canonicalOpen S K m)

end ContinuousFlexibility.Analysis
