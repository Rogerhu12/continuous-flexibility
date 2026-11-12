import ContinuousFlexibility.Statements.Nonlinear

/-!
# Inputs for independent reference-geometry estimates

These exact primitive definitions are staged from the incoming N07a
interface so their consequences can be checked independently. They are
only explicit hypotheses of the new lemmas: the current N04, N03, and
Through04 outputs are unchanged, and no primitive witness is supplied.

When these declarations land in Statements.Nonlinear, remove this module
and its import from N05PrimitiveReferenceValues. At every compiled tree
each declaration has one definition; do not retain a second copy.
-/

noncomputable section

namespace ContinuousFlexibility.Statements.CanonicalGeometry

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

def unitStrip : Set PolarPoint := Ioo (0 : ℝ) 1 ×ˢ univ

def physicalUnitPoint {S : PhysicalSpacesData} (K : CanonicalData S)
    (m : ℕ) (p : PolarPoint) : PolarPoint :=
  (K.physicalLeft m + (K.physicalRight m - K.physicalLeft m) * p.1, p.2)

def canonicalUnitPoint {S : PhysicalSpacesData} (K : CanonicalData S)
    (m : ℕ) (p : PolarPoint) : PolarPoint :=
  (K.left m + (K.right m - K.left m) * p.1, p.2)

/-- Angular coordinates occur as defects from the identity, since the
unwrapped angular coordinate itself is unbounded. All radial variables in
this list are evaluated on a unit interval. -/
inductive Atom
  | chartRadial | chartAngleDefect | inverseRadial | inverseAngleDefect
  | height | heightInverse | jacobian | jacobianInverse
  | sourceFactor | sourceFactorInverse
  | principalA | principalAInverse | principalB | principalC | potential
  | dividedA | dividedB | dividedC
  | leftColumn | nuColumn | auxiliaryColumn
  | physicalLength | physicalLengthInverse | canonicalLength | canonicalLengthInverse
  | materialEll | materialEllInverse
  | ratioH | ratioHInverse | ratioM | ratioMInverse | ratioE0 | ratioE0Inverse
  deriving DecidableEq

/-- The actual scalar functions whose jets are estimated. No new candidate
coefficients or geometric representatives are introduced. -/
def atom (D : ReferenceData) (T : MaterialData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (L : ReturnCorrectionData S) (K : CanonicalData S)
    (z : AnnularState S × ℝ) (m : ℕ) (a : Atom) (p : PolarPoint) : ℝ :=
  let x := physicalUnitPoint K m p
  let y := canonicalUnitPoint K m p
  let rₘ := T.sample (K.cell m)
  let J := |planeJacobian (K.chart z m) x|
  match a with
  | .chartRadial => ((K.chart z m x).1 - K.left m) / (K.right m - K.left m)
  | .chartAngleDefect => (K.chart z m x).2 - x.2
  | .inverseRadial => ((K.inverseChart z m y).1 - K.physicalLeft m) /
      (K.physicalRight m - K.physicalLeft m)
  | .inverseAngleDefect => (K.inverseChart z m y).2 - y.2
  | .height => K.height z m x
  | .heightInverse => (K.height z m x)⁻¹
  | .jacobian => J
  | .jacobianInverse => J⁻¹
  | .sourceFactor => canonicalSource S K z m (fun _ => 1) y
  | .sourceFactorInverse => (canonicalSource S K z m (fun _ => 1) y)⁻¹
  | .principalA => (K.coefficients z m).a y
  | .principalAInverse => ((K.coefficients z m).a y)⁻¹
  | .principalB => (K.coefficients z m).b y
  | .principalC => (K.coefficients z m).c y
  | .potential => K.potential z m y
  | .dividedA => if K.positive m then (K.dividedDifference z m).a y else 0
  | .dividedB => if K.positive m then (K.dividedDifference z m).b y else 0
  | .dividedC => if K.positive m then (K.dividedDifference z m).c y else 0
  | .leftColumn => canonicalSource S K z m
      (divergenceOperator (L.coefficients z) (fun q => S.chiLeft q.1)) y
  | .nuColumn => canonicalSource S K z m (nuColumnField D S C z) y
  | .auxiliaryColumn => canonicalSource S K z m
      ((S.height (3 / 4 : ℝ)).decode S.psi) y
  | .physicalLength => K.physicalRight m - K.physicalLeft m
  | .physicalLengthInverse => (K.physicalRight m - K.physicalLeft m)⁻¹
  | .canonicalLength => K.right m - K.left m
  | .canonicalLengthInverse => (K.right m - K.left m)⁻¹
  | .materialEll => T.ell x.1
  | .materialEllInverse => (T.ell x.1)⁻¹
  | .ratioH => T.H x.1 / T.H rₘ
  | .ratioHInverse => T.H rₘ / T.H x.1
  | .ratioM => T.M x.1 / T.M rₘ
  | .ratioMInverse => T.M rₘ / T.M x.1
  | .ratioE0 => T.E0 x.1 / T.E0 rₘ
  | .ratioE0Inverse => T.E0 rₘ / T.E0 x.1

/-- Actual reference coordinates preserve the angle, and the actual height
factor is radial. These assertions are stronger than reflection and period
equivariance, and are explicitly proved for the construction in the paper. -/
def ReferenceRadial (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (K : CanonicalData S) : Prop :=
  (∀ m p, p ∈ referencePhysicalPieceOpen S K m →
    K.chart (C.referenceState, 0) m p =
      ((K.chart (C.referenceState, 0) m (p.1, 0)).1, p.2) ∧
    K.height (C.referenceState, 0) m p =
      K.height (C.referenceState, 0) m (p.1, 0)) ∧
  (∀ m p, p ∈ canonicalOpen S K m →
    K.inverseChart (C.referenceState, 0) m p =
      ((K.inverseChart (C.referenceState, 0) m (p.1, 0)).1, p.2))

def ReferenceJets (D : ReferenceData) (T : MaterialData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (L : ReturnCorrectionData S) (K : CanonicalData S) : Prop :=
  (∀ m a, ContDiffOn ℝ ∞ (atom D T S C L K (C.referenceState, 0) m a) unitStrip ∧
    ∀ p ∈ unitStrip, atom D T S C L K (C.referenceState, 0) m a (p + (0, Real.pi)) =
      atom D T S C L K (C.referenceState, 0) m a p) ∧
  ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ m a p, p ∈ unitStrip →
    ∀ i j : ℕ, i + j ≤ s →
      |mixedDerivative i j (atom D T S C L K (C.referenceState, 0) m a) p| ≤
        B * T.E0 (T.sample (K.cell m)) ^ B

end ContinuousFlexibility.Statements.CanonicalGeometry
