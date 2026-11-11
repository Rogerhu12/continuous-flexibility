import ContinuousFlexibility.Statements.Nonlinear

/-!
# Primitive canonical geometry for the higher inverse estimates

These definitions retain actual coordinates, heights, transformed
coefficients and scalar columns, with genuine spatial and state jets.
They contain no inverse, commutator, regularity conclusion, or grading
equivalence. The coordinate construction must prove these primitive
bounds before they can supply the corresponding analytic estimates.

Sources: readable manuscript §7, uniform physical geometry, reference
regularized charts, geometric weight conversion and current geometric
jets; §8, the auxiliary compatibility source.
-/

noncomputable section

namespace ContinuousFlexibility.Statements.CanonicalGeometry

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

abbrev Parameter (S : PhysicalSpacesData) := StateDirections S × ℝ

def parameterGrading (S : PhysicalSpacesData) : ℕ → Seminorm ℝ (Parameter S) :=
  pairGrading (sectorGrading S) realGrading

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
  (∀ m p, p ∈ physicalPieceOpen S K m →
    K.chart (C.referenceState, 0) m p =
      ((K.chart (C.referenceState, 0) m (p.1, 0)).1, p.2) ∧
    K.height (C.referenceState, 0) m p =
      K.height (C.referenceState, 0) m (p.1, 0)) ∧
  (∀ m p, p ∈ canonicalOpen S K m →
    K.inverseChart (C.referenceState, 0) m p =
      ((K.inverseChart (C.referenceState, 0) m (p.1, 0)).1, p.2))

/-- Primitive reference positivity and the linear endpoint degeneracy on
positive pieces. Radiality of the coefficients can instead be derived from
`ReferenceRadial` and the existing exact operator identity; it is stated
here to make the construction-stage obligation explicit and reviewable. -/
def ReferencePrincipal (T : MaterialData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (K : CanonicalData S) : Prop :=
  (∀ m p, p ∈ canonicalOpen S K m →
    let A := K.coefficients (C.referenceState, 0) m
    0 < A.a p ∧ A.b p = 0 ∧ A.a p = A.a (p.1, 0) ∧ A.c p = A.c (p.1, 0) ∧
      K.potential (C.referenceState, 0) m p =
        K.potential (C.referenceState, 0) m (p.1, 0)) ∧
  (∃ B : ℝ, 0 < B ∧ ∀ m, K.positive m = true → ∀ p ∈ canonicalOpen S K m,
    (B * T.E0 (T.sample (K.cell m)) ^ B)⁻¹ *
        ((p.1 - K.left m) * (K.right m - p.1)) ≤
      (K.coefficients (C.referenceState, 0) m).c p)

def ReferenceJets (D : ReferenceData) (T : MaterialData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (L : ReturnCorrectionData S) (K : CanonicalData S) : Prop :=
  (∀ m a, ContDiffOn ℝ ∞ (atom D T S C L K (C.referenceState, 0) m a) unitStrip ∧
    ∀ p ∈ unitStrip, atom D T S C L K (C.referenceState, 0) m a (p + (0, Real.pi)) =
      atom D T S C L K (C.referenceState, 0) m a p) ∧
  ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ m a p, p ∈ unitStrip →
    ∀ i j : ℕ, i + j ≤ s →
      |mixedDerivative i j (atom D T S C L K (C.referenceState, 0) m a) p| ≤
        B * T.E0 (T.sample (K.cell m)) ^ B

abbrev JetField := Atom → ℕ → ℕ → ℕ → unitStrip → ℝ

/-- Spatial jets of the actual difference. A smooth directional tower for
this map differentiates actual spatial jets with respect to the state. -/
def differenceJets (D : ReferenceData) (T : MaterialData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (L : ReturnCorrectionData S) (K : CanonicalData S)
    (z : Parameter S) : JetField :=
  fun a m i j p => mixedDerivative i j
    (fun q => atom D T S C L K (liftSectorParameter S C z) m a q -
      atom D T S C L K (C.referenceState, 0) m a q) p.val

/-- The global-seminorm version of the paper's stronger localized bound.
The paper implies this by `g_{s,m} ≤ C_s n_s`. It is enough for N07a once
the N06 base inverse and N05 global reference estimates are already known. -/
def CurrentJets (D : ReferenceData) (T : MaterialData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (L : ReturnCorrectionData S) (K : CanonicalData S)
    (base : ℕ) (ε : ℝ) : Prop :=
  let U := sectorNeighborhood S base ε ε
  (∀ z ∈ U, ∀ m a, ContDiffOn ℝ ∞
    (atom D T S C L K (liftSectorParameter S C z) m a) unitStrip ∧
    ∀ p ∈ unitStrip,
      atom D T S C L K (liftSectorParameter S C z) m a (p + (0, Real.pi)) =
        atom D T S C L K (liftSectorParameter S C z) m a p) ∧
  (∃ loss : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ z ∈ U, ∀ m a (p : unitStrip),
    ∀ i j : ℕ, i + j ≤ s →
      |differenceJets D T S C L K z a m i j p| ≤
        B * T.E0 (T.sample (K.cell m)) ^ B *
          T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ) * parameterGrading S (s + loss) z) ∧
  ∃ J : SmoothDirections U (differenceJets D T S C L K),
    ∀ k : ℕ, ∃ loss : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ z ∈ U, ∀ v : Fin k → Parameter S, ∀ m a (p : unitStrip),
        ∀ i j : ℕ, i + j ≤ s →
          |J.D k z v a m i j p| ≤
            B * T.E0 (T.sample (K.cell m)) ^ B *
              T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ) *
              ((1 + parameterGrading S (s + loss) z) *
                  ∏ l, parameterGrading S base (v l) +
                ∑ l : Fin k, parameterGrading S (s + loss) (v l) *
                  ∏ h ∈ Finset.univ.erase l, parameterGrading S base (v h))

/-- The simple gauge chosen in §8: the compatibility source is radial and
is supported where current and reference coordinate/height data agree.
This is a condition on the actual chosen `S.psi`, not a new column. -/
def AuxiliaryColumnGauge (S : PhysicalSpacesData) (K : CanonicalData S) : Prop :=
  (∀ p : PolarPoint, (S.height (3 / 4 : ℝ)).decode S.psi p =
    (S.height (3 / 4 : ℝ)).decode S.psi (p.1, 0)) ∧
  (∀ p : PolarPoint, (S.height (3 / 4 : ℝ)).decode S.psi p ≠ 0 →
    p.1 ∈ K.normalizationRegion)

/-- Construction-stage geometric data for the manuscript's fixed gauge.
Every constituent concerns an actual geometric function or its derivatives.
The auxiliary-column condition records the radial, frozen source chosen
in the manuscript. -/
def PrimitiveGeometryProperties (D : ReferenceData) (T : MaterialData)
    (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (L : ReturnCorrectionData S) (K : CanonicalData S) (base : ℕ) (ε : ℝ) : Prop :=
  ReferenceRadial S C K ∧ ReferencePrincipal T S C K ∧
    ReferenceJets D T S C L K ∧ CurrentJets D T S C L K base ε ∧
      AuxiliaryColumnGauge S K

end ContinuousFlexibility.Statements.CanonicalGeometry
