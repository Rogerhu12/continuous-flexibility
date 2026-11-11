import ContinuousFlexibility.Statements.Scalar
import ContinuousFlexibility.Statements.Analysis

/-!
# Weighted scalar milestone targets

The finite-annulus calculus in `Scalar` is a separate subtarget. This module
adds actual decoded weighted maps, one common low-order neighborhood, genuine
directional towers and fixed-loss estimates, flat endpoints, and a distribution
graph on the same smooth weighted height domain.

There is deliberately no claim that arbitrary radial perturbations preserve a
fixed Banach transmission domain: that belongs to the later return-corrected
nonlinear construction. The coefficient B=E/(rQ) is not extended across a flat
endpoint. Only its actual weighted products are required to extend.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology BigOperators ENNReal

set_option backward.isDefEq.respectTransparency false

def scalarBeta : ℝ := 3 / 4

abbrev ScalarHeightSpace (S : PhysicalSpacesData) := (S.height scalarBeta).Space

def scalarHeightGrading (S : PhysicalSpacesData) : ℕ → Seminorm ℝ (ScalarHeightSpace S) :=
  (S.height scalarBeta).grading

/-- The right endpoint is normalized to zero; the left constant is free. -/
abbrev ScalarCommonHeight (S : PhysicalSpacesData) := ScalarHeightSpace S × ℝ

def scalarCommonHeightGrading (S : PhysicalSpacesData) :
    ℕ → Seminorm ℝ (ScalarCommonHeight S) :=
  pairGrading (scalarHeightGrading S) realGrading

def scalarCommonHeightDecode (S : PhysicalSpacesData) (u : ScalarCommonHeight S)
    (p : PolarPoint) : ℝ :=
  (S.height scalarBeta).decode u.1 p + u.2 * S.chiLeft p.1

/-- State coordinates are ((profile perturbation, height),left constant),q. -/
abbrev ScalarWeightedState (S : PhysicalSpacesData) :=
  ((ScalarHeightSpace S × ScalarHeightSpace S) × ℝ) × ℝ

def scalarStateGrading (S : PhysicalSpacesData) :
    ℕ → Seminorm ℝ (ScalarWeightedState S) :=
  pairGrading
    (pairGrading (pairGrading (scalarHeightGrading S) (scalarHeightGrading S)) realGrading)
    realGrading

def scalarStateCenter (S : PhysicalSpacesData) (v₀ : ScalarHeightSpace S) :
    ScalarWeightedState S := (((0, v₀), 0), 0)

def scalarStateBall (S : PhysicalSpacesData) (v₀ : ScalarHeightSpace S)
    (base : ℕ) (ε : ℝ) : Set (ScalarWeightedState S) :=
  {x | scalarStateGrading S base (x - scalarStateCenter S v₀) < ε}

def scalarStateProfile (D : ReferenceData) (S : PhysicalSpacesData)
    (x : ScalarWeightedState S) (r : ℝ) : ℝ :=
  D.w r * (1 + angularMean (fun θ => (S.height scalarBeta).decode x.1.1.1 (r, θ)))

/-- A genuine radial primitive, with its normalization fixed at the left endpoint. -/
def scalarStatePrimitive (D : ReferenceData) (S : PhysicalSpacesData)
    (x : ScalarWeightedState S) (r : ℝ) : ℝ :=
  ∫ t in D.a..r, scalarStateProfile D S x t

def scalarStateIncrement (S : PhysicalSpacesData) (x : ScalarWeightedState S) :
    PolarPoint → ℝ :=
  scalarCommonHeightDecode S (x.1.1.2, x.1.2)

def scalarStateHeight (D : ReferenceData) (S : PhysicalSpacesData)
    (x : ScalarWeightedState S) : PolarPoint → ℝ :=
  heightFamily (Radial.radialHeightField (scalarStatePrimitive D S x))
    (scalarStateIncrement S x) x.2

def scalarStateResidual (D : ReferenceData) (S : PhysicalSpacesData)
    (x : ScalarWeightedState S) : PolarPoint → ℝ :=
  normalizedResidual (scalarStateProfile D S x) (scalarStatePrimitive D S x)
    (scalarStateIncrement S x) x.2

def scalarHeightDirection (S : PhysicalSpacesData) (u : ScalarCommonHeight S) :
    ScalarWeightedState S := (((0, u.1), u.2), 0)

/-- The physical space is even. Odd coefficients are represented by the
angular derivative of an even primitive, rather than incorrectly declared even. -/
abbrev ScalarFieldSpace (S : PhysicalSpacesData) := ScalarHeightSpace S × ScalarHeightSpace S

def scalarFieldDecode (S : PhysicalSpacesData) (u : ScalarFieldSpace S)
    (p : PolarPoint) : ℝ :=
  (S.height scalarBeta).decode u.1 p +
    angularPartial ((S.height scalarBeta).decode u.2) p

def scalarFieldGrading (S : PhysicalSpacesData) : ℕ → Seminorm ℝ (ScalarFieldSpace S) :=
  pairGrading (scalarHeightGrading S) (scalarHeightGrading S)

abbrev ScalarFieldOutputs (S : PhysicalSpacesData) (n : ℕ) := Fin n → ScalarFieldSpace S

def scalarOutputsGrading (S : PhysicalSpacesData) (n : ℕ) :
    ℕ → Seminorm ℝ (ScalarFieldOutputs S n) :=
  fun s => ∑ i : Fin n, (scalarFieldGrading S s).comp (LinearMap.proj i)

/-- Seven actual decaying jet/coframe/connection components. The subtracted
background is (w,0,1,0,r,0,1), not an arbitrary reference section. -/
def scalarJetComponent (D : ReferenceData) (S : PhysicalSpacesData)
    (x : ScalarWeightedState S) (i : Fin 7) (p : PolarPoint) : ℝ :=
  let w := scalarStateProfile D S x
  let z := scalarStateHeight D S x
  match i.val with
  | 0 => heightRadial z p - w p.1
  | 1 => heightAngular z p
  | 2 => (heightCoframeOne w z).radial p - 1
  | 3 => (heightCoframeTwo w z).radial p
  | 4 => (heightCoframeTwo w z).angular p - p.1
  | 5 => (heightConnectionForm w z).radial p
  | _ => (heightConnectionForm w z).angular p - 1

def scalarStateA (D : ReferenceData) (S : PhysicalSpacesData)
    (x : ScalarWeightedState S) : PolarPoint → ℝ :=
  polarLinearA (scalarStateProfile D S x) (scalarStateHeight D S x)

def scalarStateB (D : ReferenceData) (S : PhysicalSpacesData)
    (x : ScalarWeightedState S) : PolarPoint → ℝ :=
  polarLinearB (scalarStateProfile D S x) (scalarStateHeight D S x)

def scalarStateCorrectedC (D : ReferenceData) (S : PhysicalSpacesData)
    (x : ScalarWeightedState S) : PolarPoint → ℝ :=
  polarCorrectedC (scalarStateProfile D S x) (scalarStateHeight D S x)

def scalarStateTypeB (D : ReferenceData) (S : PhysicalSpacesData)
    (x : ScalarWeightedState S) : PolarPoint → ℝ :=
  polarTypeB (scalarStateProfile D S x) (scalarStateHeight D S x)

/-- Only the coefficient differences belong to the beta-decaying space:
the actual radial reference w and w'/r need not have that weight. -/
def scalarCoefficientComponent (D : ReferenceData) (S : PhysicalSpacesData)
    (x : ScalarWeightedState S) (i : Fin 3) (p : PolarPoint) : ℝ :=
  match i.val with
  | 0 => scalarStateA D S x p - D.w p.1
  | 1 => scalarStateB D S x p
  | _ => scalarStateCorrectedC D S x p - deriv D.w p.1 / p.1

def scalarStateNormalFlux (D : ReferenceData) (S : PhysicalSpacesData)
    (x : ScalarWeightedState S) (u : ScalarCommonHeight S) : PolarPoint → ℝ :=
  symmetricNormalFlux (scalarStateA D S x) (scalarStateB D S x)
    (scalarCommonHeightDecode S u)

def scalarStateOperator (D : ReferenceData) (S : PhysicalSpacesData)
    (x : ScalarWeightedState S) (u : ScalarCommonHeight S) : PolarPoint → ℝ :=
  heightCorrectedDivergence (scalarStateProfile D S x) (scalarStateHeight D S x)
    (scalarCommonHeightDecode S u)

/-- Pure candidate output data; none of the asserted analytic conclusions
is an unexplained Prop field or an assumed inverse. -/
structure WeightedScalarData (S : PhysicalSpacesData) where
  base : ℕ
  loss : ℕ
  epsilon : ℝ
  jets : ScalarWeightedState S → ScalarFieldOutputs S 7
  residual : ScalarWeightedState S → ScalarHeightSpace S
  coefficients : ScalarWeightedState S → ScalarFieldOutputs S 3
  linear : ScalarWeightedState S → ScalarCommonHeight S →ₗ[ℝ] ScalarHeightSpace S
  error : ScalarWeightedState S → ScalarHeightSpace S →ₗ[ℝ]
    ScalarCommonHeight S →ₗ[ℝ] ScalarHeightSpace S

section UniformEstimates

variable {E F : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]

/-- One base and one loss, chosen before all output orders. Every directional
derivative is a genuine continuous multilinear map from `SmoothDirections`. -/
def UniformScalarTowerEstimate (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ F)
    (U : Set E) (base loss : ℕ) (f : E → F) (J : SmoothDirections U f) : Prop :=
  ∀ k s : ℕ, base ≤ s → ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ U, ∀ v : Fin k → E,
    q s (J.D k x v) ≤ C *
      ((1 + p (s + loss) x) * ∏ i, p base (v i) +
        ∑ i : Fin k, p (s + loss) (v i) * ∏ j ∈ Finset.univ.erase i, p base (v j))

def FixedNeighborhoodSmoothTame (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ F)
    (U : Set E) (base loss : ℕ) (f : E → F) : Prop :=
  SmoothTameOn p q U f ∧
    ∃ J : SmoothDirections U f, UniformScalarTowerEstimate p q U base loss f J

end UniformEstimates

/-- All positivity is required only in the open physical annulus. In particular,
Q is allowed to vanish at its actual flat endpoints. -/
def ScalarStateGeometry (D : ReferenceData) (S : PhysicalSpacesData)
    (x : ScalarWeightedState S) : Prop :=
  ContDiff ℝ ∞ (scalarStateProfile D S x) ∧
  ContDiff ℝ ∞ (scalarStatePrimitive D S x) ∧
  ContDiff ℝ ∞ (scalarStateIncrement S x) ∧
  (∀ r, HasDerivAt (scalarStatePrimitive D S x) (scalarStateProfile D S x r) r) ∧
  (∀ r, r ≤ D.a ∨ D.b ≤ r → scalarStateProfile D S x r = 0) ∧
  UniformFlatJets D (fun p => scalarStateProfile D S x p.1) ∧
  UniformFlatJets D ((S.height scalarBeta).decode x.1.1.2) ∧
  (∀ r, r ≤ D.a → ∀ θ, scalarStateHeight D S x (r, θ) = x.2 * x.1.2) ∧
  (∀ r, D.b ≤ r → ∀ θ,
    scalarStateHeight D S x (r, θ) = scalarStatePrimitive D S x D.b) ∧
  ∀ r ∈ Ioo D.a D.b, 0 < scalarStateProfile D S x r ∧ ∀ θ,
    (1 / 2 : ℝ) ≤ polarDiscriminant (scalarStateProfile D S x)
      (scalarStateHeight D S x) (r, θ) ∧
    (7 / 8 : ℝ) * scalarStateProfile D S x r ≤
      heightQ (profileEnergy (scalarStateProfile D S x) (r, θ))
        (heightRadial (scalarStateHeight D S x) (r, θ))
        (angularPartial (heightAngular (scalarStateHeight D S x)) (r, θ))

def IsWeightedS03 (D : ReferenceData) (S : PhysicalSpacesData)
    (v₀ : ScalarHeightSpace S) (W : WeightedScalarData S) : Prop :=
  let U := scalarStateBall S v₀ W.base W.epsilon
  0 < W.epsilon ∧ W.epsilon < 1 ∧ IsOpen U ∧ scalarStateCenter S v₀ ∈ U ∧
  (∀ x ∈ U, ScalarStateGeometry D S x) ∧
  (∀ x ∈ U, ∀ i p, scalarFieldDecode S (W.jets x i) p = scalarJetComponent D S x i p) ∧
  FixedNeighborhoodSmoothTame (scalarStateGrading S) (scalarOutputsGrading S 7)
    U W.base W.loss W.jets

/-- Actual source decoding, removable normalization, and all metric/height/q
directional compatibility on the same low-order neighborhood. -/
def IsWeightedS04 (D : ReferenceData) (S : PhysicalSpacesData)
    (v₀ : ScalarHeightSpace S) (W : WeightedScalarData S) : Prop :=
  let U := scalarStateBall S v₀ W.base W.epsilon
  (∀ x ∈ U, ∀ p,
    (S.height scalarBeta).decode (W.residual x) p = scalarStateResidual D S x p) ∧
  SmoothTameOn (scalarStateGrading S) (scalarHeightGrading S) U W.residual ∧
  ∃ J : SmoothDirections U W.residual,
    UniformScalarTowerEstimate (scalarStateGrading S) (scalarHeightGrading S)
      U W.base W.loss W.residual J ∧
    (∀ k x, x ∈ U → ∀ directions : Fin k → ScalarWeightedState S,
      S.Q (J.D k x directions) = 0 ∧
      ContDiff ℝ ∞ ((S.height scalarBeta).decode (J.D k x directions)) ∧
      UniformFlatJets D ((S.height scalarBeta).decode (J.D k x directions)) ∧
      physicalSourceIntegral D ((S.height scalarBeta).decode (J.D k x directions)) = 0) ∧
    (∀ k x, x ∈ U → ∀ directions : Fin k → ScalarWeightedState S,
      ∀ h : ScalarWeightedState S, ∀ p : PolarPoint,
        HasDerivAt
          (fun t : ℝ => (S.height scalarBeta).decode (J.D k (x + t • h) directions) p)
          ((S.height scalarBeta).decode (J.D (k + 1) x (Fin.cons h directions)) p) 0) ∧
    (∀ x ∈ U, x.2 = 0 → ∀ p,
      (S.height scalarBeta).decode (W.residual x) p =
        Radial.radialPDE (scalarStateProfile D S x)
          (fun r θ => scalarStateIncrement S x (r, θ)) p.1 p.2)

/-! ## The real distribution graph on one common smooth height domain -/

def IsPhysicalScalarTest (D : ReferenceData) (φ : PolarPoint → ℝ) : Prop :=
  ContDiff ℝ ∞ φ ∧ Function.Periodic φ (0, Real.pi) ∧ HasCompactRadialSupport D φ

def scalarAnnularIntegral (D : ReferenceData) (f : PolarPoint → ℝ) : ℝ :=
  ∫ r in D.a..D.b, ∫ θ in (0 : ℝ)..Real.pi, f (r, θ)

/-- The graph is literally the weak divergence equation against smooth
periodic compact-interior tests, with the physical dr dθ pairing. -/
def PhysicalScalarWeakGraph (D : ReferenceData) (S : PhysicalSpacesData)
    (x : ScalarWeightedState S) : Set (ScalarCommonHeight S × ScalarHeightSpace S) :=
  {z | ∀ φ : PolarPoint → ℝ, IsPhysicalScalarTest D φ →
    scalarAnnularIntegral D (fun p => (S.height scalarBeta).decode z.2 p * φ p) =
      -scalarAnnularIntegral D (fun p =>
        (scalarStateA D S x p * radialPartial (scalarCommonHeightDecode S z.1) p +
          scalarStateB D S x p * angularPartial (scalarCommonHeightDecode S z.1) p) *
            radialPartial φ p +
        (scalarStateB D S x p * radialPartial (scalarCommonHeightDecode S z.1) p +
          scalarStateCorrectedC D S x p * angularPartial (scalarCommonHeightDecode S z.1) p) *
            angularPartial φ p)}

def ScalarGreenIntegrand (D : ReferenceData) (S : PhysicalSpacesData)
    (x : ScalarWeightedState S) (u v : ScalarCommonHeight S) (p : PolarPoint) : ℝ :=
  scalarCommonHeightDecode S u p * scalarStateOperator D S x v p -
    scalarCommonHeightDecode S v p * scalarStateOperator D S x u p

/-- The coefficients and error are genuine physical expressions; B alone
is not asserted to extend across the flat ends. -/
def IsWeightedS05 (D : ReferenceData) (S : PhysicalSpacesData)
    (v₀ : ScalarHeightSpace S) (W : WeightedScalarData S) : Prop :=
  let U := scalarStateBall S v₀ W.base W.epsilon
  (∀ x ∈ U, ∀ i p,
    scalarFieldDecode S (W.coefficients x i) p = scalarCoefficientComponent D S x i p) ∧
  FixedNeighborhoodSmoothTame (scalarStateGrading S) (scalarOutputsGrading S 3)
    U W.base W.loss W.coefficients ∧
  (∀ x ∈ U, ∀ coefficient ∈
      ({scalarStateA D S x, scalarStateB D S x, scalarStateCorrectedC D S x} :
        Set (PolarPoint → ℝ)),
    ContDiff ℝ ∞ coefficient ∧ UniformFlatJets D coefficient) ∧
  (∃ C : ℝ, 0 < C ∧ ∀ x ∈ U, ∀ r ∈ Ioo D.a D.b, ∀ θ,
    |scalarStateProfile D S x r * scalarStateTypeB D S x (r, θ)| ≤ C) ∧
  (∀ x ∈ U, ∀ u p,
    (S.height scalarBeta).decode (W.linear x u) p = scalarStateOperator D S x u p) ∧
  (∀ x ∈ U, ∀ R u p,
    (S.height scalarBeta).decode (W.error x R u) p =
      scalarCorrectionError (scalarStateTypeB D S x) ((S.height scalarBeta).decode R)
        (scalarCommonHeightDecode S u) p) ∧
  SmoothTameOn (pairGrading (scalarStateGrading S) (scalarCommonHeightGrading S))
    (scalarHeightGrading S) (U ×ˢ univ)
    (fun z : ScalarWeightedState S × ScalarCommonHeight S => W.linear z.1 z.2) ∧
  SmoothTameOn
    (pairGrading (pairGrading (scalarStateGrading S) (scalarHeightGrading S))
      (scalarCommonHeightGrading S)) (scalarHeightGrading S) ((U ×ˢ univ) ×ˢ univ)
    (fun z : (ScalarWeightedState S × ScalarHeightSpace S) × ScalarCommonHeight S =>
      W.error z.1.1 z.1.2 z.2) ∧
  (∀ s : ℕ, W.base ≤ s → ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ U, ∀ u,
    scalarHeightGrading S s (W.linear x u) ≤ C *
      (scalarCommonHeightGrading S (s + W.loss) u +
        (1 + scalarStateGrading S (s + W.loss) x) * scalarCommonHeightGrading S W.base u)) ∧
  (∀ s : ℕ, W.base ≤ s → ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ U, ∀ R u,
    scalarHeightGrading S s (W.error x R u) ≤ C *
      (scalarHeightGrading S (s + W.loss) R * scalarCommonHeightGrading S W.base u +
        scalarHeightGrading S W.base R * scalarCommonHeightGrading S (s + W.loss) u +
        (1 + scalarStateGrading S (s + W.loss) x) * scalarHeightGrading S W.base R *
          scalarCommonHeightGrading S W.base u)) ∧
  (∀ x ∈ U, ∀ u, S.Q (W.linear x u) = 0) ∧
  (∀ x ∈ U, ∀ R u, S.Q (W.error x R u) = 0) ∧
  (∀ x ∈ U, ∀ u,
    ContinuousFlexibility.Analysis.HasProjectiveLineDerivAt W.residual
      (W.linear x u + x.2 • W.error x (W.residual x) u) x (scalarHeightDirection S u)) ∧
  (∀ x ∈ U, IsClosed (PhysicalScalarWeakGraph D S x) ∧
    (∀ u, ∃ f, (u, f) ∈ PhysicalScalarWeakGraph D S x) ∧
    ∀ u f, (u, f) ∈ PhysicalScalarWeakGraph D S x ↔ f = W.linear x u) ∧
  (∀ x ∈ U, ∀ u,
    UniformFlatJets D (scalarStateNormalFlux D S x u) ∧
    (∀ θ, scalarStateNormalFlux D S x u (D.a, θ) = 0 ∧
      scalarStateNormalFlux D S x u (D.b, θ) = 0) ∧
    (∀ θ, Tendsto (fun r => scalarStateNormalFlux D S x u (r, θ))
      (𝓝[>] D.a) (𝓝 0) ∧
      Tendsto (fun r => scalarStateNormalFlux D S x u (r, θ)) (𝓝[<] D.b) (𝓝 0))) ∧
  (∀ x ∈ U, ∀ u v,
    IntervalIntegrable (fun r => ∫ θ in (0 : ℝ)..Real.pi,
      ScalarGreenIntegrand D S x u v (r, θ)) volume D.a D.b ∧
    scalarAnnularIntegral D (ScalarGreenIntegrand D S x u v) = 0)

/-- The full S03 target includes a real weighted smooth-tame realization. -/
def S03WeightedStatement : Prop := ∀ D T S,
  IsAccumulatingProfile D → IsMaterialData D T → IsPhysicalSpaces D T S →
  ∀ v₀ : ScalarHeightSpace S, ∃ W : WeightedScalarData S, IsWeightedS03 D S v₀ W

/-- S04 uses the same decoded state data and the same low-order neighborhood
for every height, metric, and independent q-directional derivative. -/
def S04WeightedStatement : Prop := ∀ D T S,
  IsAccumulatingProfile D → IsMaterialData D T → IsPhysicalSpaces D T S →
  ∀ v₀ : ScalarHeightSpace S, ∃ W : WeightedScalarData S,
    IsWeightedS03 D S v₀ W ∧ IsWeightedS04 D S v₀ W

/-- One final witness carries all scalar interfaces. The graph here is the
maximal weak graph relative to the common smooth weighted domain, not an
unproved fixed Banach transmission domain for arbitrary moving roots. -/
def S05WeightedStatement : Prop := ∀ D T S,
  IsAccumulatingProfile D → IsMaterialData D T → IsPhysicalSpaces D T S →
  ∀ v₀ : ScalarHeightSpace S, ∃ W : WeightedScalarData S,
    IsWeightedS03 D S v₀ W ∧ IsWeightedS04 D S v₀ W ∧ IsWeightedS05 D S v₀ W

/-- S03, complete original scalar-calculus and weighted-interface target. -/
def S03Statement : Prop := S03CalculusStatement ∧ S03WeightedStatement

/-- S04, including actual weighted endpoint and all-direction compatibility. -/
def S04Statement : Prop := S04CalculusStatement ∧ S04WeightedStatement

/-- S05, including flat-endpoint Green on the actual common smooth domain. -/
def S05Statement : Prop := S05CalculusStatement ∧ S05WeightedStatement

abbrev S03FullStatement : Prop := S03Statement
abbrev S04FullStatement : Prop := S04Statement
abbrev S05FullStatement : Prop := S05Statement

end ContinuousFlexibility.Statements
