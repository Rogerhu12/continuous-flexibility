module

public import ContinuousFlexibility.Statements.Nonlinear

/-!
# Actual existence and doubled-weight completion targets

These are proposition definitions, not proofs of N11, N12, or X02.
N11 constructs one common reference, material and function-space realization
instead of assuming that those realizations have instances. N12 is unconditional.
All strengthened branch assertions concern the very same weak branch.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators

abbrev StateParameter (S : PhysicalSpacesData) := AnnularState S × ℝ

def stateParameterGrading (S : PhysicalSpacesData) :
    ℕ → Seminorm ℝ (StateParameter S) := pairGrading (stateGrading S) realGrading

abbrev HeightAt (S : PhysicalSpacesData) (γ : ℝ) := (S.height γ).Space
abbrev CircleAt (S : PhysicalSpacesData) (γ : ℝ) := (S.circle γ).Space
abbrev ExtendedHeightAt (S : PhysicalSpacesData) (γ : ℝ) := HeightAt S γ × ℝ

def extendedHeightGrading (S : PhysicalSpacesData) (γ : ℝ) :
    ℕ → Seminorm ℝ (ExtendedHeightAt S γ) :=
  pairGrading (S.height γ).grading realGrading

def extendedHeightField (S : PhysicalSpacesData) (γ : ℝ)
    (u : ExtendedHeightAt S γ) (p : PolarPoint) : ℝ :=
  (S.height γ).decode u.1 p + u.2 * S.chiLeft p.1

structure WeakBranchData (S : PhysicalSpacesData) where
  radius : ℝ
  state : ℝ → AnnularState S

/-- The exact scalar and both return equations, normalization, genuine
parameter smoothness, and all-order estimates on one common interval. -/
def IsWeakBranch (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (R : ReturnEquationData S)
    (base : ℕ) (ε : ℝ) (B : WeakBranchData S) : Prop :=
  0 < B.radius ∧ B.state 0 = C.referenceState ∧
  SmoothTameOn realGrading (stateGrading S) (Ioo (-B.radius) B.radius) B.state ∧
  (∀ q : ℝ, |q| < B.radius →
    (B.state q, q) ∈ stateNeighborhood S C base ε ∧
    stateSector S (B.state q) ∧
    referenceRow D (stateU S (B.state q)) = 1 ∧
    (∀ p ∈ annularOpen D, scalarResidualField D S C (B.state q, q) p = 0) ∧
    R.residual (B.state q, q) = 0 ∧
    ∀ m θ,
      rightChartCandidate S C (B.state q, q) m
          (C.minusFlow (B.state q, q) m (C.right m) θ) =
        stateLeftChart S (B.state q) m θ - C.travel m ∧
      rightChartCandidate S C (B.state q, q) m
          (-C.minusFlow (B.state q, q) m (C.right m) (-θ)) =
        stateLeftChart S (B.state q) m θ + C.travel m) ∧
  (∀ s : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ q : ℝ, |q| < B.radius →
    stateGrading S s (B.state q - C.referenceState) ≤ K * |q|)

/-- N11: construct one common reference and instantiate all analysis objects;
no reference, function-space or nonlinear-inverse existence is a premise. Section 9,
lines 229--238. The parameter q is separate from the bending phase. -/
def N11Statement : Prop :=
  ∃ A : RadialReference,
    ∃ T : MaterialData, ∃ S : PhysicalSpacesData,
      IsMaterialData A.val T ∧ IsPhysicalSpaces A.val T S ∧
      ∃ C : NonlinearGeometryData S, ∃ R : ReturnEquationData S,
        ∃ base loss : ℕ, ∃ ε q0 : ℝ,
          N01Properties A.val T S C base loss ε ∧
          N02Properties A.val T S C R base ε ∧
          NonlinearStagesThrough10 A.val T S C R base loss ε q0 ∧
          ∃ B : WeakBranchData S, IsWeakBranch A.val S C R base ε B ∧ B.radius ≤ q0

/-- N12: the actual flat annular core exists, with no hypothetical input
core, reference, implicit-function theorem, or inverse. Section 10,
lines 250--317. The existing core fields enforce actual residual zero,
positive remainder, nonradiality and unequal permitted endpoint constants. -/
def N12Statement : Prop := Nonempty FlatAnnularCore

/-- Actual connection-period error with an independently varied height U. -/
def posteriorPeriod (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (x : AnnularState S)
    (U : PolarPoint → ℝ) (r : ℝ) : ℝ :=
  angularMean (fun θ =>
    (heightConnectionForm (stateProfile D S C x)
      (fun p => stateRadialHeight D S C x p.1 + U p)).angular (r, θ)) - 1

/-- A real two-parameter second derivative, not a named remainder
predicate. The metric is held at x and both height arguments vary. -/
def posteriorPeriodSecond (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (x : AnnularState S)
    (U η ξ : PolarPoint → ℝ) (r : ℝ) : ℝ :=
  deriv (fun s : ℝ => deriv (fun t : ℝ =>
    posteriorPeriod D S C x (fun p => U p + s * η p + t * ξ p) r) 0) 0

def posteriorPeriodTaylor (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (z : StateParameter S)
    (η ξ : HeightPair S) (p : PolarPoint) : ℝ :=
  (stateProfile D S C z.1 p.1)⁻¹ *
    ∫ t in (0 : ℝ)..1, (1 - t) *
      posteriorPeriodSecond D S C z.1
        (fun y => t * z.2 * stateU S z.1 y)
        (heightPairField S η) (heightPairField S ξ) p.1

/-! Circle Taylor expansion uses the raw height Z, not the pair (u,q).
Taking mixed q/u derivatives of e(qu,...) would create a one-factor linear
term and would incorrectly claim that term has doubled endpoint weight. -/

def rawNeighborhood (S : PhysicalSpacesData) (base : ℕ) (δ : ℝ) : Set (AnnularState S) :=
  {x | stateGrading S base x < δ}

def RawReturnConditions (D : ReferenceData) (S : PhysicalSpacesData)
    (C C₀ : NonlinearGeometryData S) (E : AnnularState S → CircleSpace S)
    (U : Set (AnnularState S)) : Prop :=
  C₀.control = C.control ∧ C₀.left = C.left ∧ C₀.right = C.right ∧
  C₀.travel = C.travel ∧
  (∀ x ∈ U, ∀ m θ,
    C₀.minusFlow (x, 1) m (C₀.left m) θ = θ ∧
    ContinuousOn (fun r => C₀.minusFlow (x, 1) m r θ) (Icc (C₀.left m) (C₀.right m)) ∧
    (∀ r ∈ Ioo (C₀.left m) (C₀.right m),
      HasDerivAt (fun t => C₀.minusFlow (x, 1) m t θ)
        (minusCharacteristicSpeed (originalCoefficients D S C₀ (x, 1))
          (r, C₀.minusFlow (x, 1) m r θ)) r) ∧
    (∀ r ∈ Icc (C₀.left m) (C₀.right m),
      0 < deriv (C₀.minusFlow (x, 1) m r) θ ∧
      C₀.minusFlow (x, 1) m r (θ + Real.pi) = C₀.minusFlow (x, 1) m r θ + Real.pi) ∧
    C₀.minusFlow (x, 1) m (C₀.right m) (C₀.minusReturnInverse (x, 1) m θ) = θ ∧
    C₀.minusReturnInverse (x, 1) m (C₀.minusFlow (x, 1) m (C₀.right m) θ) = θ ∧
    rightChartCandidate S C₀ (x, 1) m (C₀.rightChartInverse (x, 1) m θ) = θ ∧
    C₀.rightChartInverse (x, 1) m (rightChartCandidate S C₀ (x, 1) m θ) = θ ∧
    0 < deriv (rightChartCandidate S C₀ (x, 1) m) θ ∧
    (S.circle (3 / 4 : ℝ)).decode (E x) m θ = returnResidualField S C₀ (x, 1) m θ) ∧
  SmoothTameOn (stateGrading S) (S.circle (3 / 4 : ℝ)).grading U E

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1000000 in
def posteriorCircleTaylor (S : PhysicalSpacesData)
    (U : Set (AnnularState S)) (E : AnnularState S → CircleSpace S)
    (J : SmoothDirections U E) (z v w : AnnularState S)
    (m : ℕ) : ℝ :=
  ∫ t in (0 : ℝ)..1, (1 - t) * angularMean (fun θ =>
    (S.circle (3 / 4 : ℝ)).decode
      (J.D 2 (@SMul.smul ℝ (AnnularState S) inferInstance t z)
        (fun i : Fin 2 => if i = 0 then v else w)) m θ)

set_option maxHeartbeats 1000000 in
/-- The actual two Taylor remainders land in exponent 2 beta, with
genuine smooth tame dependence and continuous bilinearity in independent
arguments. Section 10, lines 19--174. -/
def DoubledRemainderTarget (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S)
    (base : ℕ) (ε : ℝ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ δ ≤ ε ∧
    let U := stateNeighborhood S C base δ
    (∃ B : StateParameter S → HeightPair S →L[ℝ] HeightPair S →L[ℝ]
        HeightAt S (3 / 2 : ℝ),
      (∀ z ∈ U, ∀ (η ξ : HeightPair S) (p : PolarPoint), p ∈ annularOpen D →
        (S.height (3 / 2 : ℝ)).decode (B z η ξ) p =
          posteriorPeriodTaylor D S C z η ξ p) ∧
      SmoothTameOn
        (pairGrading (pairGrading (stateParameterGrading S) (heightPairGrading S))
          (heightPairGrading S)) (S.height (3 / 2 : ℝ)).grading
        ((U ×ˢ univ) ×ˢ univ)
        (fun z : (StateParameter S × HeightPair S) × HeightPair S => B z.1.1 z.1.2 z.2)) ∧
    (∃ C₀ : NonlinearGeometryData S, ∃ E : AnnularState S → CircleSpace S,
      ∃ rawBase : ℕ, ∃ rawδ : ℝ, 0 < rawδ ∧
      let U₀ := rawNeighborhood S rawBase rawδ
      RawReturnConditions D S C C₀ E U₀ ∧
      ∃ J : SmoothDirections U₀ E,
      ∃ B : AnnularState S → AnnularState S →L[ℝ] AnnularState S →L[ℝ]
          CircleAt S (3 / 2 : ℝ),
        (∀ z ∈ U₀, ∀ v w m θ,
          (S.circle (3 / 2 : ℝ)).decode (B z v w) m θ =
            posteriorCircleTaylor S U₀ E J z v w m) ∧
        SmoothTameOn
          (pairGrading (pairGrading (stateGrading S) (stateGrading S))
            (stateGrading S)) (S.circle (3 / 2 : ℝ)).grading
          ((U₀ ×ˢ univ) ×ˢ univ)
          (fun z : (AnnularState S × AnnularState S) × AnnularState S =>
            B z.1.1 z.1.2 z.2))

/-- A primitive from the right endpoint has its own free left constant.
Its exponent is unchanged, and its loss is fixed before the output order. -/
def MeanPrimitiveTarget (D : ReferenceData) (S : PhysicalSpacesData) : Prop :=
  ∀ γ : ℝ, 0 < γ →
    ∃ P : HeightAt S γ →L[ℝ] ExtendedHeightAt S γ,
      (∀ (f : HeightAt S γ) (p : PolarPoint), p ∈ annularOpen D →
        extendedHeightField S γ (P f) p =
          -(∫ r in p.1..D.b, angularMean (fun θ => (S.height γ).decode f (r, θ)))) ∧
      (∃ loss base : ℕ, ContinuousFlexibility.Analysis.IsTameLinear
        (S.height γ).grading (extendedHeightGrading S γ) P.toLinearMap loss base)

def StrongBranchTarget (D : ReferenceData) (T : MaterialData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (B : WeakBranchData S) : Prop :=
  ∃ strongMean : ℝ → ExtendedHeightAt S (3 / 2 : ℝ),
    ∃ strongKappa : ℝ → CircleAt S (3 / 2 : ℝ),
      (∀ q : ℝ, |q| < B.radius →
        (∀ p ∈ annularOpen D, extendedHeightField S (3 / 2 : ℝ) (strongMean q) p =
          angularMean (fun θ => stateU S (B.state q) (p.1, θ))) ∧
        ∀ m θ, (S.circle (3 / 2 : ℝ)).decode (strongKappa q) m θ =
          stateKappa S (B.state q) m) ∧
      SmoothTameOn realGrading (extendedHeightGrading S (3 / 2 : ℝ))
        (Ioo (-B.radius) B.radius) strongMean ∧
      SmoothTameOn realGrading (S.circle (3 / 2 : ℝ)).grading
        (Ioo (-B.radius) B.radius) strongKappa ∧
      (∀ s : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ q : ℝ, |q| < B.radius →
        extendedHeightGrading S (3 / 2 : ℝ) s (strongMean q) ≤ K * |q| ∧
        |(B.state q).2.1| + (S.circle (3 / 2 : ℝ)).grading s (strongKappa q) ≤ K * q ^ 2) ∧
      (∀ a : ℕ, ∀ ε : ℝ, 0 < ε → ∃ K δ : ℝ, 0 ≤ K ∧ 0 < δ ∧
        ∀ q r : ℝ, |q| < B.radius → r ∈ Ioo D.a D.b → endpointDistance D r < δ →
          |iteratedDeriv a (fun t => stateProfile D S C (B.state q) t - D.w t) r| ≤
            K * q ^ 2 * T.H r ^ (1 - ε)) ∧
      (∀ a : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ q r : ℝ, |q| < B.radius →
        |iteratedDeriv a (fun t => stateProfile D S C (B.state q) t - D.w t) r| ≤ K * q ^ 2)

/-- X02 strengthens the same branch: actual two-weak-factor remainders,
an exponent-preserving mean primitive, strong parameter topology,
quadratic controls and the H^(1-epsilon) endpoint bound. -/
def X02Statement : Prop :=
  ∃ A : RadialReference, ∃ T S C R base loss ε q0,
    IsMaterialData A.val T ∧ IsPhysicalSpaces A.val T S ∧
    N01Properties A.val T S C base loss ε ∧ N02Properties A.val T S C R base ε ∧
      NonlinearStagesThrough10 A.val T S C R base loss ε q0 ∧
      DoubledRemainderTarget A.val S C base ε ∧ MeanPrimitiveTarget A.val S ∧
      ∃ B : WeakBranchData S, IsWeakBranch A.val S C R base ε B ∧ B.radius ≤ q0 ∧
        ∃ q1 : ℝ, 0 < q1 ∧ q1 ≤ B.radius ∧
          StrongBranchTarget A.val T S C { radius := q1, state := B.state }

end ContinuousFlexibility.Statements
