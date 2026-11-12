import ContinuousFlexibility.Statements.Analysis
import ContinuousFlexibility.Contracts.Annular
import ContinuousFlexibility.Scalar.NormalizedConservation
import ContinuousFlexibility.Scalar.TypeCorrection
import ContinuousFlexibility.Scalar.FormPullback
import Mathlib.Topology.OpenPartialHomeomorph.Defs

/-!
# Concrete nonlinear targets N01--N12 and X02

Every `...Statement` below is a proposition awaiting proof. Candidate data
contain actual functions, charts, linear maps and closed-graph candidates,
not assumed existence theorems or arbitrary predicates called stable inverse.
The scalar residual is the project's actual removable height residual.

Paper correspondence: section 7, lines 208--715; section 8; section 9;
section 10, lines 19--317.  N12 is unconditionally `Nonempty FlatAnnularCore`.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators ENNReal

set_option backward.isDefEq.respectTransparency false

abbrev HeightPair (S : PhysicalSpacesData) := (S.height (3 / 4 : ℝ)).Space × ℝ
abbrev CircleSpace (S : PhysicalSpacesData) := (S.circle (3 / 4 : ℝ)).Space
abbrev AnnularState (S : PhysicalSpacesData) :=
  HeightPair S × (ℝ × (CircleSpace S × CircleSpace S))

def stateSector (S : PhysicalSpacesData) (x : AnnularState S) : Prop :=
  (∀ m θ φ, (S.circle (3 / 4 : ℝ)).decode x.2.2.1 m θ =
    (S.circle (3 / 4 : ℝ)).decode x.2.2.1 m φ) ∧
  (∀ m θ, (S.circle (3 / 4 : ℝ)).decode x.2.2.2 m (-θ) =
    -(S.circle (3 / 4 : ℝ)).decode x.2.2.2 m θ)

/-- Evaluate one decoded circle component as an actual scalar linear map. -/
private def circleScalarEval (S : PhysicalSpacesData) (m : ℕ) (θ : ℝ) :
    CircleSpace S →ₗ[ℝ] ℝ :=
  (LinearMap.proj θ).comp ((LinearMap.proj m).comp (S.circle (3 / 4 : ℝ)).decode)

private def stateCirclePairProjection (S : PhysicalSpacesData) :
    AnnularState S →ₗ[ℝ] CircleSpace S × CircleSpace S :=
  (LinearMap.snd ℝ ℝ (CircleSpace S × CircleSpace S)).comp
    (LinearMap.snd ℝ (HeightPair S) (ℝ × (CircleSpace S × CircleSpace S)))

private def stateKappaEval (S : PhysicalSpacesData) (m : ℕ) (θ : ℝ) :
    AnnularState S →ₗ[ℝ] ℝ :=
  (circleScalarEval S m θ).comp
    ((LinearMap.fst ℝ (CircleSpace S) (CircleSpace S)).comp (stateCirclePairProjection S))

private def stateChartEval (S : PhysicalSpacesData) (m : ℕ) (θ : ℝ) :
    AnnularState S →ₗ[ℝ] ℝ :=
  (circleScalarEval S m θ).comp
    ((LinearMap.snd ℝ (CircleSpace S) (CircleSpace S)).comp (stateCirclePairProjection S))

private theorem stateKappaEval_apply (S : PhysicalSpacesData) (m : ℕ) (θ : ℝ)
    (x : AnnularState S) :
    stateKappaEval S m θ x = (S.circle (3 / 4 : ℝ)).decode x.2.2.1 m θ := rfl

private theorem stateChartEval_apply (S : PhysicalSpacesData) (m : ℕ) (θ : ℝ)
    (x : AnnularState S) :
    stateChartEval S m θ x = (S.circle (3 / 4 : ℝ)).decode x.2.2.2 m θ := rfl

/-- Constancy and oddness are intersections of actual scalar linear kernels. -/
private def stateSectorKernel (S : PhysicalSpacesData) : Submodule ℝ (AnnularState S) :=
  (⨅ (m : ℕ), ⨅ (θ : ℝ), ⨅ (φ : ℝ),
    (stateKappaEval S m θ - stateKappaEval S m φ).ker) ⊓
    (⨅ (m : ℕ), ⨅ (θ : ℝ),
      (stateChartEval S m (-θ) + stateChartEval S m θ).ker)

private theorem stateSector_iff_mem_kernel (S : PhysicalSpacesData) (x : AnnularState S) :
    stateSector S x ↔ x ∈ stateSectorKernel S := by
  simp only [stateSector, stateSectorKernel, Submodule.mem_inf, Submodule.mem_iInf,
    LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.add_apply,
    stateKappaEval_apply, stateChartEval_apply, sub_eq_zero, add_eq_zero_iff_eq_neg]

set_option maxHeartbeats 1000000 in
def stateSectorSubmodule (S : PhysicalSpacesData) : Submodule ℝ (AnnularState S) :=
  (stateSectorKernel S).copy {x | stateSector S x} (by
    ext x
    exact stateSector_iff_mem_kernel S x)

abbrev StateDirections (S : PhysicalSpacesData) := stateSectorSubmodule S

abbrev evenCircleSubmodule (S : PhysicalSpacesData) := evenCircleSubmoduleAt S (3 / 4 : ℝ)

abbrev EvenCircle (S : PhysicalSpacesData) := evenCircleSubmodule S
abbrev ResidualSpace (S : PhysicalSpacesData) := S.Source × EvenCircle S

structure ResidualData (S : PhysicalSpacesData) where
  scalar : AnnularState S × ℝ → S.Source
  circle : AnnularState S × ℝ → EvenCircle S

def jointResidual (S : PhysicalSpacesData) (P : ResidualData S)
    (z : AnnularState S × ℝ) : ResidualSpace S := (P.scalar z, P.circle z)

structure CoupledInverseData (S : PhysicalSpacesData) where
  V : AnnularState S × ℝ → ResidualSpace S →ₗ[ℝ] AnnularState S
  sectorV : StateDirections S × ℝ → ResidualSpace S →ₗ[ℝ] StateDirections S

structure QuadraticErrorData (S : PhysicalSpacesData) where
  Q : AnnularState S × ℝ → ResidualSpace S →ₗ[ℝ] ResidualSpace S →ₗ[ℝ] ResidualSpace S

def residualGrading (S : PhysicalSpacesData) : ℕ → Seminorm ℝ (ResidualSpace S) :=
  pairGrading S.sourceGrading (fun n => ((S.circle (3 / 4 : ℝ)).grading n).comp
    (evenCircleSubmodule S).subtype)

def heightPairField (S : PhysicalSpacesData) (u : HeightPair S) : PolarPoint → ℝ :=
  fun p => (S.height (3 / 4 : ℝ)).decode u.1 p + u.2 * S.chiLeft p.1

def heightPairGrading (S : PhysicalSpacesData) : ℕ → Seminorm ℝ (HeightPair S) :=
  pairGrading (S.height (3 / 4 : ℝ)).grading realGrading

def stateGrading (S : PhysicalSpacesData) : ℕ → Seminorm ℝ (AnnularState S) :=
  pairGrading (heightPairGrading S)
    (pairGrading realGrading (pairGrading (S.circle (3 / 4 : ℝ)).grading
      (S.circle (3 / 4 : ℝ)).grading))

def stateU (S : PhysicalSpacesData) (x : AnnularState S) : PolarPoint → ℝ :=
  heightPairField S x.1

def stateKappa (S : PhysicalSpacesData) (x : AnnularState S) (m : ℕ) : ℝ :=
  angularMean ((S.circle (3 / 4 : ℝ)).decode x.2.2.1 m)

def stateLeftChart (S : PhysicalSpacesData) (x : AnnularState S) (m : ℕ) (θ : ℝ) : ℝ :=
  θ + (S.circle (3 / 4 : ℝ)).decode x.2.2.2 m θ

/-- Optical-control geometry and ordinary flow candidates, without their properties. -/
structure NonlinearGeometryData (S : PhysicalSpacesData) where
  control : ℕ → ℝ → ℝ
  cell : ℕ → ℕ
  left : ℕ → ℝ
  right : ℕ → ℝ
  travel : ℕ → ℝ
  referenceState : AnnularState S
  minusFlow : AnnularState S × ℝ → ℕ → ℝ → ℝ → ℝ
  minusReturnInverse : AnnularState S × ℝ → ℕ → ℝ → ℝ
  rightChartInverse : AnnularState S × ℝ → ℕ → ℝ → ℝ

def stateProfile (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (x : AnnularState S) (r : ℝ) : ℝ :=
  D.w r * Real.exp (x.2.1 * D.chi r + ∑' m, stateKappa S x m * C.control m r)

def stateRadialHeight (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (x : AnnularState S) (r : ℝ) : ℝ :=
  ∫ t in D.b..r, stateProfile D S C x t

def stateHeight (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (z : AnnularState S × ℝ) (p : PolarPoint) : ℝ :=
  stateRadialHeight D S C z.1 p.1 + z.2 * stateU S z.1 p

def scalarResidualField (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (z : AnnularState S × ℝ) : PolarPoint → ℝ :=
  normalizedHeightResidual (stateProfile D S C z.1)
    (ContinuousFlexibility.Radial.radialHeightField (stateRadialHeight D S C z.1))
    (stateU S z.1) z.2

structure SymmetricCoefficients where
  a : PolarPoint → ℝ
  b : PolarPoint → ℝ
  c : PolarPoint → ℝ

def divergenceOperator (L : SymmetricCoefficients) (u : PolarPoint → ℝ)
    (p : PolarPoint) : ℝ :=
  radialPartial (fun y => L.a y * radialPartial u y + L.b y * angularPartial u y) p +
  angularPartial (fun y => L.b y * radialPartial u y + L.c y * angularPartial u y) p

def originalCoefficients (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (z : AnnularState S × ℝ) : SymmetricCoefficients where
  a := polarLinearA (stateProfile D S C z.1) (stateHeight D S C z)
  b := polarLinearB (stateProfile D S C z.1) (stateHeight D S C z)
  c := polarCorrectedC (stateProfile D S C z.1) (stateHeight D S C z)

def minusCharacteristicSpeed (L : SymmetricCoefficients) (p : PolarPoint) : ℝ :=
  L.b p / L.a p - Real.sqrt (L.b p ^ 2 - L.a p * L.c p) / L.a p

def plusCharacteristicSpeed (L : SymmetricCoefficients) (p : PolarPoint) : ℝ :=
  L.b p / L.a p + Real.sqrt (L.b p ^ 2 - L.a p * L.c p) / L.a p

def stateNeighborhood (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (base : ℕ) (ε : ℝ) : Set (AnnularState S × ℝ) :=
  {z | stateGrading S base (z.1 - C.referenceState) < ε ∧ |z.2| < ε}

def sectorGrading (S : PhysicalSpacesData) : ℕ → Seminorm ℝ (StateDirections S) :=
  fun n => (stateGrading S n).comp (stateSectorSubmodule S).subtype

def liftSectorParameter (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (z : StateDirections S × ℝ) : AnnularState S × ℝ :=
  (C.referenceState + z.1.val, z.2)

def sectorNeighborhood (S : PhysicalSpacesData) (base : ℕ) (ε q0 : ℝ) :
    Set (StateDirections S × ℝ) :=
  {z | sectorGrading S base z.1 < ε ∧ |z.2| < q0}

def sectorJointResidual (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (P : ResidualData S) (z : StateDirections S × ℝ) : ResidualSpace S :=
  jointResidual S P (liftSectorParameter S C z)

def referenceStateConditions (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) : Prop :=
  (∀ p, stateU S C.referenceState p = D.phi p.1 * ContinuousFlexibility.Radial.cosineMode 2 p.2) ∧
  C.referenceState.1.2 = 0 ∧ C.referenceState.2.1 = 0 ∧
  C.referenceState.2.2.1 = 0 ∧ C.referenceState.2.2.2 = 0 ∧
  referenceRow D (stateU S C.referenceState) = 1

def controlGeometryConditions (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) : Prop :=
  (∀ m, D.a < C.left m ∧ C.left m < C.right m ∧ C.right m < D.b) ∧
  (∀ m, deriv D.w (C.left m) = 0 ∧ deriv D.w (C.right m) = 0 ∧
    deriv (deriv D.w) (C.left m) ≠ 0 ∧ deriv (deriv D.w) (C.right m) ≠ 0) ∧
  (∀ m n, m ≠ n → Disjoint (Ioo (C.left m) (C.right m)) (Ioo (C.left n) (C.right n))) ∧
  (∀ m r, r ∈ Ioo (C.left m) (C.right m) → deriv D.w r < 0) ∧
  (∀ r ∈ Ioo D.a D.b, deriv D.w r < 0 →
    ∃ m, r ∈ Ioo (C.left m) (C.right m)) ∧
  (∀ m, ContDiff ℝ ∞ (C.control m) ∧ HasCompactSupport (C.control m) ∧
    tsupport (C.control m) ⊆ Ioo (C.left m) (C.right m)) ∧
  LocallyFinite (fun m => {r : Ioo D.a D.b | (r : ℝ) ∈ Function.support (C.control m)}) ∧
  (∀ m, C.travel m = ∫ r in C.left m..C.right m,
    Real.sqrt (-deriv D.w r / (r * D.w r))) ∧
  (∀ m, HasDerivAt (fun t : ℝ => ∫ r in C.left m..C.right m,
      Real.sqrt (-deriv (fun s => D.w s * Real.exp (t * C.control m s)) r /
        (r * (D.w r * Real.exp (t * C.control m r))))) 1 0)

/-- Passing to ordinary support preserves the component inclusion. -/
theorem controlGeometryConditions.support_subset
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    (hC : controlGeometryConditions D S C) (m : ℕ) :
    Function.support (C.control m) ⊆ Ioo (C.left m) (C.right m) := by
  obtain ⟨_, _, _, _, _, hcontrol, _⟩ := hC
  exact (subset_tsupport (C.control m)).trans (hcontrol m).2.2

def ordinaryFlowConditions (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (U : Set (AnnularState S × ℝ)) : Prop :=
  ∀ z ∈ U, ∀ m θ,
    C.minusFlow z m (C.left m) θ = θ ∧
    ContinuousOn (fun r => C.minusFlow z m r θ) (Icc (C.left m) (C.right m)) ∧
    (∀ r ∈ Ioo (C.left m) (C.right m), HasDerivAt (fun s => C.minusFlow z m s θ)
      (minusCharacteristicSpeed (originalCoefficients D S C z)
        (r, C.minusFlow z m r θ)) r) ∧
    (∀ r ∈ Icc (C.left m) (C.right m),
      0 < deriv (C.minusFlow z m r) θ ∧
      C.minusFlow z m r (θ + Real.pi) = C.minusFlow z m r θ + Real.pi)

def coefficientFamily (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (i : Fin 3) (a b : ℕ) (p : PolarPoint)
    (z : AnnularState S × ℝ) : ℝ :=
  let F : AnnularState S × ℝ → PolarPoint → ℝ := fun y =>
    if i = 0 then (originalCoefficients D S C y).a else
    if i = 1 then (originalCoefficients D S C y).b else (originalCoefficients D S C y).c
  mixedDerivative a b (fun x => F z x - F (C.referenceState, 0) x) p

def ordinaryFlowFamily (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (m a b : ℕ) (p : PolarPoint) (z : AnnularState S × ℝ) : ℝ :=
  mixedDerivative a b (fun x => C.minusFlow z m x.1 x.2 -
    C.minusFlow (C.referenceState, 0) m x.1 x.2) p

def oneHighVariationWeight {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (base high : ℕ) (x : E) {k : ℕ} (v : Fin k → E) : ℝ :=
  (1 + p high x) * ∏ i, p base (v i) +
    ∑ i : Fin k, p high (v i) * ∏ j ∈ Finset.univ.erase i, p base (v j)

def N01Properties (D : ReferenceData) (T : MaterialData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (base loss : ℕ) (ε : ℝ) : Prop :=
  IsRadialReference D ∧ 0 < ε ∧ referenceStateConditions D S C ∧ controlGeometryConditions D S C ∧
  (∃ B : ℝ, 0 < B ∧ ∀ m,
    |(D.cellIndex (C.cell m) : ℝ) - D.cellIndex m| ≤ B) ∧
  (∀ s : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ m r,
    r ∈ Ioo (C.left m) (C.right m) →
      |iteratedDeriv s (C.control m) r| ≤ B * T.E0 (T.sample (C.cell m)) ^ B) ∧
  ordinaryFlowConditions D S C (stateNeighborhood S C base ε) ∧
  (∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 → ∀ m θ,
    (1 / 2 : ℝ) ≤ deriv (stateLeftChart S z.1 m) θ ∧
    deriv (stateLeftChart S z.1 m) θ ≤ 2 ∧
    stateLeftChart S z.1 m (θ + Real.pi) = stateLeftChart S z.1 m θ + Real.pi ∧
    stateLeftChart S z.1 m (-θ) = -stateLeftChart S z.1 m θ) ∧
  (∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 → ∀ m θ,
    let hR : ℝ → ℝ := fun t =>
      ((stateLeftChart S z.1 m (C.minusReturnInverse z m t) - C.travel m) -
        (stateLeftChart S z.1 m (C.minusReturnInverse z m (-t)) - C.travel m)) / 2
    C.minusFlow z m (C.right m) (C.minusReturnInverse z m θ) = θ ∧
    C.minusReturnInverse z m (C.minusFlow z m (C.right m) θ) = θ ∧
    hR (C.rightChartInverse z m θ) = θ ∧ C.rightChartInverse z m (hR θ) = θ) ∧
  (∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 → ∀ p ∈ annularOpen D,
    (1 / 2 : ℝ) ≤ stateProfile D S C z.1 p.1 / D.w p.1 ∧
    stateProfile D S C z.1 p.1 / D.w p.1 ≤ 2 ∧
    (7 / 8 : ℝ) ≤ heightQ (profileEnergy (stateProfile D S C z.1) p)
      (heightRadial (stateHeight D S C z) p)
      (angularPartial (heightAngular (stateHeight D S C z)) p) /
        stateProfile D S C z.1 p.1 ∧
    heightQ (profileEnergy (stateProfile D S C z.1) p)
      (heightRadial (stateHeight D S C z) p)
      (angularPartial (heightAngular (stateHeight D S C z)) p) /
        stateProfile D S C z.1 p.1 ≤ (9 / 8 : ℝ) ∧
    (1 / 2 : ℝ) ≤ polarDiscriminant (stateProfile D S C z.1) (stateHeight D S C z) p ∧
    polarDiscriminant (stateProfile D S C z.1) (stateHeight D S C z) p ≤ (3 / 2 : ℝ)) ∧
  (∀ z ∈ stateNeighborhood S C base ε, ∀ r ∈ Ioo D.a D.b,
    deriv D.w r = 0 → stateProfile D S C z.1 =ᶠ[𝓝 r] D.w) ∧
  (∀ k s : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ m i a b p,
    a + b ≤ s → p.1 ∈ D.cells m →
    ∃ J : SmoothDirections (stateNeighborhood S C base ε) (coefficientFamily D S C i a b p),
      ∀ z ∈ stateNeighborhood S C base ε, ∀ v : Fin k → (AnnularState S × ℝ),
        |J.D k z v| ≤ B * T.H (T.sample m) ^ (3 / 4 : ℝ) *
          T.E0 (T.sample m) ^ B *
          oneHighVariationWeight (pairGrading (stateGrading S) realGrading)
            base (s + loss) (z - (C.referenceState, 0)) v) ∧
  (∀ k s : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ m a b p,
    a + b ≤ s → p.1 ∈ Ioo (C.left m) (C.right m) →
    ∃ J : SmoothDirections (stateNeighborhood S C base ε) (ordinaryFlowFamily S C m a b p),
      ∀ z ∈ stateNeighborhood S C base ε, ∀ v : Fin k → (AnnularState S × ℝ),
        min (p.1 - C.left m) (C.right m - p.1) ^ a * |J.D k z v| ≤
          B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
          T.E0 (T.sample (C.cell m)) ^ B *
          oneHighVariationWeight (pairGrading (stateGrading S) realGrading)
            base (s + loss) (z - (C.referenceState, 0)) v)

/-- The first concrete stage, on the neighborhood used by every later stage. -/
def NonlinearPropertiesThrough01 (D : ReferenceData) (T : MaterialData)
    (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (base loss : ℕ) (ε : ℝ) : Prop :=
  N01Properties D T S C base loss ε

/-- N01, section 7 lines 208--338. Construct the actual reference and all
realizations; one base, loss and radius precede all orders. -/
def N01Statement : Prop :=
  ∃ A : RadialReference, ∃ T : MaterialData, ∃ S : PhysicalSpacesData,
    ∃ C : NonlinearGeometryData S, ∃ base loss : ℕ, ∃ ε : ℝ,
      IsMaterialData A.val T ∧ IsPhysicalSpaces A.val T S ∧
        NonlinearPropertiesThrough01 A.val T S C base loss ε

def oddPart (f : ℝ → ℝ) (θ : ℝ) : ℝ := (f θ - f (-θ)) / 2
def evenPart (f : ℝ → ℝ) (θ : ℝ) : ℝ := (f θ + f (-θ)) / 2

def rightChartCandidate (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (z : AnnularState S × ℝ) (m : ℕ) : ℝ → ℝ :=
  oddPart (fun θ => stateLeftChart S z.1 m (C.minusReturnInverse z m θ) - C.travel m)

def returnResidualField (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (z : AnnularState S × ℝ) (m : ℕ) (θ : ℝ) : ℝ :=
  evenPart (fun t => stateLeftChart S z.1 m (C.minusReturnInverse z m t) - C.travel m)
    (C.rightChartInverse z m θ)

def circleRotationDifference (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (v : CircleSpace S) (m : ℕ) (θ : ℝ) : ℝ :=
  evenPart (fun t => (S.circle (3 / 4 : ℝ)).decode v m (t + C.travel m)) θ

def circleChartError (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (z : AnnularState S × ℝ) (r v : CircleSpace S) (m : ℕ) (θ : ℝ) : ℝ :=
  evenPart (fun t => (S.circle (3 / 4 : ℝ)).decode r m t *
    ∫ a in (0 : ℝ)..1,
      deriv ((S.circle (3 / 4 : ℝ)).decode v m)
        (t + C.travel m + a * returnResidualField S C z m t)) θ -
  deriv ((S.circle (3 / 4 : ℝ)).decode r m) θ *
    oddPart (fun t => (S.circle (3 / 4 : ℝ)).decode v m
      (t + C.travel m + returnResidualField S C z m t)) θ

def IsEvenZeroMeanCircle (S : PhysicalSpacesData) (u : CircleSpace S) : Prop :=
  ∀ m, Function.Even ((S.circle (3 / 4 : ℝ)).decode u m) ∧
    angularMean ((S.circle (3 / 4 : ℝ)).decode u m) = 0

def IsOddCircle (S : PhysicalSpacesData) (u : CircleSpace S) : Prop :=
  ∀ m θ, (S.circle (3 / 4 : ℝ)).decode u m (-θ) =
    -(S.circle (3 / 4 : ℝ)).decode u m θ

structure ReturnEquationData (S : PhysicalSpacesData) where
  residual : AnnularState S × ℝ → CircleSpace S
  linearPart : CircleSpace S →L[ℝ] CircleSpace S
  inverse : CircleSpace S →ₗ[ℝ] CircleSpace S
  chartIncrement : AnnularState S × ℝ → CircleSpace S →ₗ[ℝ] CircleSpace S
  error : AnnularState S × ℝ → CircleSpace S →ₗ[ℝ] CircleSpace S →ₗ[ℝ] CircleSpace S

def N02Properties (_D : ReferenceData) (_T : MaterialData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (R : ReturnEquationData S)
    (base : ℕ) (ε : ℝ) : Prop :=
  let U := stateNeighborhood S C base ε
  (∀ z ∈ U, stateSector S z.1 → ∀ m θ,
    C.minusFlow z m (C.right m) (C.minusReturnInverse z m θ) = θ ∧
    C.minusReturnInverse z m (C.minusFlow z m (C.right m) θ) = θ ∧
    rightChartCandidate S C z m (C.rightChartInverse z m θ) = θ ∧
    C.rightChartInverse z m (rightChartCandidate S C z m θ) = θ ∧
    0 < deriv (rightChartCandidate S C z m) θ) ∧
  (∀ z ∈ U, stateSector S z.1 → ∀ m θ, (S.circle (3 / 4 : ℝ)).decode (R.residual z) m θ =
    returnResidualField S C z m θ) ∧
  (∀ z ∈ U, stateSector S z.1 → (R.residual z = 0 ↔ ∀ m θ,
    rightChartCandidate S C z m (C.minusFlow z m (C.right m) θ) =
      stateLeftChart S z.1 m θ - C.travel m ∧
    rightChartCandidate S C z m (-C.minusFlow z m (C.right m) (-θ)) =
      stateLeftChart S z.1 m θ + C.travel m)) ∧
  (∀ v m θ, (S.circle (3 / 4 : ℝ)).decode (R.linearPart v) m θ =
    circleRotationDifference S C v m θ) ∧
  (∀ z ∈ U, stateSector S z.1 → ∀ r v m θ, (S.circle (3 / 4 : ℝ)).decode (R.error z r v) m θ =
    circleChartError S C z r v m θ) ∧
  (∀ z ∈ U, stateSector S z.1 → ∀ v m θ, (S.circle (3 / 4 : ℝ)).decode (R.chartIncrement z v) m θ =
    (S.circle (3 / 4 : ℝ)).decode v m (stateLeftChart S z.1 m θ)) ∧
  (∀ z ∈ U, stateSector S z.1 → ∀ v, IsOddCircle S v →
    ContinuousFlexibility.Analysis.HasProjectiveLineDerivAt
      (fun x => R.residual (x, z.2)) (R.linearPart v + R.error z (R.residual z) v)
      z.1 (0, (0, (0, R.chartIncrement z v)))) ∧
  (∀ g, IsEvenZeroMeanCircle S g → R.linearPart (R.inverse g) = g ∧
    IsOddCircle S (R.inverse g)) ∧
  (∀ v, IsOddCircle S v → R.inverse (R.linearPart v) = v) ∧
  (∃ loss b, ContinuousFlexibility.Analysis.IsTameLinear
    (S.circle (3 / 4 : ℝ)).grading (S.circle (3 / 4 : ℝ)).grading R.inverse loss b) ∧
  SmoothTameOn (pairGrading (sectorGrading S) realGrading)
    (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε ε)
    (fun z => R.residual (liftSectorParameter S C z))

/-- The same geometric data also realize the actual return equation. -/
def NonlinearPropertiesThrough02 (D : ReferenceData) (T : MaterialData)
    (S : PhysicalSpacesData) (C : NonlinearGeometryData S) (R : ReturnEquationData S)
    (base loss : ℕ) (ε : ℝ) : Prop :=
  NonlinearPropertiesThrough01 D T S C base loss ε ∧ N02Properties D T S C R base ε

/-- N02, two actual returns and the zero-mean small-divisor inverse; §7 341--389.
The earlier stage is realized by this very same construction. -/
def N02Statement : Prop :=
  ∃ A : RadialReference, ∃ T : MaterialData, ∃ S : PhysicalSpacesData,
    ∃ C : NonlinearGeometryData S, ∃ R : ReturnEquationData S,
      ∃ base loss : ℕ, ∃ ε : ℝ,
        IsMaterialData A.val T ∧ IsPhysicalSpaces A.val T S ∧
          NonlinearPropertiesThrough02 A.val T S C R base loss ε

structure ReturnCorrectionData (S : PhysicalSpacesData) where
  coefficients : AnnularState S × ℝ → SymmetricCoefficients
  minusFlow : AnnularState S × ℝ → ℕ → ℝ → ℝ → ℝ
  error : AnnularState S × ℝ → CircleSpace S →ₗ[ℝ] HeightPair S →ₗ[ℝ] S.Source

def N03Properties (D : ReferenceData) (_T : MaterialData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (R : ReturnEquationData S)
    (L : ReturnCorrectionData S) (base : ℕ) (ε : ℝ) : Prop :=
  let U := stateNeighborhood S C base ε
  (∀ z ∈ U, stateSector S z.1 → ∀ p, (L.coefficients z).a p = (originalCoefficients D S C z).a p) ∧
  (∀ z ∈ U, stateSector S z.1 → ∀ p ∈ annularOpen D, 0 < deriv D.w p.1 →
    (L.coefficients z).b =ᶠ[𝓝 p] (originalCoefficients D S C z).b ∧
    (L.coefficients z).c =ᶠ[𝓝 p] (originalCoefficients D S C z).c) ∧
  (∀ z ∈ U, stateSector S z.1 → ∀ p ∈ annularOpen D, deriv D.w p.1 = 0 →
    (L.coefficients z).b =ᶠ[𝓝 p] (originalCoefficients D S C z).b ∧
    (L.coefficients z).c =ᶠ[𝓝 p] (originalCoefficients D S C z).c) ∧
  (∀ z ∈ U, stateSector S z.1 → ∀ r θ,
    (L.coefficients z).a (r, -θ) = (L.coefficients z).a (r, θ) ∧
    (L.coefficients z).b (r, -θ) = -(L.coefficients z).b (r, θ) ∧
    (L.coefficients z).c (r, -θ) = (L.coefficients z).c (r, θ)) ∧
  (∀ z ∈ U, stateSector S z.1 → ∀ m θ,
    L.minusFlow z m (C.left m) θ = θ ∧
    ContinuousOn (fun r => L.minusFlow z m r θ) (Icc (C.left m) (C.right m)) ∧
    (∀ r ∈ Ioo (C.left m) (C.right m), HasDerivAt (fun s => L.minusFlow z m s θ)
      (minusCharacteristicSpeed (L.coefficients z) (r, L.minusFlow z m r θ)) r) ∧
    rightChartCandidate S C z m (L.minusFlow z m (C.right m) θ) =
      stateLeftChart S z.1 m θ - C.travel m ∧
    rightChartCandidate S C z m (-L.minusFlow z m (C.right m) (-θ)) =
      stateLeftChart S z.1 m θ + C.travel m) ∧
  (∀ z ∈ U, stateSector S z.1 → ∀ η : HeightPair S, ∀ p ∈ annularOpen D,
    divergenceOperator (originalCoefficients D S C z) (heightPairField S η) p -
      divergenceOperator (L.coefficients z) (heightPairField S η) p =
        (S.height (3 / 4 : ℝ)).decode ((L.error z (R.residual z) η).val) p) ∧
  (∀ z ∈ U, stateSector S z.1 → ∀ r η,
    physicalSourceIntegral D ((S.height (3 / 4 : ℝ)).decode ((L.error z r η).val)) = 0) ∧
  SmoothTameOn
    (pairGrading (pairGrading (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading) (heightPairGrading S))
    S.sourceGrading ((sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ univ)
    (fun z : ((StateDirections S × ℝ) × CircleSpace S) × HeightPair S =>
      L.error (liftSectorParameter S C z.1.1) z.1.2 z.2)

/-- Return correction is attached to the same profile, spaces and returns. -/
def NonlinearPropertiesThrough03 (D : ReferenceData) (T : MaterialData)
    (S : PhysicalSpacesData) (C : NonlinearGeometryData S) (R : ReturnEquationData S)
    (L : ReturnCorrectionData S) (base loss : ℕ) (ε : ℝ) : Prop :=
  NonlinearPropertiesThrough02 D T S C R base loss ε ∧ N03Properties D T S C R L base ε

/-- N03: actual symmetric divergence completion on one cumulative construction;
only interface flux is fixed. -/
def N03Statement : Prop :=
  ∃ A : RadialReference, ∃ T : MaterialData, ∃ S : PhysicalSpacesData,
    ∃ C : NonlinearGeometryData S, ∃ R : ReturnEquationData S,
      ∃ L : ReturnCorrectionData S, ∃ base loss : ℕ, ∃ ε : ℝ,
        IsMaterialData A.val T ∧ IsPhysicalSpaces A.val T S ∧
          NonlinearPropertiesThrough03 A.val T S C R L base loss ε

def rootEven (G : ℝ × ℝ × ℝ → ℝ) (p : PolarPoint) : ℝ :=
  (G (p.1, p.1 ^ (3 / 2 : ℝ), p.2) + G (p.1, -(p.1 ^ (3 / 2 : ℝ)), p.2)) / 2

def rootOdd (G : ℝ × ℝ × ℝ → ℝ) (p : PolarPoint) : ℝ :=
  if p.1 = 0 then deriv (fun t => G (0, t, p.2)) 0 else
    (G (p.1, p.1 ^ (3 / 2 : ℝ), p.2) - G (p.1, -(p.1 ^ (3 / 2 : ℝ)), p.2)) /
      (2 * p.1 ^ (3 / 2 : ℝ))

def CSBound {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : ℕ) (K : Set E) (f : E → ℝ) (M : ℝ) : Prop :=
  ∀ n : ℕ, n ≤ s → ∀ x ∈ K, ‖iteratedFDeriv ℝ n f x‖ ≤ M

def RootCompositionTarget : Prop :=
  (∀ G : ℝ × ℝ × ℝ → ℝ, ContDiff ℝ ∞ G →
    ContDiffOn ℝ ∞ (rootEven G) (Ici (0 : ℝ) ×ˢ univ) ∧
    ContDiffOn ℝ ∞ (rootOdd G) (Ici (0 : ℝ) ×ˢ univ)) ∧
    ∀ s : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ G : ℝ × ℝ × ℝ → ℝ,
      ContDiff ℝ ∞ G → ∀ M : ℝ,
      (CSBound s (Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 ×ˢ Icc (-Real.pi) Real.pi) G M →
        CSBound s (Icc (0 : ℝ) 1 ×ˢ Icc (-Real.pi) Real.pi) (rootEven G) (C * M)) ∧
      (CSBound (s + 1) (Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 ×ˢ Icc (-Real.pi) Real.pi) G M →
        CSBound s (Icc (0 : ℝ) 1 ×ˢ Icc (-Real.pi) Real.pi) (rootOdd G) (C * M))

def cubicQuotient (f : ℝ → ℝ) (y : ℝ) : ℝ :=
  if y = 0 then iteratedDeriv 3 f 0 / 6 else f y / y ^ 3

def CubicDivisionTarget : Prop :=
  ∀ s : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ f : ℝ → ℝ,
    ContDiff ℝ ∞ f → f 0 = 0 → deriv f 0 = 0 → iteratedDeriv 2 f 0 = 0 →
      ContDiffOn ℝ ∞ (cubicQuotient f) (Icc (0 : ℝ) 1) ∧
      eLpNorm (iteratedDeriv s (cubicQuotient f)) 2 (volume.restrict (Ioo (0 : ℝ) 1)) ≤
        ENNReal.ofReal C *
          eLpNorm (iteratedDeriv (s + 3) f) 2 (volume.restrict (Ioo (0 : ℝ) 1))

/-- Value and conormal transmission are used together with the actual
equation and one smoothly matching source. They alone do not imply higher jets. -/
def PhysicalTransmissionTarget : Prop :=
  ∀ (a r0 b : ℝ) (L : SymmetricCoefficients) (f u v : PolarPoint → ℝ),
    a < r0 → r0 < b → ContDiff ℝ ∞ L.a → ContDiff ℝ ∞ L.b → ContDiff ℝ ∞ L.c →
    ContDiff ℝ ∞ f → ContDiff ℝ ∞ u → ContDiff ℝ ∞ v →
    (∀ p ∈ Ioo a b ×ˢ univ, 0 < L.a p) →
    (∀ p ∈ Ioo a r0 ×ˢ univ, divergenceOperator L u p = f p) →
    (∀ p ∈ Ioo r0 b ×ˢ univ, divergenceOperator L v p = f p) →
    (∀ θ, u (r0, θ) = v (r0, θ)) →
    (∀ θ, L.a (r0, θ) * radialPartial u (r0, θ) + L.b (r0, θ) * angularPartial u (r0, θ) =
      L.a (r0, θ) * radialPartial v (r0, θ) + L.b (r0, θ) * angularPartial v (r0, θ)) →
    (∀ i j : ℕ, ∀ θ, mixedDerivative i j u (r0, θ) = mixedDerivative i j v (r0, θ)) ∧
    ContDiffOn ℝ ∞ (fun p : PolarPoint => if p.1 ≤ r0 then u p else v p)
      (Ioo a b ×ˢ univ)

structure CanonicalData (S : PhysicalSpacesData) where
  left : ℕ → ℝ
  right : ℕ → ℝ
  physicalLeft : ℕ → ℝ
  physicalRight : ℕ → ℝ
  /-- Actual physical pieces; the radial endpoint fields describe their reference state. -/
  physicalDomain : (AnnularState S × ℝ) → ℕ → Set PolarPoint
  cell : ℕ → ℕ
  positive : ℕ → Bool
  chart : AnnularState S × ℝ → ℕ → PolarPoint → PolarPoint
  inverseChart : AnnularState S × ℝ → ℕ → PolarPoint → PolarPoint
  height : AnnularState S × ℝ → ℕ → PolarPoint → ℝ
  coefficients : AnnularState S × ℝ → ℕ → SymmetricCoefficients
  potential : AnnularState S × ℝ → ℕ → PolarPoint → ℝ
  dividedDifference : AnnularState S × ℝ → ℕ → SymmetricCoefficients
  cutPair : ℕ → ℕ × ℕ
  cutRadius : ℕ → ℝ
  normalizationRegion : Set ℝ

def canonicalOpen (S : PhysicalSpacesData) (K : CanonicalData S) (m : ℕ) : Set PolarPoint :=
  Ioo (K.left m) (K.right m) ×ˢ univ

def referencePhysicalPieceOpen (S : PhysicalSpacesData) (K : CanonicalData S)
    (m : ℕ) : Set PolarPoint :=
  Ioo (K.physicalLeft m) (K.physicalRight m) ×ˢ univ

def physicalPieceOpen (S : PhysicalSpacesData) (K : CanonicalData S)
    (z : AnnularState S × ℝ) (m : ℕ) : Set PolarPoint :=
  K.physicalDomain z m

def physicalPieceClosed (S : PhysicalSpacesData) (K : CanonicalData S)
    (z : AnnularState S × ℝ) (m : ℕ) : Set PolarPoint :=
  closure (physicalPieceOpen S K z m)

def canonicalClosed (S : PhysicalSpacesData) (K : CanonicalData S)
    (m : ℕ) : Set PolarPoint :=
  Icc (K.left m) (K.right m) ×ˢ univ

/-- The physical cut is the actual left inverse image of the fixed canonical boundary. -/
def canonicalCutPoint (S : PhysicalSpacesData) (K : CanonicalData S)
    (z : AnnularState S × ℝ) (m : ℕ) (θ : ℝ) : PolarPoint :=
  K.inverseChart z (K.cutPair m).1 (K.cutRadius m, θ)

def canonicalHeight (S : PhysicalSpacesData) (K : CanonicalData S)
    (z : AnnularState S × ℝ) (m : ℕ) (u : PolarPoint → ℝ) (p : PolarPoint) : ℝ :=
  u (K.inverseChart z m p) / K.height z m (K.inverseChart z m p)

def canonicalSource (S : PhysicalSpacesData) (K : CanonicalData S)
    (z : AnnularState S × ℝ) (m : ℕ) (f : PolarPoint → ℝ) (p : PolarPoint) : ℝ :=
  let x := K.inverseChart z m p
  K.height z m x * f x / |planeJacobian (K.chart z m) x|

def canonicalOperator (S : PhysicalSpacesData) (K : CanonicalData S)
    (L : ReturnCorrectionData S) (z : AnnularState S × ℝ) (m : ℕ)
    (W : PolarPoint → ℝ) (p : PolarPoint) : ℝ :=
  let f := divergenceOperator (L.coefficients z)
    (fun x => K.height z m x * W (K.chart z m x))
  (if K.positive m then -1 else (1 : ℝ)) * canonicalSource S K z m f p

/-! ## Primitive estimates retained by the actual coordinate construction

These are fields of the geometry, independent of every physical source or
unknown. The normalized density contains the actual cell weight; the
coordinate derivatives refer to actual chart and inverse-chart maps.
-/

/-- The angular column of the inverse of an actual planar derivative. -/
def canonicalInverseAngularVector (Ψ : PolarPoint → PolarPoint)
    (x : PolarPoint) : PolarPoint :=
  (-(fderiv ℝ Ψ x (0, 1)).1 / planeJacobian Ψ x,
    (fderiv ℝ Ψ x (1, 0)).1 / planeJacobian Ψ x)

/-- The actual physical-to-material Jacobian density. -/
def canonicalMaterialJacobian {S : PhysicalSpacesData} (T : MaterialData)
    (K : CanonicalData S) (z : AnnularState S × ℝ) (m : ℕ) (x : PolarPoint) : ℝ :=
  T.ell x.1 * |planeJacobian (K.chart z m) x|

def canonicalMaterialHeightRatio {S : PhysicalSpacesData} (T : MaterialData)
    (K : CanonicalData S) (m : ℕ) (x : PolarPoint) : ℝ :=
  T.H x.1 / T.H (T.sample (K.cell m))

/-- The common half-density normalization for every material coefficient. -/
def canonicalMaterialNormalizer {S : PhysicalSpacesData} (T : MaterialData)
    (K : CanonicalData S) (z : AnnularState S × ℝ) (m : ℕ) (β : ℝ)
    (x : PolarPoint) : ℝ :=
  Real.sqrt (canonicalMaterialJacobian T K z m x) *
    canonicalMaterialHeightRatio T K m x ^ β

/-- The reference physical point having the same canonical coordinates. -/
def canonicalReferencePoint {S : PhysicalSpacesData}
    (C : NonlinearGeometryData S) (K : CanonicalData S)
    (z : AnnularState S × ℝ) (m : ℕ) (x : PolarPoint) : PolarPoint :=
  K.inverseChart (C.referenceState, 0) m (K.chart z m x)

/-- The actual transition from a reference physical piece to the current one. -/
def canonicalCurrentPoint {S : PhysicalSpacesData}
    (C : NonlinearGeometryData S) (K : CanonicalData S)
    (z : AnnularState S × ℝ) (m : ℕ) (y : PolarPoint) : PolarPoint :=
  K.inverseChart z m (K.chart (C.referenceState, 0) m y)

def canonicalReferenceHeightRatio {S : PhysicalSpacesData}
    (C : NonlinearGeometryData S) (K : CanonicalData S)
    (z : AnnularState S × ℝ) (m : ℕ) (x : PolarPoint) : ℝ :=
  K.height (C.referenceState, 0) m (canonicalReferencePoint C K z m x) /
    K.height z m x

def canonicalReferenceSourceFactor {S : PhysicalSpacesData}
    (C : NonlinearGeometryData S) (K : CanonicalData S)
    (z : AnnularState S × ℝ) (m : ℕ) (x : PolarPoint) : ℝ :=
  K.height (C.referenceState, 0) m (canonicalReferencePoint C K z m x) /
    |planeJacobian (K.chart (C.referenceState, 0) m)
      (canonicalReferencePoint C K z m x)|

/-- Current inverse-angular direction, then transported reference radial
and angular directions. These are genuine derivatives of the stored maps. -/
def canonicalPrimitiveDirection {S : PhysicalSpacesData}
    (C : NonlinearGeometryData S) (K : CanonicalData S)
    (z : AnnularState S × ℝ) (m : ℕ) (i : Fin 3) (x : PolarPoint) : PolarPoint :=
  if i = 0 then canonicalInverseAngularVector (K.chart z m) x else
    fderiv ℝ (canonicalCurrentPoint C K z m)
      (canonicalReferencePoint C K z m x) (if i = 1 then (1, 0) else (0, 1))

/-- Nine direction fields, three normalized initial factors, and three
reference differential multipliers. No recursively expanded coefficient
or variable physical function is part of this index type. -/
abbrev CanonicalPrimitiveIndex := (Fin 3 × Fin 3) ⊕ (Fin 3 ⊕ Fin 3)

def canonicalPrimitiveField (D : ReferenceData) (T : MaterialData)
    {S : PhysicalSpacesData} (C : NonlinearGeometryData S) (K : CanonicalData S)
    (z : AnnularState S × ℝ) (m : ℕ) : CanonicalPrimitiveIndex → PolarPoint → ℝ
  | Sum.inl (i, j), x =>
      let Y := canonicalPrimitiveDirection C K z m i
      if j = 0 then (Y x).1 / T.ell x.1 else if j = 1 then (Y x).2 else
        -((Y x).1 * radialPartial (canonicalMaterialJacobian T K z m) x +
          (Y x).2 * angularPartial (canonicalMaterialJacobian T K z m) x) /
            (2 * canonicalMaterialJacobian T K z m x)
  | Sum.inr (Sum.inl i), x =>
      canonicalMaterialNormalizer T K z m (3 / 4 : ℝ) x *
        (if i = 0 then K.height z m x / |planeJacobian (K.chart z m) x|
         else if i = 1 then (K.height z m x)⁻¹
         else canonicalReferenceHeightRatio C K z m x)
  | Sum.inr (Sum.inr i), x =>
      let r := (canonicalReferencePoint C K z m x).1
      canonicalReferenceSourceFactor C K z m x *
        (if i = 0 then deriv D.w r else if i = 1 then D.w r else deriv D.w r / r)

/-- Primitive geometric information retained on the same neighborhood as
the charts. Finite polynomial state dependence is sufficient because N07b
uses one fixed angular order and may raise the low neighborhood order.

The transition maps are independent of the physical field. Their C3
matching is finite: arbitrary normal jets of adjacent charts are not
required to agree. All higher estimates are on the actual open pieces.
Neither canonical-space membership nor an inverse bound is a field here. -/
structure CanonicalPrimitiveGeometry (D : ReferenceData) (T : MaterialData)
    (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (L : ReturnCorrectionData S) (K : CanonicalData S)
    (base : ℕ) (ε : ℝ) : Prop where
  materialJets : ∀ N : ℕ, ∃ r d : ℕ, ∃ C₀ A : ℝ, 0 < C₀ ∧ 0 ≤ A ∧
    ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      ∀ (m : ℕ) (y : PolarPoint), (T.radius y.1, y.2) ∈ physicalPieceOpen S K z m →
        ∀ i : CanonicalPrimitiveIndex, ∀ k : ℕ, k ≤ N →
          ‖iteratedFDeriv ℝ k
            (fun v : PolarPoint => canonicalPrimitiveField D T C K z m i
              (T.radius v.1, v.2)) y‖ ≤
            C₀ * T.E0 (T.radius y.1) ^ A *
              (1 + stateGrading S r (z.1 - C.referenceState) + |z.2|) ^ d
  transport : ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
    ∃ τ : PolarPoint → PolarPoint, ∃ q : PolarPoint → ℝ,
      ContDiffOn ℝ 3 τ (annularOpen D) ∧ ContDiffOn ℝ 3 q (annularOpen D) ∧
      MapsTo τ (annularOpen D) (annularOpen D) ∧
      (∀ p, τ (p + (0, Real.pi)) = τ p + (0, Real.pi)) ∧
      Function.Periodic q (0, Real.pi) ∧
      (∀ p, τ (p.1, -p.2) = ((τ p).1, -(τ p).2)) ∧
      (∀ r θ, q (r, -θ) = q (r, θ)) ∧
      (∀ m, ∀ p ∈ referencePhysicalPieceOpen S K m,
        τ p = canonicalCurrentPoint C K z m p ∧
          q p = K.height (C.referenceState, 0) m p / K.height z m (τ p)) ∧
      ∃ C₀ A : ℝ, 0 < C₀ ∧ 0 ≤ A ∧
        (∀ p ∈ annularOpen D, ∀ n : ℕ, n ≤ 2 →
          ‖iteratedFDeriv ℝ n q p‖ ≤ C₀ * T.M p.1 ^ A) ∧
        (∀ p ∈ annularOpen D, ∀ n : ℕ, 1 ≤ n → n ≤ 2 →
          ‖iteratedFDeriv ℝ n τ p‖ ≤ C₀ * T.M p.1 ^ A) ∧
        (∀ p ∈ annularOpen D,
          T.H (τ p).1 / T.H p.1 ≤ C₀ * T.E0 p.1 ^ A) ∧
        (∀ p ∈ annularOpen D,
          T.M (τ p).1 / T.M p.1 ≤ C₀ * T.E0 p.1 ^ A)
  physicalCoefficients : ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
    ContDiffOn ℝ ∞ (L.coefficients z).a (annularOpen D) ∧
    ContDiffOn ℝ ∞ (L.coefficients z).b (annularOpen D) ∧
    ContDiffOn ℝ ∞ (L.coefficients z).c (annularOpen D) ∧
    (∀ r ∈ radialCore D,
      Function.Periodic (fun θ => (L.coefficients z).b (r, θ)) Real.pi) ∧
    (∀ r ∈ radialCore D,
      Function.Periodic (fun θ => (L.coefficients z).c (r, θ)) Real.pi)

/-- A stored inverse agrees on a full neighborhood with a genuine local inverse.
This fixes the boundary jets used by the canonical transmission equation. -/
def CanonicalBoundaryInverseGerm
    (F G : PolarPoint → PolarPoint) (p : PolarPoint) : Prop :=
  ∃ e : OpenPartialHomeomorph PolarPoint PolarPoint,
    (e : PolarPoint → PolarPoint) = F ∧ p ∈ e.source ∧
      ContDiffAt ℝ ∞ e.symm (F p) ∧ G =ᶠ[𝓝 (F p)] e.symm

/-- Geometric data on the actual state-dependent physical pieces.
The reference endpoint fields retain their radial meaning; artificial
negative cuts may move as curves under the actual travel coordinates. -/
structure CanonicalGeometry (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (K : CanonicalData S)
    (base : ℕ) (ε : ℝ) : Prop where
  normalizationOpen : IsOpen K.normalizationRegion
  normalizationSupport : Function.support (referenceColumn D) ⊆ K.normalizationRegion
  normalization : ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 → ∀ m,
    physicalPieceOpen S K z m ∩ (K.normalizationRegion ×ˢ univ) =
      physicalPieceOpen S K (C.referenceState, 0) m ∩ (K.normalizationRegion ×ˢ univ) ∧
    ∀ p ∈ physicalPieceOpen S K z m, p.1 ∈ K.normalizationRegion →
      K.chart z m p = K.chart (C.referenceState, 0) m p ∧
      K.height z m p = K.height (C.referenceState, 0) m p
  referenceBounds : ∀ m,
    K.physicalLeft m < K.physicalRight m ∧ K.left m < K.right m ∧
      Ioo (K.physicalLeft m) (K.physicalRight m) ⊆ Ioo D.a D.b
  referencePositive : ∀ m, K.positive m = true →
    ∀ r ∈ Ioo (K.physicalLeft m) (K.physicalRight m), 0 < deriv D.w r
  referenceNegative : ∀ m, K.positive m = false →
    ∀ r ∈ Ioo (K.physicalLeft m) (K.physicalRight m), deriv D.w r < 0
  referencePartition : ∃ E : Set ℝ, volume E = 0 ∧ ∀ r ∈ Ioo D.a D.b \ E,
    ∃! m, r ∈ Ioo (K.physicalLeft m) (K.physicalRight m)
  referenceDomain : ∀ m, physicalPieceOpen S K (C.referenceState, 0) m =
    referencePhysicalPieceOpen S K m
  domains : ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 → ∀ m,
    let Ω := physicalPieceOpen S K z m
    IsOpen Ω ∧ Ω.Nonempty ∧ Ω ⊆ annularOpen D ∧
    (∀ p : PolarPoint, p + (0, Real.pi) ∈ Ω ↔ p ∈ Ω) ∧
    (∀ p : PolarPoint, (p.1, -p.2) ∈ Ω ↔ p ∈ Ω) ∧
    (K.positive m = true → Ω = referencePhysicalPieceOpen S K m) ∧
    (∀ p ∈ Ω, K.positive m = true → 0 < deriv D.w p.1) ∧
    (∀ p ∈ Ω, K.positive m = false → deriv D.w p.1 < 0)
  partition : ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
    ∃ E : Set PolarPoint, volume E = 0 ∧ ∀ p ∈ annularOpen D \ E,
      ∃! m, p ∈ physicalPieceOpen S K z m
  charts : ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 → ∀ m,
    MapsTo (K.chart z m) (physicalPieceOpen S K z m) (canonicalOpen S K m) ∧
    MapsTo (K.inverseChart z m) (canonicalOpen S K m) (physicalPieceOpen S K z m) ∧
    (∀ p ∈ physicalPieceOpen S K z m, K.inverseChart z m (K.chart z m p) = p) ∧
    (∀ p ∈ canonicalOpen S K m, K.chart z m (K.inverseChart z m p) = p) ∧
    ContDiffOn ℝ ∞ (K.chart z m) (physicalPieceOpen S K z m) ∧
    ContDiffOn ℝ ∞ (K.inverseChart z m) (canonicalOpen S K m) ∧
    ContDiffOn ℝ ∞ (K.height z m) (physicalPieceOpen S K z m) ∧
    (∀ p ∈ physicalPieceOpen S K z m,
      0 < K.height z m p ∧ planeJacobian (K.chart z m) p ≠ 0 ∧
      K.chart z m (p + (0, Real.pi)) = K.chart z m p + (0, Real.pi) ∧
      K.height z m (p + (0, Real.pi)) = K.height z m p)
  boundary : ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 → ∀ m,
    MapsTo (K.chart z m) (physicalPieceClosed S K z m) (canonicalClosed S K m) ∧
    MapsTo (K.inverseChart z m) (canonicalClosed S K m) (physicalPieceClosed S K z m) ∧
    (∀ p ∈ physicalPieceClosed S K z m, K.inverseChart z m (K.chart z m p) = p) ∧
    (∀ p ∈ canonicalClosed S K m, K.chart z m (K.inverseChart z m p) = p) ∧
    (∀ p ∈ physicalPieceClosed S K z m,
      ContDiffAt ℝ ∞ (K.chart z m) p ∧ ContDiffAt ℝ ∞ (K.height z m) p ∧
        planeJacobian (K.chart z m) p ≠ 0 ∧ 0 < K.height z m p) ∧
    (∀ p ∈ frontier (physicalPieceOpen S K z m),
      CanonicalBoundaryInverseGerm (K.chart z m) (K.inverseChart z m) p)
  reflection : ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 → ∀ m,
    ∀ p ∈ physicalPieceOpen S K z m,
      K.chart z m (p.1, -p.2) = ((K.chart z m p).1, -(K.chart z m p).2) ∧
      K.height z m (p.1, -p.2) = K.height z m p ∧
      planeJacobian (K.chart z m) (p.1, -p.2) = planeJacobian (K.chart z m) p
  inverseReflection : ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 → ∀ m,
    ∀ p ∈ canonicalOpen S K m,
      K.inverseChart z m (p.1, -p.2) =
        ((K.inverseChart z m p).1, -(K.inverseChart z m p).2)

/-- The paired reference pieces have the actual component endpoints and
one fixed positive canonical radius. -/
def CanonicalReferenceCutPairs (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (K : CanonicalData S) : Prop :=
  (∀ m,
    K.positive (K.cutPair m).1 = false ∧ K.positive (K.cutPair m).2 = false ∧
    K.physicalLeft (K.cutPair m).1 = C.left m ∧
    K.physicalRight (K.cutPair m).2 = C.right m ∧
    K.physicalRight (K.cutPair m).1 = K.physicalLeft (K.cutPair m).2 ∧
    0 < K.cutRadius m ∧ K.left (K.cutPair m).1 = 0 ∧ K.left (K.cutPair m).2 = 0 ∧
    K.right (K.cutPair m).1 = K.cutRadius m ∧ K.right (K.cutPair m).2 = K.cutRadius m)

/-- Both actual negative halves meet along the same genuine inverse-chart
curve, cover their component off that curve, and retain the true root circles. -/
def CanonicalCurrentCutPair (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (K : CanonicalData S) (z : AnnularState S × ℝ) (m : ℕ) : Prop :=
  let iL := (K.cutPair m).1
  let iR := (K.cutPair m).2
  let R := K.cutRadius m
  let ΩL := physicalPieceOpen S K z iL
  let ΩR := physicalPieceOpen S K z iR
  let Γ := canonicalCutPoint S K z m
  let N := Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ)
  (∀ θ, K.inverseChart z iR (R, θ) = Γ θ) ∧
  Set.range Γ ⊆ N ∧ Disjoint ΩL ΩR ∧ ΩL ∪ ΩR = N \ Set.range Γ ∧
  K.inverseChart z iL '' ({(0 : ℝ)} ×ˢ (univ : Set ℝ)) =
    ({C.left m} ×ˢ (univ : Set ℝ)) ∧
  K.inverseChart z iR '' ({(0 : ℝ)} ×ˢ (univ : Set ℝ)) =
    ({C.right m} ×ˢ (univ : Set ℝ))

/-- Reference cut metadata and current two-dimensional cut geometry. -/
def CanonicalCutGeometry (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (K : CanonicalData S) (base : ℕ) (ε : ℝ) : Prop :=
  CanonicalReferenceCutPairs S C K ∧
    ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      ∀ m, CanonicalCurrentCutPair S C K z m

/-- Cut geometry and the unchanged actual canonical operator identities. -/
def CanonicalCutOperatorProperties (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (L : ReturnCorrectionData S) (K : CanonicalData S) (base : ℕ) (ε : ℝ) : Prop :=
  let U := stateNeighborhood S C base ε
  CanonicalCutGeometry S C K base ε ∧
  (∀ z ∈ U, stateSector S z.1 → ∀ u : PolarPoint → ℝ, ContDiff ℝ ∞ u → ∀ m θ,
    let Wl := canonicalHeight S K z (K.cutPair m).1 u
    let Wr := canonicalHeight S K z (K.cutPair m).2 u
    Wr (K.cutRadius m, θ) = Wl (K.cutRadius m, θ) ∧
    radialPartial Wr (K.cutRadius m, θ) =
      -radialPartial Wl (K.cutRadius m, θ) - Wl (K.cutRadius m, θ) / (2 * K.cutRadius m)) ∧
  (∀ z ∈ U, stateSector S z.1 → ∀ m W, ContDiff ℝ ∞ W → ∀ p ∈ canonicalOpen S K m,
    canonicalOperator S K L z m W p =
      (if K.positive m then -1 else (1 : ℝ)) *
        divergenceOperator (K.coefficients z m) W p + K.potential z m p * W p) ∧
  (∀ z ∈ U, stateSector S z.1 → ∀ m, K.positive m = false → ∀ p ∈ canonicalOpen S K m,
    (K.coefficients z m).a p = 1 ∧ (K.coefficients z m).b p = 0 ∧
    (K.coefficients z m).c p = -p.1) ∧
  (∀ z ∈ U, stateSector S z.1 → ∀ m, K.positive m = true → ∀ p ∈ canonicalOpen S K m,
    let d := (p.1 - K.left m) * (K.right m - p.1)
    (K.coefficients z m).a p - (K.coefficients (C.referenceState, 0) m).a p =
      d ^ 3 * (K.dividedDifference z m).a p ∧
    (K.coefficients z m).b p - (K.coefficients (C.referenceState, 0) m).b p =
      d ^ 3 * (K.dividedDifference z m).b p ∧
    (K.coefficients z m).c p - (K.coefficients (C.referenceState, 0) m).c p =
      d ^ 3 * (K.dividedDifference z m).c p)

/-- Actual physical/canonical source pairing on the current physical domain. -/
def CanonicalSourcePairing (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (K : CanonicalData S)
    (base : ℕ) (ε : ℝ) : Prop :=
  let U := stateNeighborhood S C base ε
  (∀ z ∈ U, stateSector S z.1 → ∀ m u f, ContDiff ℝ ∞ u → ContDiff ℝ ∞ f →
    Function.Periodic u (0, Real.pi) → Function.Periodic f (0, Real.pi) →
    HasCompactRadialSupport D u → HasCompactRadialSupport D f →
    (∫ p in physicalPieceOpen S K z m ∩ (univ ×ˢ Ioc (0 : ℝ) Real.pi), u p * f p) =
      ∫ p in canonicalOpen S K m ∩ (univ ×ˢ Ioc (0 : ℝ) Real.pi),
        canonicalHeight S K z m u p * canonicalSource S K z m f p)

/-- The same geometry and operator predicates used by the blueprint,
together with the quantitative bounds and actual source pairing. -/
def N04Properties (D : ReferenceData) (T : MaterialData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (L : ReturnCorrectionData S)
    (K : CanonicalData S) (base loss : ℕ) (ε : ℝ) : Prop :=
  let U := stateNeighborhood S C base ε
  CanonicalGeometry D S C K base ε ∧
  CanonicalCutOperatorProperties S C L K base ε ∧
  (∀ s : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ z ∈ U, ∀ m p,
    p ∈ canonicalOpen S K m → ∀ a b : ℕ, a + b ≤ s →
      |mixedDerivative a b (K.potential z m) p| +
      |mixedDerivative a b (K.dividedDifference z m).a p| +
      |mixedDerivative a b (K.dividedDifference z m).b p| +
      |mixedDerivative a b (K.dividedDifference z m).c p| ≤
        B * T.E0 (T.sample (K.cell m)) ^ B *
          (1 + stateGrading S (s + loss) (z.1 - C.referenceState) + |z.2|)) ∧
  CanonicalSourcePairing D S C K base ε

/-- The coordinate stage retains the three independent calculus targets as
well as every preceding property on the same final neighborhood. -/
def NonlinearPropertiesThrough04 (D : ReferenceData) (T : MaterialData)
    (S : PhysicalSpacesData) (C : NonlinearGeometryData S) (R : ReturnEquationData S)
    (L : ReturnCorrectionData S) (K : CanonicalData S)
    (base loss : ℕ) (ε : ℝ) : Prop :=
  NonlinearPropertiesThrough03 D T S C R L base loss ε ∧
    RootCompositionTarget ∧ CubicDivisionTarget ∧ PhysicalTransmissionTarget ∧
      N04Properties D T S C L K base loss ε ∧
        CanonicalPrimitiveGeometry D T S C L K base ε

/-- N04 includes the independently precise root-composition and cubic-division
targets and actual coordinate/source formulas; §7 lines 462--715. -/
def N04Statement : Prop :=
  ∃ A : RadialReference, ∃ T : MaterialData, ∃ S : PhysicalSpacesData,
    ∃ C : NonlinearGeometryData S, ∃ R : ReturnEquationData S,
      ∃ L : ReturnCorrectionData S, ∃ K : CanonicalData S,
        ∃ base loss : ℕ, ∃ ε : ℝ,
          IsMaterialData A.val T ∧ IsPhysicalSpaces A.val T S ∧
            NonlinearPropertiesThrough04 A.val T S C R L K base loss ε

/-! ## Actual finite-order canonical source spaces and a common graph domain -/

def canonicalMeasure (S : PhysicalSpacesData) (K : CanonicalData S) (m : ℕ) : Measure PolarPoint :=
  volume.restrict (Ioo (K.left m) (K.right m) ×ˢ Ioc (0 : ℝ) Real.pi)

abbrev CanonicalL2 (S : PhysicalSpacesData) (K : CanonicalData S) (m : ℕ) :=
  Lp ℝ 2 (canonicalMeasure S K m)
abbrev CanonicalSequence (S : PhysicalSpacesData) (K : CanonicalData S) :=
  ∀ m, CanonicalL2 S K m
abbrev CanonicalL2Sequence (S : PhysicalSpacesData) (K : CanonicalData S) :=
  lp (fun m => CanonicalL2 S K m) 2
abbrev CanonicalVolumeJets (S : PhysicalSpacesData) (K : CanonicalData S) (s : ℕ) :=
  lp (fun m => PiLp 2 (fun _ : Fin (s + 1) => CanonicalL2 S K m)) 2

def CanonicalTest (S : PhysicalSpacesData) (K : CanonicalData S) (m : ℕ)
    (φ : PolarPoint → ℝ) : Prop :=
  ContDiff ℝ ∞ φ ∧ Function.Periodic φ (0, Real.pi) ∧
  ∃ J : Set ℝ, IsCompact J ∧ J ⊆ Ioo (K.left m) (K.right m) ∧
    ∀ r, r ∉ J → ∀ θ, φ (r, θ) = 0

def WeakCanonicalAngularDerivative (S : PhysicalSpacesData) (K : CanonicalData S)
    (m : ℕ) (f g : CanonicalL2 S K m) (j : ℕ) : Prop :=
  ∀ φ, CanonicalTest S K m φ →
    (∫ p, g p * φ p ∂canonicalMeasure S K m) =
      (-1 : ℝ) ^ j * ∫ p, f p * mixedDerivative 0 j φ p ∂canonicalMeasure S K m

def canonicalVolumeGraph (S : PhysicalSpacesData) (K : CanonicalData S)
    (s : ℕ) : Set (CanonicalVolumeJets S K s) :=
  {v | (∀ m, (fun p : PolarPoint => v m 0 (p.1, Real.pi - p.2))
      =ᵐ[canonicalMeasure S K m] (v m 0 : PolarPoint → ℝ)) ∧
    ∀ m j, WeakCanonicalAngularDerivative S K m (v m 0) (v m j) j.val}

structure VolumeModelData (S : PhysicalSpacesData) (K : CanonicalData S) where
  level : ℝ → ℝ → ∀ s, Submodule ℝ (CanonicalVolumeJets S K s)
  forget : ∀ γ t s, level γ t s →ₗ[ℝ] CanonicalSequence S K

def IsVolumeModel (T : MaterialData) (S : PhysicalSpacesData) (K : CanonicalData S)
    (V : VolumeModelData S K) : Prop :=
  (∀ γ t s, (V.level γ t s : Set (CanonicalVolumeJets S K s)) = canonicalVolumeGraph S K s) ∧
  (∀ γ t s, IsClosed (V.level γ t s : Set (CanonicalVolumeJets S K s))) ∧
  (∀ γ t s, Function.Injective (V.forget γ t s)) ∧
  (∀ γ t s v m,
    V.forget γ t s v m =
      (T.M (T.sample (K.cell m)) ^ (-t) * T.H (T.sample (K.cell m)) ^ γ) •
        (v.val m 0))

def VolumeMember (S : PhysicalSpacesData) (K : CanonicalData S) (V : VolumeModelData S K)
    (γ t : ℝ) (s : ℕ) (f : CanonicalSequence S K) : Prop :=
  ∃ F : V.level γ t s, V.forget γ t s F = f

abbrev CanonicalUnknown (S : PhysicalSpacesData) (K : CanonicalData S) :=
  CanonicalL2Sequence S K × (ℝ × ℝ × ℝ)

def canonicalUnknownScalars (S : PhysicalSpacesData) (K : CanonicalData S)
    (u : CanonicalUnknown S K) : ℝ := |u.2.1| + |u.2.2.1| + |u.2.2.2|

def HasCanonicalRepresentation (_D : ReferenceData) (S : PhysicalSpacesData)
    (_C : NonlinearGeometryData S) (K : CanonicalData S) (z : AnnularState S × ℝ)
    (U : CanonicalUnknown S K) (F : CanonicalSequence S K)
    (η f : PolarPoint → ℝ) : Prop :=
  (∀ m, (U.1 m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
    canonicalHeight S K z m (fun p => η p - U.2.1 * S.chiLeft p.1)) ∧
  (∀ m, (F m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m] canonicalSource S K z m f)

/-- The reference domain is pinned to the actual physical distributional
equation, natural endpoint class, normalization and source compatibility. -/
def ReferenceCanonicalRelation (D : ReferenceData) (_T : MaterialData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (K : CanonicalData S) (V : VolumeModelData S K)
    (γ M0 M1 loss : ℝ) (U : CanonicalUnknown S K) (F : CanonicalSequence S K) : Prop :=
  VolumeMember S K V (3 / 4 : ℝ) (-loss) 0 (fun m => U.1 m) ∧
  ∃ η f : PolarPoint → ℝ,
    HasCanonicalRepresentation D S C K (C.referenceState, 0) U F η f ∧
    ReferenceGraph D γ M0 M1 (η, U.2.2.1)
      ((fun p => f p - U.2.2.2 * (S.height (3 / 4 : ℝ)).decode S.psi p), 0)

structure CanonicalDomainData (S : PhysicalSpacesData) (K : CanonicalData S)
    (V : VolumeModelData S K) (b : ℕ) where
  weakExponent : ℝ
  sourceMaterial : ℝ
  outputMaterial : ℝ
  lossMaterial : ℝ
  graph : Submodule ℝ (CanonicalUnknown S K × V.level (3 / 4 : ℝ) 0 b)
  inverse : V.level (3 / 4 : ℝ) 0 b →L[ℝ] graph
  globalInverse : CanonicalSequence S K → CanonicalUnknown S K

abbrev CanonicalDomainData.Space {S K V b} (B : CanonicalDomainData S K V b) := B.graph

def N05Properties (D : ReferenceData) (T : MaterialData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (K : CanonicalData S) (V : VolumeModelData S K)
    (b : ℕ) (B : CanonicalDomainData S K V b) : Prop :=
  2 ≤ b ∧ IsVolumeModel T S K V ∧ 0 < B.weakExponent ∧ B.weakExponent < (3 / 4 : ℝ) ∧
  0 ≤ B.lossMaterial ∧ IsClosed (B.graph : Set (CanonicalUnknown S K × V.level (3 / 4 : ℝ) 0 b)) ∧
  (∀ u, u ∈ B.graph ↔ ReferenceCanonicalRelation D T S C K V B.weakExponent
    B.sourceMaterial B.outputMaterial B.lossMaterial u.1 (V.forget (3 / 4 : ℝ) 0 b u.2)) ∧
  (∀ F, (B.inverse F).val.2 = F) ∧ (∀ u : B.Space, B.inverse u.val.2 = u) ∧
  (∀ F, (B.inverse F).val.1 = B.globalInverse (V.forget (3 / 4 : ℝ) 0 b F)) ∧
  (∃ C0 : ℝ, 0 < C0 ∧ ∀ u : B.Space, ‖u‖ ≤ C0 * ‖u.val.2‖) ∧
  (∃ δ : ℝ, 0 < δ ∧ δ < (1 / 4 : ℝ) ∧ ∀ γ : ℝ,
    (γ = (3 / 4 : ℝ) - δ ∨ γ = (3 / 4 : ℝ) ∨ γ = (3 / 4 : ℝ) + δ) →
    ∀ t : ℝ, ∀ s : ℕ, ∃ C0 : ℝ, 0 < C0 ∧ ∀ F : V.level γ t s,
      ∃ W : V.level γ (t - B.lossMaterial) s,
        V.forget γ (t - B.lossMaterial) s W =
          (fun m => (B.globalInverse (V.forget γ t s F)).1 m) ∧
        ‖W‖ + canonicalUnknownScalars S K (B.globalInverse (V.forget γ t s F)) ≤ C0 * ‖F‖) ∧
  (∀ t : ℝ, ∀ s : ℕ, ∃ C0 : ℝ, 0 < C0 ∧ ∀ F : V.level (3 / 4 : ℝ) t s,
    ∃ W : V.level (3 / 4 : ℝ) (t - B.lossMaterial) s,
      V.forget (3 / 4 : ℝ) (t - B.lossMaterial) s W =
        (fun m => (B.globalInverse (V.forget (3 / 4 : ℝ) t s F)).1 m) ∧
      ‖W‖ + canonicalUnknownScalars S K (B.globalInverse (V.forget (3 / 4 : ℝ) t s F)) ≤ C0 * ‖F‖) ∧
  (∀ t : ℝ, ∀ s : ℕ, ∃ C0 : ℝ, 0 < C0 ∧ ∀ F : V.level (3 / 4 : ℝ) t (s + 1),
    ∃ W : V.level (3 / 4 : ℝ) (t - B.lossMaterial) s,
      (∀ m φ, CanonicalTest S K m φ →
        (∫ p, V.forget (3 / 4 : ℝ) (t - B.lossMaterial) s W m p * φ p
          ∂canonicalMeasure S K m) =
        -(∫ p, (B.globalInverse (V.forget (3 / 4 : ℝ) t (s + 1) F)).1 m p *
          mixedDerivative 1 0 φ p ∂canonicalMeasure S K m)) ∧ ‖W‖ ≤ C0 * ‖F‖)

/-- The source scale and physical graph use the preceding canonical charts. -/
def NonlinearPropertiesThrough05 (D : ReferenceData) (T : MaterialData)
    (S : PhysicalSpacesData) (C : NonlinearGeometryData S) (R : ReturnEquationData S)
    (L : ReturnCorrectionData S) (K : CanonicalData S) (Vol : VolumeModelData S K)
    (b : ℕ) (Domain : CanonicalDomainData S K Vol b)
    (base loss : ℕ) (ε : ℝ) : Prop :=
  NonlinearPropertiesThrough04 D T S C R L K base loss ε ∧
    N05Properties D T S C K Vol b Domain

/-- N05, §8 lines 14--171: a genuine canonical source scale and a complete
closed physical graph on the same construction; no inverse-image graph definition. -/
def N05Statement : Prop :=
  ∃ A : RadialReference, ∃ T : MaterialData, ∃ S : PhysicalSpacesData,
    ∃ C : NonlinearGeometryData S, ∃ R : ReturnEquationData S,
      ∃ L : ReturnCorrectionData S, ∃ K : CanonicalData S,
        ∃ Vol : VolumeModelData S K, ∃ b : ℕ,
          ∃ Domain : CanonicalDomainData S K Vol b,
            ∃ base loss : ℕ, ∃ ε : ℝ,
              IsMaterialData A.val T ∧ IsPhysicalSpaces A.val T S ∧
                NonlinearPropertiesThrough05 A.val T S C R L K Vol b Domain base loss ε

def nuColumnField (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (z : AnnularState S × ℝ) (p : PolarPoint) : ℝ :=
  deriv (fun ν => scalarResidualField D S C ((z.1.1, (ν, z.1.2.2)), z.2) p) z.1.2.1

/-- The physical weak equation uses the full angular period of `RadialTest`,
as does `ReferenceGraph`. The canonical source coordinates still use one
half-period for the half-periodic fields themselves. -/
def PerturbedCanonicalRelation (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (K : CanonicalData S) (L : ReturnCorrectionData S)
    (z : AnnularState S × ℝ) (U : CanonicalUnknown S K) (F : CanonicalSequence S K) : Prop :=
  ∃ η f : PolarPoint → ℝ,
    HasCanonicalRepresentation D S C K z U F η f ∧ referenceRow D η = 0 ∧
    ∀ φ, RadialTest D φ →
      (∫ r in D.a..D.b, radialAngularMean (fun θ =>
        η (r, θ) * divergenceOperator (L.coefficients z) φ (r, θ))) +
        U.2.2.1 * (∫ r in D.a..D.b, radialAngularMean (fun θ =>
          nuColumnField D S C z (r, θ) * φ (r, θ))) +
        U.2.2.2 * (∫ r in D.a..D.b, radialAngularMean (fun θ =>
          (S.height (3 / 4 : ℝ)).decode S.psi (r, θ) * φ (r, θ))) =
      ∫ r in D.a..D.b, radialAngularMean (fun θ => f (r, θ) * φ (r, θ))

structure RelativeInverseData (S : PhysicalSpacesData) (K : CanonicalData S)
    (V : VolumeModelData S K) (b : ℕ) (B : CanonicalDomainData S K V b) where
  operator : AnnularState S × ℝ → B.Space →L[ℝ] V.level (3 / 4 : ℝ) 0 b
  relative : AnnularState S × ℝ → V.level (3 / 4 : ℝ) 0 b →L[ℝ] V.level (3 / 4 : ℝ) 0 b
  inverse : AnnularState S × ℝ → V.level (3 / 4 : ℝ) 0 b →L[ℝ] V.level (3 / 4 : ℝ) 0 b

def N06Properties (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (K : CanonicalData S) (L : ReturnCorrectionData S) (V : VolumeModelData S K)
    (b : ℕ) (B : CanonicalDomainData S K V b) (P : RelativeInverseData S K V b B)
    (base : ℕ) (ε : ℝ) : Prop :=
  0 < ε ∧ ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
    (∀ u : B.Space, PerturbedCanonicalRelation D S C K L z u.val.1
      (V.forget (3 / 4 : ℝ) 0 b (P.operator z u))) ∧
    (∀ F, P.relative z F = P.operator z (B.inverse F) - F) ∧
    ‖P.relative z‖ < (1 / 2 : ℝ) ∧
    (∀ u : B.Space, P.operator z u = u.val.2 + P.relative z u.val.2) ∧
    (∀ F, P.inverse z (F + P.relative z F) = F ∧
      P.inverse z F + P.relative z (P.inverse z F) = F) ∧ ‖P.inverse z‖ ≤ 2

/-- The relative inverse acts on exactly the source and graph already chosen. -/
def NonlinearPropertiesThrough06 (D : ReferenceData) (T : MaterialData)
    (S : PhysicalSpacesData) (C : NonlinearGeometryData S) (R : ReturnEquationData S)
    (L : ReturnCorrectionData S) (K : CanonicalData S) (Vol : VolumeModelData S K)
    (b : ℕ) (Domain : CanonicalDomainData S K Vol b)
    (Relative : RelativeInverseData S K Vol b Domain)
    (base loss : ℕ) (ε : ℝ) : Prop :=
  NonlinearPropertiesThrough05 D T S C R L K Vol b Domain base loss ε ∧
    N06Properties D S C K L Vol b Domain Relative base ε

/-- N06: the first Neumann inverse is on precisely one Banach source space,
and all previous properties hold on this same chosen neighborhood. -/
def N06Statement : Prop :=
  ∃ A : RadialReference, ∃ T : MaterialData, ∃ S : PhysicalSpacesData,
    ∃ C : NonlinearGeometryData S, ∃ R : ReturnEquationData S,
      ∃ L : ReturnCorrectionData S, ∃ K : CanonicalData S,
        ∃ Vol : VolumeModelData S K, ∃ b : ℕ,
          ∃ Domain : CanonicalDomainData S K Vol b,
            ∃ Relative : RelativeInverseData S K Vol b Domain,
              ∃ base loss : ℕ, ∃ ε : ℝ,
                IsMaterialData A.val T ∧ IsPhysicalSpaces A.val T S ∧
                  NonlinearPropertiesThrough06 A.val T S C R L K Vol b Domain Relative
                    base loss ε

structure ScalarInverseData (S : PhysicalSpacesData) where
  G : AnnularState S × ℝ → S.Source →L[ℝ] (HeightPair S × ℝ)

def ScalarInverseProperties (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (L : ReturnCorrectionData S)
    (G : ScalarInverseData S) (base : ℕ) (ε : ℝ) : Prop :=
  let U := stateNeighborhood S C base ε
  (∀ z ∈ U, stateSector S z.1 → ∀ f : S.Source,
    referenceRow D (heightPairField S (G.G z f).1) = 0 ∧
    (∀ p ∈ annularOpen D,
      divergenceOperator (L.coefficients z) (heightPairField S (G.G z f).1) p +
        (G.G z f).2 * nuColumnField D S C z p =
          (S.height (3 / 4 : ℝ)).decode f.val p)) ∧
  (∀ z ∈ U, stateSector S z.1 → ∀ η : HeightPair S, ∀ μ : ℝ, ∀ f : S.Source,
    referenceRow D (heightPairField S η) = 0 →
    (∀ p ∈ annularOpen D, divergenceOperator (L.coefficients z) (heightPairField S η) p +
      μ * nuColumnField D S C z p = (S.height (3 / 4 : ℝ)).decode f.val p) →
      G.G z f = (η, μ)) ∧
  LinearFamilyTame (pairGrading (sectorGrading S) realGrading)
    (pairGrading (heightPairGrading S) realGrading) S.sourceGrading
    (sectorNeighborhood S base ε ε)
    (fun z => (G.G (liftSectorParameter S C z)).toLinearMap) ∧
  SmoothTameOn (pairGrading (pairGrading (sectorGrading S) realGrading) S.sourceGrading)
    (pairGrading (heightPairGrading S) realGrading) (sectorNeighborhood S base ε ε ×ˢ univ)
    (fun z : (StateDirections S × ℝ) × S.Source => G.G (liftSectorParameter S C z.1) z.2)

def ScalarBanachBridgeProperties (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (K : CanonicalData S) (V : VolumeModelData S K)
    (b : ℕ) (B : CanonicalDomainData S K V b) (P : RelativeInverseData S K V b B)
    (G : ScalarInverseData S) (base : ℕ) (ε : ℝ) : Prop :=
  ∃ s : ℕ, b ≤ s ∧ ∃ C0 : ℝ, 0 < C0 ∧
  ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 → ∀ f : S.Source,
    ∃ F : V.level (3 / 4 : ℝ) 0 b,
      ‖F‖ ≤ C0 * (1 + stateGrading S s (z.1 - C.referenceState) + |z.2|) *
        S.sourceGrading s f ∧
      (∀ m, (V.forget (3 / 4 : ℝ) 0 b F m : PolarPoint → ℝ)
        =ᵐ[canonicalMeasure S K m]
          canonicalSource S K z m ((S.height (3 / 4 : ℝ)).decode f.val)) ∧
      let d := B.inverse (P.inverse z F)
      d.val.1.2.2.2 = 0 ∧
      d.val.1.2.1 = (G.G z f).1.2 ∧ d.val.1.2.2.1 = (G.G z f).2 ∧
      HasCanonicalRepresentation D S C K z d.val.1 (V.forget (3 / 4 : ℝ) 0 b F)
        (heightPairField S (G.G z f).1) ((S.height (3 / 4 : ℝ)).decode f.val)

/-- The physical scalar inverse is explicitly the already chosen Banach solution,
including the vanishing compatibility scalar and the free left constant. -/
def NonlinearPropertiesThrough07 (D : ReferenceData) (T : MaterialData)
    (S : PhysicalSpacesData) (C : NonlinearGeometryData S) (R : ReturnEquationData S)
    (L : ReturnCorrectionData S) (K : CanonicalData S) (Vol : VolumeModelData S K)
    (b : ℕ) (Domain : CanonicalDomainData S K Vol b)
    (Relative : RelativeInverseData S K Vol b Domain) (G : ScalarInverseData S)
    (base loss : ℕ) (ε : ℝ) : Prop :=
  NonlinearPropertiesThrough06 D T S C R L K Vol b Domain Relative base loss ε ∧
    ScalarInverseProperties D S C L G base ε ∧
      ScalarBanachBridgeProperties D S C K Vol b Domain Relative G base ε

/-- N07: the same basic solution has all height orders and a smooth tame
inverse family; the left endpoint constant is retained in `HeightPair`. -/
def N07Statement : Prop :=
  ∃ A : RadialReference, ∃ T : MaterialData, ∃ S : PhysicalSpacesData,
    ∃ C : NonlinearGeometryData S, ∃ R : ReturnEquationData S,
      ∃ L : ReturnCorrectionData S, ∃ K : CanonicalData S,
        ∃ Vol : VolumeModelData S K, ∃ b : ℕ,
          ∃ Domain : CanonicalDomainData S K Vol b,
            ∃ Relative : RelativeInverseData S K Vol b Domain,
              ∃ G : ScalarInverseData S, ∃ base loss : ℕ, ∃ ε : ℝ,
                IsMaterialData A.val T ∧ IsPhysicalSpaces A.val T S ∧
                  NonlinearPropertiesThrough07 A.val T S C R L K Vol b Domain Relative G
                    base loss ε

/-! ## The actual joint residual and the second, control-space Neumann inverse -/

/-- Elements store the weighted coordinates H_m^(-beta) xi_m. -/
abbrev ControlBanach := lp (fun _ : ℕ => ℝ) 2

def controlGrading : ℕ → Seminorm ℝ ControlBanach := fun _ => normSeminorm ℝ ControlBanach

structure ControlColumnData (S : PhysicalSpacesData) where
  restriction : CircleSpace S →L[ℝ] ControlBanach
  heightColumn : AnnularState S × ℝ → ControlBanach →L[ℝ] S.Source
  nuColumn : AnnularState S × ℝ → S.Source
  heightRow : AnnularState S × ℝ → HeightPair S →L[ℝ] CircleSpace S
  circleColumn : AnnularState S × ℝ → CircleSpace S →L[ℝ] CircleSpace S
  J : AnnularState S × ℝ → ControlBanach →L[ℝ] ControlBanach
  JInverse : AnnularState S × ℝ → ControlBanach →L[ℝ] ControlBanach
  diagonal : AnnularState S × ℝ → ℕ → ℝ

def controlHeightResponse (S : PhysicalSpacesData) (B : ControlColumnData S)
    (G : ScalarInverseData S) (z : AnnularState S × ℝ) : ControlBanach →L[ℝ] HeightPair S :=
  (ContinuousLinearMap.fst ℝ (HeightPair S) ℝ).comp ((G.G z).comp (B.heightColumn z))

def controlMeanRow (S : PhysicalSpacesData) (B : ControlColumnData S)
    (z : AnnularState S × ℝ) : HeightPair S →L[ℝ] ControlBanach :=
  B.restriction.comp (B.heightRow z)

def controlFeedback (S : PhysicalSpacesData) (B : ControlColumnData S)
    (G : ScalarInverseData S) (z : AnnularState S × ℝ) : ControlBanach →L[ℝ] ControlBanach :=
  (B.JInverse z).comp ((controlMeanRow S B z).comp (controlHeightResponse S B G z))

def N08Properties (D : ReferenceData) (T : MaterialData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (R : ReturnEquationData S) (G : ScalarInverseData S)
    (P : ResidualData S) (B : ControlColumnData S) (base loss : ℕ) (ε : ℝ) : Prop :=
  let U := stateNeighborhood S C base ε
  IsClosed (stateSectorSubmodule S : Set (AnnularState S)) ∧
  IsOpen (sectorNeighborhood S base ε ε) ∧
  (∀ z ∈ U, stateSector S z.1 → ∀ p ∈ annularOpen D,
    (S.height (3 / 4 : ℝ)).decode (P.scalar z).val p = scalarResidualField D S C z p) ∧
  (∀ z ∈ U, stateSector S z.1 → (P.circle z).val = R.residual z) ∧
  jointResidual S P (C.referenceState, 0) = 0 ∧
  (∀ u m, B.restriction u m = T.H (T.sample m) ^ (-(3 / 4 : ℝ)) *
    angularMean ((S.circle (3 / 4 : ℝ)).decode u m)) ∧
  (∀ z ∈ U, stateSector S z.1 → ∀ p ∈ annularOpen D,
    (S.height (3 / 4 : ℝ)).decode (B.nuColumn z).val p = nuColumnField D S C z p) ∧
  (∀ z ∈ U,
    ContinuousFlexibility.Analysis.HasProjectiveLineDerivAt
      (fun x => P.scalar (x, z.2)) (B.nuColumn z) z.1 (0, (1, (0, 0)))) ∧
  (∀ z ∈ U, stateSector S z.1 → ∀ u : CircleSpace S,
    ContinuousFlexibility.Analysis.HasProjectiveLineDerivAt
      (fun x => P.scalar (x, z.2)) (B.heightColumn z (B.restriction u))
      z.1 (0, (0, (u, 0)))) ∧
  (∀ z ∈ U, stateSector S z.1 → ∀ η : HeightPair S,
    ContinuousFlexibility.Analysis.HasProjectiveLineDerivAt
      (fun x => (P.circle (x, z.2)).val) (z.2 • B.heightRow z η)
      z.1 (η, (0, (0, 0)))) ∧
  (∀ z ∈ U, stateSector S z.1 → ∀ u : CircleSpace S,
    ContinuousFlexibility.Analysis.HasProjectiveLineDerivAt
      (fun x => (P.circle (x, z.2)).val) (B.circleColumn z u)
      z.1 (0, (0, (u, 0)))) ∧
  (∀ z ∈ U, stateSector S z.1 → ∀ u, B.restriction (B.circleColumn z u) = B.J z (B.restriction u)) ∧
  (∀ z ∈ U, stateSector S z.1 → ∀ u m, B.J z u m = B.diagonal z m * u m) ∧
  (∀ m, B.diagonal (C.referenceState, 0) m = 1) ∧
  (∀ z ∈ U, stateSector S z.1 → ∀ u, B.JInverse z (B.J z u) = u ∧ B.J z (B.JInverse z u) = u) ∧
  (∀ z ∈ U, stateSector S z.1 → ∀ m, (1 / 2 : ℝ) ≤ |B.diagonal z m| ∧ |B.diagonal z m| ≤ 2) ∧
  (∀ s : ℕ, ∃ C0 : ℝ, 0 < C0 ∧ ∀ z ∈ U, ∀ u : ControlBanach,
    S.sourceGrading s (B.heightColumn z u) +
      heightPairGrading S s (G.G z (B.heightColumn z u)).1 +
      |(G.G z (B.heightColumn z u)).2| ≤
      C0 * (1 + stateGrading S (s + loss) (z.1 - C.referenceState) + |z.2|) * ‖u‖) ∧
  SmoothTameOn (pairGrading (sectorGrading S) realGrading) (residualGrading S)
    (sectorNeighborhood S base ε ε) (sectorJointResidual S C P) ∧
  SmoothTameOn (pairGrading (pairGrading (sectorGrading S) realGrading) controlGrading)
    S.sourceGrading (sectorNeighborhood S base ε ε ×ˢ univ)
    (fun z : (StateDirections S × ℝ) × ControlBanach =>
      B.heightColumn (liftSectorParameter S C z.1) z.2)

/-- The genuine residual and controls use the same scalar inverse and spaces. -/
def NonlinearPropertiesThrough08 (D : ReferenceData) (T : MaterialData)
    (S : PhysicalSpacesData) (C : NonlinearGeometryData S) (R : ReturnEquationData S)
    (L : ReturnCorrectionData S) (K : CanonicalData S) (Vol : VolumeModelData S K)
    (b : ℕ) (Domain : CanonicalDomainData S K Vol b)
    (Relative : RelativeInverseData S K Vol b Domain) (G : ScalarInverseData S)
    (Joint : ResidualData S) (Columns : ControlColumnData S)
    (base loss : ℕ) (ε : ℝ) : Prop :=
  NonlinearPropertiesThrough07 D T S C R L K Vol b Domain Relative G base loss ε ∧
    N08Properties D T S C R G Joint Columns base loss ε

/-- N08: actual scalar/circle residual, q=0, true nu/control derivatives,
and all component-weight smoothing; §9 lines 13--137. -/
def N08Statement : Prop :=
  ∃ A : RadialReference, ∃ T : MaterialData, ∃ S : PhysicalSpacesData,
    ∃ C : NonlinearGeometryData S, ∃ R : ReturnEquationData S,
      ∃ L : ReturnCorrectionData S, ∃ K : CanonicalData S,
        ∃ Vol : VolumeModelData S K, ∃ b : ℕ,
          ∃ Domain : CanonicalDomainData S K Vol b,
            ∃ Relative : RelativeInverseData S K Vol b Domain,
              ∃ G : ScalarInverseData S, ∃ Joint : ResidualData S,
                ∃ Columns : ControlColumnData S, ∃ base loss : ℕ, ∃ ε : ℝ,
                  IsMaterialData A.val T ∧ IsPhysicalSpaces A.val T S ∧
                    NonlinearPropertiesThrough08 A.val T S C R L K Vol b Domain Relative G
                      Joint Columns base loss ε

structure ControlInverseData (S : PhysicalSpacesData) where
  inverse : AnnularState S × ℝ → ControlBanach →L[ℝ] ControlBanach

def controlSolution (S : PhysicalSpacesData) (B : ControlColumnData S)
    (G : ScalarInverseData S) (N : ControlInverseData S)
    (z : AnnularState S × ℝ) (y : ResidualSpace S) : ControlBanach :=
  N.inverse z (B.JInverse z (B.restriction y.2.val -
    z.2 • controlMeanRow S B z (G.G z y.1).1))

def coupledNeighborhood (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (base : ℕ) (ε q0 : ℝ) : Set (AnnularState S × ℝ) :=
  {z | stateGrading S base (z.1 - C.referenceState) < ε ∧ |z.2| < q0}

def N09Properties (_D : ReferenceData) (_T : MaterialData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (R : ReturnEquationData S) (G : ScalarInverseData S)
    (B : ControlColumnData S) (N : ControlInverseData S) (V : CoupledInverseData S)
    (base : ℕ) (ε q0 : ℝ) : Prop :=
  0 < q0 ∧ q0 ≤ ε ∧
  let U := coupledNeighborhood S C base ε q0
  (∀ z ∈ U, stateSector S z.1 → ‖z.2 • controlFeedback S B G z‖ < (1 / 2 : ℝ)) ∧
  (∀ z ∈ U, stateSector S z.1 → ∀ u : ControlBanach,
    N.inverse z (u - z.2 • controlFeedback S B G z u) = u ∧
    N.inverse z u - z.2 • controlFeedback S B G z (N.inverse z u) = u) ∧
  (∀ z ∈ U, stateSector S z.1 → ∀ y : ResidualSpace S,
    let ξ := controlSolution S B G N z y
    let w := V.V z y
    let η := w.1
    let μ := w.2.1
    let κ := w.2.2.1
    let f := y.2.val - z.2 • B.heightRow z η - B.circleColumn z κ
    stateSector S w ∧ B.restriction κ = ξ ∧
    (η, μ) = G.G z y.1 - G.G z (B.heightColumn z ξ) ∧
    IsEvenZeroMeanCircle S f ∧
    w.2.2.2 = R.chartIncrement z (R.inverse f) ∧
    (S.circle (3 / 4 : ℝ)).decode (R.linearPart (R.inverse f)) =
      (S.circle (3 / 4 : ℝ)).decode f) ∧
  (∀ z ∈ sectorNeighborhood S base ε q0, ∀ y : ResidualSpace S,
    (V.sectorV z y).val = V.V (liftSectorParameter S C z) y) ∧
  SmoothTameOn (pairGrading (pairGrading (sectorGrading S) realGrading) (residualGrading S))
    (sectorGrading S) (sectorNeighborhood S base ε q0 ×ˢ univ)
    (fun z : (StateDirections S × ℝ) × ResidualSpace S => V.sectorV z.1 z.2)

/-- Both Neumann inverses, the recovered increments and the preceding scalar
bridge are attached to one common construction. -/
def NonlinearPropertiesThrough09 (D : ReferenceData) (T : MaterialData)
    (S : PhysicalSpacesData) (C : NonlinearGeometryData S) (R : ReturnEquationData S)
    (L : ReturnCorrectionData S) (K : CanonicalData S) (Vol : VolumeModelData S K)
    (b : ℕ) (Domain : CanonicalDomainData S K Vol b)
    (Relative : RelativeInverseData S K Vol b Domain) (G : ScalarInverseData S)
    (Joint : ResidualData S) (Columns : ControlColumnData S)
    (ControlInverse : ControlInverseData S) (Coupled : CoupledInverseData S)
    (base loss : ℕ) (ε q0 : ℝ) : Prop :=
  NonlinearPropertiesThrough08 D T S C R L K Vol b Domain Relative G Joint Columns
    base loss ε ∧ N09Properties D T S C R G Columns ControlInverse Coupled base ε q0

/-- N09: two-sided inversion of a bounded endomorphism of the same weighted
control Banach space, followed by all-order height/chart recovery; §9 139--181. -/
def N09Statement : Prop :=
  ∃ A : RadialReference, ∃ T : MaterialData, ∃ S : PhysicalSpacesData,
    ∃ C : NonlinearGeometryData S, ∃ R : ReturnEquationData S,
      ∃ L : ReturnCorrectionData S, ∃ K : CanonicalData S,
        ∃ Vol : VolumeModelData S K, ∃ b : ℕ,
          ∃ Domain : CanonicalDomainData S K Vol b,
            ∃ Relative : RelativeInverseData S K Vol b Domain,
              ∃ G : ScalarInverseData S, ∃ Joint : ResidualData S,
                ∃ Columns : ControlColumnData S, ∃ ControlInverse : ControlInverseData S,
                  ∃ Coupled : CoupledInverseData S, ∃ base loss : ℕ, ∃ ε q0 : ℝ,
                    IsMaterialData A.val T ∧ IsPhysicalSpaces A.val T S ∧
                      NonlinearPropertiesThrough09 A.val T S C R L K Vol b Domain Relative G
                        Joint Columns ControlInverse Coupled base loss ε q0

def residualErrorCoefficient (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (z : AnnularState S × ℝ) (p : PolarPoint) : ℝ :=
  polarTypeB (stateProfile D S C z.1) (stateHeight D S C z) p

def N10Properties (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (R : ReturnEquationData S) (L : ReturnCorrectionData S)
    (P : ResidualData S) (B : ControlColumnData S) (V : CoupledInverseData S) (Q : QuadraticErrorData S)
    (base : ℕ) (ε q0 : ℝ) : Prop :=
  let U := coupledNeighborhood S C base ε q0
  (∀ z ∈ U, stateSector S z.1 → ∀ r y : ResidualSpace S, ∀ p ∈ annularOpen D,
    let η := (V.V z y).1
    (S.height (3 / 4 : ℝ)).decode (Q.Q z r y).1.val p =
      z.2 * angularPartial (fun t => residualErrorCoefficient D S C z t *
        (S.height (3 / 4 : ℝ)).decode r.1.val t *
        angularPartial (heightPairField S η) t) p +
      (S.height (3 / 4 : ℝ)).decode ((L.error z r.2.val η).val) p) ∧
  (∀ z ∈ U, stateSector S z.1 → ∀ r y : ResidualSpace S, ∀ m θ,
    let w := V.V z y
    let f := y.2.val - z.2 • B.heightRow z w.1 - B.circleColumn z w.2.2.1
    (S.circle (3 / 4 : ℝ)).decode (Q.Q z r y).2.val m θ =
      circleChartError S C z r.2.val (R.inverse f) m θ) ∧
  (∀ z ∈ U, stateSector S z.1 → ∀ r y : ResidualSpace S,
    physicalSourceIntegral D ((S.height (3 / 4 : ℝ)).decode (Q.Q z r y).1.val) = 0) ∧
  (∀ z ∈ U, stateSector S z.1 → ∀ y : ResidualSpace S,
    ContinuousFlexibility.Analysis.HasProjectiveLineDerivAt
      (fun x => jointResidual S P (x, z.2))
      (y + Q.Q z (jointResidual S P z) y) z.1 (V.V z y)) ∧
  (∀ z ∈ sectorNeighborhood S base ε q0, ∀ y : ResidualSpace S,
    ContinuousFlexibility.Analysis.HasProjectiveLineDerivAt
      (fun x : StateDirections S => sectorJointResidual S C P (x, z.2))
      (y + Q.Q (liftSectorParameter S C z) (sectorJointResidual S C P z) y)
      z.1 (V.sectorV z y)) ∧
  SmoothTameOn
    (pairGrading (pairGrading (pairGrading (sectorGrading S) realGrading) (residualGrading S))
      (residualGrading S)) (residualGrading S)
    ((sectorNeighborhood S base ε q0 ×ˢ univ) ×ˢ univ)
    (fun z : ((StateDirections S × ℝ) × ResidualSpace S) × ResidualSpace S =>
      Q.Q (liftSectorParameter S C z.1.1) z.1.2 z.2)

/-- Transparent cumulative interface for completion: every stage uses the same
reference, spaces, geometric data, canonical graph, two inverses and final
neighborhood. All existential data below are functions or concrete linear maps. -/
def NonlinearStagesThrough10 (D : ReferenceData) (T : MaterialData)
    (S : PhysicalSpacesData) (C : NonlinearGeometryData S) (R : ReturnEquationData S)
    (base loss : ℕ) (ε q0 : ℝ) : Prop :=
  ∃ L : ReturnCorrectionData S, ∃ K : CanonicalData S,
    ∃ Vol : VolumeModelData S K, ∃ b : ℕ,
      ∃ Domain : CanonicalDomainData S K Vol b,
        ∃ Relative : RelativeInverseData S K Vol b Domain,
          ∃ G : ScalarInverseData S, ∃ Joint : ResidualData S,
            ∃ Columns : ControlColumnData S, ∃ ControlInverse : ControlInverseData S,
              ∃ Coupled : CoupledInverseData S, ∃ Q : QuadraticErrorData S,
                NonlinearPropertiesThrough09 D T S C R L K Vol b Domain Relative G
                  Joint Columns ControlInverse Coupled base loss ε q0 ∧
                    N10Properties D S C R L Joint Columns Coupled Q base ε q0

/-- N10: one unconditional construction through all ten stages. Its Q is
genuinely bilinear on two independent residuals, has the actual source
identities, and obeys the exact derivative identity; §9 183--227. -/
def N10Statement : Prop :=
  ∃ A : RadialReference, ∃ T : MaterialData, ∃ S : PhysicalSpacesData,
    ∃ C : NonlinearGeometryData S, ∃ R : ReturnEquationData S,
      ∃ base loss : ℕ, ∃ ε q0 : ℝ,
        IsMaterialData A.val T ∧ IsPhysicalSpaces A.val T S ∧
          NonlinearStagesThrough10 A.val T S C R base loss ε q0

end ContinuousFlexibility.Statements
