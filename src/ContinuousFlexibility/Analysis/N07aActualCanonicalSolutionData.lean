import ContinuousFlexibility.Analysis.N07aCurrentQualitativeRegularity
import ContinuousFlexibility.Analysis.N07aScalarSourceTerminal

/-!
# The actual canonical solution family consumed by physical reconstruction

There is one base source and one fixed Banach inverse. The unknown and
source sequence below are definitions from that source, rather than
independently chosen representatives. The record collects the exact
weak relation and the fixed-loss estimates for its smooth decoder.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency true

attribute [local instance]
  n07aNonlinearAnnularGroup n07aNonlinearAnnularModule
  n07aNonlinearAnnularAddGroup n07aNonlinearAnnularSMul n07aNonlinearAnnularSub
  n07aNonlinearAnnularParameterGroup n07aNonlinearAnnularParameterModule
  n07aNonlinearAnnularParameterAddGroup n07aNonlinearAnnularParameterSMul
  n07aNonlinearAnnularParameterSub
  n07aNonlinearDirectionsGroup n07aNonlinearDirectionsModule
  n07aNonlinearDirectionsAddGroup n07aNonlinearDirectionsSMul n07aNonlinearDirectionsSub
  n07aNonlinearSectorParameterGroup n07aNonlinearSectorParameterModule
  n07aNonlinearSectorParameterAddGroup n07aNonlinearSectorParameterSMul
  n07aNonlinearSectorParameterSub

variable {S : PhysicalSpacesData} {K : CanonicalData S}
  {V : VolumeModelData S K} {b : ℕ}

local instance n07aCanonicalSolutionDataLevelGroup :
    NormedAddCommGroup (V.level (3 / 4 : ℝ) 0 b) := Submodule.normedAddCommGroup _
local instance n07aCanonicalSolutionDataLevelSpace :
    NormedSpace ℝ (V.level (3 / 4 : ℝ) 0 b) := Submodule.normedSpace _

def n07aActualCanonicalUnknown (C : NonlinearGeometryData S)
    (B : CanonicalDomainData S K V b) (P : RelativeInverseData S K V b B)
    (F₀ : CanonicalGeometry.Parameter S → S.Source → V.level (3 / 4 : ℝ) 0 b)
    (z : CanonicalGeometry.Parameter S) (f : S.Source) : CanonicalUnknown S K :=
  (n07aBaseInverse B P (liftSectorParameter S C z) (F₀ z f)).val.1

def n07aActualCanonicalSource
    (F₀ : CanonicalGeometry.Parameter S → S.Source → V.level (3 / 4 : ℝ) 0 b)
    (z : CanonicalGeometry.Parameter S) (f : S.Source) : CanonicalSequence S K :=
  V.forget (3 / 4 : ℝ) 0 b (F₀ z f)

structure N07aActualCanonicalSolutionData
    (D : ReferenceData) (T : MaterialData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (L : ReturnCorrectionData S) (K : CanonicalData S)
    (V : VolumeModelData S K) (b : ℕ) (B : CanonicalDomainData S K V b)
    (P : RelativeInverseData S K V b B) (base : ℕ) (ε : ℝ) where
  F₀ : CanonicalGeometry.Parameter S → S.Source → V.level (3 / 4 : ℝ) 0 b
  w : CanonicalGeometry.Parameter S → S.Source → ℕ → PolarPoint → ℝ
  interval : ∀ m, K.left m < K.right m
  low : ℕ
  loss : ℕ
  C₀ : ℝ
  Cα : ℝ
  C₀_pos : 0 < C₀
  Cα_nonneg : 0 ≤ Cα
  baseNorm : ∀ z ∈ sectorNeighborhood S base ε ε, ∀ f,
    ‖F₀ z f‖ ≤ C₀ * S.sourceGrading low f
  scalars : ∀ z ∈ sectorNeighborhood S base ε ε, ∀ f i,
    |n07aUnknownScalar (n07aActualCanonicalUnknown C B P F₀ z f) i| ≤
      Cα * S.sourceGrading low f
  sourceAE : ∀ z ∈ sectorNeighborhood S base ε ε, ∀ f m,
    (n07aActualCanonicalSource F₀ z f m : PolarPoint → ℝ)
      =ᵐ[canonicalMeasure S K m]
        canonicalSource S K (liftSectorParameter S C z) m
          ((S.height (3 / 4 : ℝ)).decode f.val)
  relation : ∀ z ∈ sectorNeighborhood S base ε ε, ∀ f,
    PerturbedCanonicalRelation D S C K L (liftSectorParameter S C z)
      (n07aActualCanonicalUnknown C B P F₀ z f) (n07aActualCanonicalSource F₀ z f)
  even : ∀ z ∈ sectorNeighborhood S base ε ε, ∀ f m,
    n07aAngularReflection m ((n07aActualCanonicalUnknown C B P F₀ z f).1 m) =
      (n07aActualCanonicalUnknown C B P F₀ z f).1 m
  regular : ∀ z ∈ sectorNeighborhood S base ε ε, ∀ f m k,
    N07aCanonicalNormalRegular S K m ((n07aActualCanonicalUnknown C B P F₀ z f).1 m) k
  decode : ∀ z (hz : z ∈ sectorNeighborhood S base ε ε) f m,
    w z f m = n07aCanonicalSmoothDecode (interval m)
      ⟨(n07aActualCanonicalUnknown C B P F₀ z f).1 m, regular z hz f m⟩
  equation : ∀ z ∈ sectorNeighborhood S base ε ε, ∀ f m,
    EqOn (mixedDerivative 2 0 (w z f m))
      (n07aNormalRhs
        (fun i => n07aNormalCoefficientFamily
          (fun k z m => n07aPrincipalField K (liftSectorParameter S C z) m k)
          (fun m => if K.positive m then -1 else 1) i z m)
        (w z f m)
        (n07aCanonicalSourceWithoutColumns D S C L K
          (fun z f => n07aUnknownScalar (n07aActualCanonicalUnknown C B P F₀ z f)) z f m))
      (canonicalOpen S K m)
  jets : N07aSampleLinearJetBounds T K (CanonicalGeometry.parameterGrading S)
    S.sourceGrading (sectorNeighborhood S base ε ε) (canonicalOpen S K)
    (fun c m => T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ) *
      (T.M (T.sample (K.cell m)) ^ c)⁻¹) low loss w

namespace N07aActualCanonicalSolutionData

variable {D : ReferenceData} {T : MaterialData} {C : NonlinearGeometryData S}
  {L : ReturnCorrectionData S} {B : CanonicalDomainData S K V b}
  {P : RelativeInverseData S K V b B} {base : ℕ} {ε : ℝ}

def U (data : N07aActualCanonicalSolutionData D T S C L K V b B P base ε) :
    CanonicalGeometry.Parameter S → S.Source → CanonicalUnknown S K :=
  n07aActualCanonicalUnknown C B P data.F₀

def F (data : N07aActualCanonicalSolutionData D T S C L K V b B P base ε) :
    CanonicalGeometry.Parameter S → S.Source → CanonicalSequence S K :=
  n07aActualCanonicalSource data.F₀

theorem smooth (data : N07aActualCanonicalSolutionData D T S C L K V b B P base ε)
    (z : CanonicalGeometry.Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
    (f : S.Source) (m : ℕ) : ContDiffOn ℝ ∞ (data.w z f m) (canonicalOpen S K m) := by
  rw [data.decode z hz f m]
  exact (n07aCanonicalSmoothRepresentative_properties (data.interval m)
    ⟨(data.U z f).1 m, data.regular z hz f m⟩).1

theorem periodic (data : N07aActualCanonicalSolutionData D T S C L K V b B P base ε)
    (z : CanonicalGeometry.Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
    (f : S.Source) (m : ℕ) : Function.Periodic (data.w z f m) (0, Real.pi) := by
  rw [data.decode z hz f m]
  exact (n07aCanonicalSmoothRepresentative_properties (data.interval m)
    ⟨(data.U z f).1 m, data.regular z hz f m⟩).2.1

/-- The actual relative inverse still takes its values in the original
reference graph. This retains the reference weak equation needed to identify
the two genuine first traces, independently of the current source sequence. -/
theorem referenceGraph
    (data : N07aActualCanonicalSolutionData D T S C L K V b B P base ε)
    (h05 : N05Properties D T S C K V b B)
    (z : CanonicalGeometry.Parameter S) (f : S.Source) :
    ∃ Fref : CanonicalSequence S K, ∃ ηref fref : PolarPoint → ℝ,
      HasCanonicalRepresentation D S C K (C.referenceState, 0)
        (data.U z f) Fref ηref fref ∧
      ReferenceGraph D B.weakExponent B.sourceMaterial B.outputMaterial
        (ηref, (data.U z f).2.2.1)
        ((fun p => fref p - (data.U z f).2.2.2 *
          (S.height (3 / 4 : ℝ)).decode S.psi p), 0) := by
  let u := n07aBaseInverse B P (liftSectorParameter S C z) (data.F₀ z f)
  have hgraph := (h05.2.2.2.2.2.2.1 u.val).mp u.property
  exact ⟨V.forget (3 / 4 : ℝ) 0 b u.val.2, hgraph.2⟩

end N07aActualCanonicalSolutionData

end ContinuousFlexibility.Analysis
