import ContinuousFlexibility.Analysis.N06FiniteCurrentGreenAssembly
import ContinuousFlexibility.Analysis.N06LeftColumnFullPairing
import ContinuousFlexibility.Analysis.N06PositiveDividedRegularity
import ContinuousFlexibility.Analysis.N06NamedPhysicalRelation

/-!
# From actual local Green data to the original physical relation

The finite value representatives, true endpoint jets and matching normal
rows are the local analytic data still to be constructed. They imply the
original full-period physical equation: the actual left-cutoff identity
removes the last scalar defect. The original N05 graph supplies the
normalization row. Positive regularity is derived on the same complete
Through05 witness after one neighborhood restriction.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory
open ContinuousFlexibility.Analysis
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-- The explicit local data used in finite Green gluing. Boundary values
are true traces, and the matching condition is pointwise between adjacent
reference indices. Actual inverse endpoint circles are required only at
true sides; artificial cuts are handled by their common canonical radius. The physical equation is not a field of this structure. -/
structure N06CurrentFiniteGreenData
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (L : ReturnCorrectionData S) (K : CanonicalData S) (z : AnnularState S × ℝ)
    (u : CanonicalUnknown S K) (F : CanonicalSequence S K) (φ : PolarPoint → ℝ) where
  test : ∀ m, N06CurrentHeightTestTraces S K z m (n06_radialTestAverage φ)
  value : ℕ → PolarPoint → ℝ
  radialCoefficient : ℕ → ℝ → ℝ
  reverse : ℕ → Bool
  regular : ∀ m, ContDiff ℝ 1 (value m)
  represents : ∀ m, (u.1 m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m] value m
  endpointCircles : ∀ m, ∀ side : Bool, ¬n06ArtificialCutSide K m side →
    ∀ θ ∈ Icc (0 : ℝ) Real.pi,
      (K.inverseChart z m
        ((if (if reverse m then !side else side) then K.right m else K.left m), θ)).1 =
          if side then K.physicalRight m else K.physicalLeft m
  green : ∀ m,
    (∫ p, n06CurrentRemainderSource D S C L K z u F m p *
      canonicalHeight S K z m (n06_radialTestAverage φ) p ∂canonicalMeasure S K m) -
    (∫ p, value m p * canonicalSource S K z m
      (n06_radialTestAverage (divergenceOperator (L.coefficients z) φ)) p
        ∂canonicalMeasure S K m) =
    ∫ θ in (0 : ℝ)..Real.pi,
      radialCoefficient m (K.right m) *
        ((test m).value (K.right m, θ) * radialPartial (value m) (K.right m, θ) -
          value m (K.right m, θ) * (test m).radial (K.right m, θ)) -
      radialCoefficient m (K.left m) *
        ((test m).value (K.left m, θ) * radialPartial (value m) (K.left m, θ) -
          value m (K.left m, θ) * (test m).radial (K.left m, θ))
  matching : ∀ i j, K.physicalRight i = K.physicalLeft j →
    ∀ θ ∈ Icc (0 : ℝ) Real.pi,
      n06OrientedCanonicalBoundary (test i) (value i) (radialCoefficient i) (reverse i) true θ =
        n06OrientedCanonicalBoundary (test j) (value j) (radialCoefficient j) (reverse j) false θ

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S}
  {V : VolumeModelData S K} {b base loss : ℕ} {ε : ℝ}
  {B : CanonicalDomainData S K V b} {z : AnnularState S × ℝ}

/-- Local Green formulas and matching rows give the full original weak
equation, with no left-cutoff residual. -/
theorem n06_namedPhysicalWeakRelation_of_finiteGreen
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (hcoords : N05ControlledReferenceCoordinates D S C K)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hpositive : ∀ m, K.positive m = true →
      ContDiffOn ℝ ∞ (K.coefficients z m).a (canonicalOpen S K m) ∧
      ContDiffOn ℝ ∞ (K.coefficients z m).b (canonicalOpen S K m) ∧
      ContDiffOn ℝ ∞ (K.coefficients z m).c (canonicalOpen S K m))
    (u : B.Space) (F : V.level (3 / 4 : ℝ) 0 b)
    (hdata : ∀ φ, RadialTest D φ → Nonempty (N06CurrentFiniteGreenData D S C L K z
      u.val.1 (V.forget (3 / 4 : ℝ) 0 b F) φ)) :
    N06NamedPhysicalWeakRelation D C L B z u F := by
  intro φ hφ
  obtain ⟨P⟩ := hdata φ hφ
  have he := n06_current_finiteGreen_assembly hT hS h01 h03 h04 hcoords hz hs
    u.val.1 (V.forget (3 / 4 : ℝ) 0 b F) hφ P.test P.value P.radialCoefficient P.reverse
    P.regular P.represents P.endpointCircles P.green P.matching
  rw [n06_currentLeftColumn_full_pairing hT hS h01 h03 h04 hcoords hz hs hpositive hφ,
    sub_self, mul_zero] at he
  exact sub_eq_zero.mp he

/-- The same complete Through05 construction gives a neighborhood on
which local finite Green data imply the unchanged physical relation.
There is no separate positive-regularity premise in this conclusion. -/
theorem n06_exists_finiteGreen_relation_through05
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hthrough : NonlinearPropertiesThrough05 D T S C R L K V b B base loss ε)
    (hcoords : N05ControlledReferenceCoordinates D S C K) :
    ∃ ε' : ℝ, 0 < ε' ∧ ε' ≤ ε ∧
      NonlinearPropertiesThrough05 D T S C R L K V b B base loss ε' ∧
      ∀ z ∈ stateNeighborhood S C base ε', stateSector S z.1 →
        ∀ u : B.Space, ∀ F : V.level (3 / 4 : ℝ) 0 b,
          (∀ φ, RadialTest D φ → Nonempty (N06CurrentFiniteGreenData D S C L K z
            u.val.1 (V.forget (3 / 4 : ℝ) 0 b F) φ)) →
          PerturbedCanonicalRelation D S C K L z u.val.1 (V.forget (3 / 4 : ℝ) 0 b F) := by
  have hex := n06_exists_positive_regular_through05 hT hS hthrough
  let ε' : ℝ := hex.choose
  have hε' : 0 < ε' := hex.choose_spec.1
  have hle : ε' ≤ ε := hex.choose_spec.2.1
  have hnew := hex.choose_spec.2.2.1
  have hreg := hex.choose_spec.2.2.2
  have h01 := hnew.1.1.1.1
  have h03 := hnew.1.1.2
  have h04 := hnew.1.2.2.2.2
  refine ⟨ε', hε', hle, hnew, ?_⟩
  intro z hz hs u F hdata
  exact n06_namedPhysicalWeakRelation_implies h01.1.1.choose_spec.1.2.1.le
    h04 hnew.2 (n05_referenceState_mem hε') (n05_referenceState_sector h01.2.2.1)
    hz hs u F (n06_namedPhysicalWeakRelation_of_finiteGreen hT hS h01 h03 h04 hcoords
      hz hs (fun m hm => (hreg z hz hs m hm).1) u F hdata)

end ContinuousFlexibility.Statements
