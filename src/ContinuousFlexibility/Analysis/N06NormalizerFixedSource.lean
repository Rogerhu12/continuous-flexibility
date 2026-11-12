import ContinuousFlexibility.Analysis.N06NormalizerConstruction
import ContinuousFlexibility.Analysis.N06FiniteSourceNormalization

/-!
# The reselected actual normalizer has no canonical source variation

The normalizer comes from the supported Through05 construction. N04
fixes the chart, height and actual Jacobian on this already existing
region. Thus its actual current and reference canonical sources agree,
and every mixed jet of their difference vanishes. No support condition
is required of the input normalizer.
-/

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

/-- The complete reselected Through05 witness has an exactly fixed actual
normalizer source. Its height/circle spaces, compatibility functional,
cutoff, geometry, source levels and material parameters remain the ones
already chosen, via the explicit copies and graph equivalence. -/
theorem n06_exists_fixed_normalizer_through05
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {V : VolumeModelData S K} {b base loss : ℕ} {ε : ℝ}
    {B : CanonicalDomainData S K V b}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hthrough : NonlinearPropertiesThrough05 D T S C R L K V b B base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K) :
    ∃ ψ : (S.height (3 / 4 : ℝ)).Space,
      ∃ v : B.Space, ∃ hv : n06NormalizerLambda S K v.val.1 = 0,
        IsPhysicalSpaces D T (n06WithNormalizer S ψ) ∧
        NonlinearPropertiesThrough05 D T (n06WithNormalizer S ψ)
          (n06NormalizerGeometry C ψ) (n06NormalizerReturns R ψ)
          (n06NormalizerCorrection L ψ) (n06NormalizerCanonical K ψ)
          (n06NormalizerVolume V ψ) b (n06NormalizerDomain B ψ v hv) base loss ε ∧
        N05ControlledReferenceCoordinates D (n06WithNormalizer S ψ)
          (n06NormalizerGeometry C ψ) (n06NormalizerCanonical K ψ) ∧
        N06NormalizerSourceFixed (n06WithNormalizer S ψ)
          (n06NormalizerGeometry C ψ) (n06NormalizerCanonical K ψ) base ε := by
  obtain ⟨ψ, _, v, hv, hS', hthrough', g, J, _, _, _, hJK, hzero, hψ⟩ :=
    n06_exists_supported_normalizer_through05 hT hS hthrough hcoordinates
  refine ⟨ψ, v, hv, hS', hthrough',
    n06Normalizer_controlledReferenceCoordinates ψ hcoordinates, ?_⟩
  have h01 := hthrough'.1.1.1.1
  have h04 := hthrough'.1.2.2.2.2.1
  have href : ((n06NormalizerGeometry C ψ).referenceState, 0) ∈
      stateNeighborhood (n06WithNormalizer S ψ) (n06NormalizerGeometry C ψ) base ε :=
    n05_referenceState_mem h01.2.1
  have hsector : stateSector (n06WithNormalizer S ψ) (n06NormalizerGeometry C ψ).referenceState :=
    n05_referenceState_sector h01.2.2.1
  have hsupport : ∀ p : PolarPoint,
      ((n06WithNormalizer S ψ).height (3 / 4 : ℝ)).decode (n06WithNormalizer S ψ).psi p ≠ 0 →
        p.1 ∈ (n06NormalizerCanonical K ψ).normalizationRegion := by
    intro p hp
    apply hJK
    by_contra hnot
    apply hp
    change (S.height (3 / 4 : ℝ)).decode ψ p = 0
    exact (congrFun hψ p).trans (hzero p.1 hnot)
  intro z hz hs m
  constructor
  · intro p hp
    exact n06_canonicalSource_normalization_fixed h04 href hsector hz hs hsupport m hp
  · intro a b p hp
    exact n06_canonicalSource_normalization_difference_jet_zero
      h04 href hsector hz hs hsupport m a b hp

end ContinuousFlexibility.Statements
