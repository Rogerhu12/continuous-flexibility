import ContinuousFlexibility.Analysis.N06NormalizerSupport
import ContinuousFlexibility.Analysis.SpacesSources

/-!
# Retaining the actual construction when the normalizer is replaced

Only the psi field of the physical-space data is changed. Its height,
circle, cutoff and compatibility functional are the original ones.
Parameterized records are copied field by field; their physical fields,
state neighborhoods and source spaces retain their original definitions.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open scoped ContDiff

set_option backward.isDefEq.respectTransparency true

def n06WithNormalizer (S : PhysicalSpacesData)
    (ψ : (S.height (3 / 4 : ℝ)).Space) : PhysicalSpacesData :=
  { S with psi := ψ }

/-- Replacing the normalizer also reconstructs its actual tame projection
onto the unchanged kernel of Q. -/
theorem n06WithNormalizer_isPhysical
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (ψ : (S.height (3 / 4 : ℝ)).Space)
    (hcompact : HasCompactRadialSupport D ((S.height (3 / 4 : ℝ)).decode ψ))
    (hunit : S.Q ψ = 1) : IsPhysicalSpaces D T (n06WithNormalizer S ψ) := by
  have hH : IsSobolevModel D T (3 / 4 : ℝ) (S.height (3 / 4 : ℝ)) := hS.1 _
  have hQ := hS.2.2.2.2.2.2.2
  have he : spacesSourceFunctional hT hH = S.Q := by
    apply ContinuousLinearMap.ext
    intro f
    exact (hQ.1 f).symm
  have hψ : spacesSourceFunctional hT hH ψ = 1 := by
    rw [he]
    exact hunit
  obtain ⟨P, hP, hker, hid, htame⟩ := spaces_source_projection hT hH ψ hψ
  refine ⟨hS.1, hS.2.1, hS.2.2.1, hS.2.2.2.1,
    hS.2.2.2.2.1, hS.2.2.2.2.2.1, hS.2.2.2.2.2.2.1,
    hQ.1, hcompact, hunit, hQ.2.2.2.1, ?_, hQ.2.2.2.2.2⟩
  refine ⟨P, ?_, ?_, ?_, 0, 2, htame⟩
  · intro f
    dsimp only [n06WithNormalizer] at f ⊢
    rw [← he]
    exact hP f
  · intro f
    change S.Q (P f) = 0
    simpa only [he] using hker f
  · intro f hf
    change S.Q f = 0 at hf
    exact hid f (by simpa only [he] using hf)

def n06NormalizerGeometry {S : PhysicalSpacesData}
    (C : NonlinearGeometryData S) (ψ : (S.height (3 / 4 : ℝ)).Space) :
    NonlinearGeometryData (n06WithNormalizer S ψ) where
  control := C.control
  cell := C.cell
  left := C.left
  right := C.right
  travel := C.travel
  referenceState := C.referenceState
  minusFlow := C.minusFlow
  minusReturnInverse := C.minusReturnInverse
  rightChartInverse := C.rightChartInverse

def n06NormalizerReturns {S : PhysicalSpacesData}
    (R : ReturnEquationData S) (ψ : (S.height (3 / 4 : ℝ)).Space) :
    ReturnEquationData (n06WithNormalizer S ψ) where
  residual := R.residual
  linearPart := R.linearPart
  inverse := R.inverse
  chartIncrement := R.chartIncrement
  error := R.error

def n06NormalizerCorrection {S : PhysicalSpacesData}
    (L : ReturnCorrectionData S) (ψ : (S.height (3 / 4 : ℝ)).Space) :
    ReturnCorrectionData (n06WithNormalizer S ψ) where
  coefficients := L.coefficients
  minusFlow := L.minusFlow
  error := L.error

def n06NormalizerCanonical {S : PhysicalSpacesData}
    (K : CanonicalData S) (ψ : (S.height (3 / 4 : ℝ)).Space) :
    CanonicalData (n06WithNormalizer S ψ) where
  left := K.left
  right := K.right
  physicalLeft := K.physicalLeft
  physicalRight := K.physicalRight
  physicalDomain := K.physicalDomain
  cell := K.cell
  positive := K.positive
  chart := K.chart
  inverseChart := K.inverseChart
  height := K.height
  coefficients := K.coefficients
  potential := K.potential
  dividedDifference := K.dividedDifference
  cutPair := K.cutPair
  cutRadius := K.cutRadius
  normalizationRegion := K.normalizationRegion

def n06NormalizerVolume {S : PhysicalSpacesData} {K : CanonicalData S}
    (V : VolumeModelData S K) (ψ : (S.height (3 / 4 : ℝ)).Space) :
    VolumeModelData (n06WithNormalizer S ψ) (n06NormalizerCanonical K ψ) where
  level := V.level
  forget := V.forget

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S}
  {V : VolumeModelData S K} {base loss : ℕ} {ε : ℝ}

theorem n06Normalizer_N01 (ψ : (S.height (3 / 4 : ℝ)).Space)
    (h : N01Properties D T S C base loss ε) :
    N01Properties D T (n06WithNormalizer S ψ) (n06NormalizerGeometry C ψ) base loss ε :=
  h

theorem n06Normalizer_N02 (ψ : (S.height (3 / 4 : ℝ)).Space)
    (h : N02Properties D T S C R base ε) :
    N02Properties D T (n06WithNormalizer S ψ) (n06NormalizerGeometry C ψ)
      (n06NormalizerReturns R ψ) base ε :=
  h

theorem n06Normalizer_N03 (ψ : (S.height (3 / 4 : ℝ)).Space)
    (h : N03Properties D T S C R L base ε) :
    N03Properties D T (n06WithNormalizer S ψ) (n06NormalizerGeometry C ψ)
      (n06NormalizerReturns R ψ) (n06NormalizerCorrection L ψ) base ε :=
  h

theorem n06Normalizer_N04 (ψ : (S.height (3 / 4 : ℝ)).Space)
    (h : N04Properties D T S C L K base loss ε) :
    N04Properties D T (n06WithNormalizer S ψ) (n06NormalizerGeometry C ψ)
      (n06NormalizerCorrection L ψ) (n06NormalizerCanonical K ψ) base loss ε := by
  refine ⟨?_, h.2⟩
  exact {
    normalizationOpen := h.1.normalizationOpen
    normalizationSupport := h.1.normalizationSupport
    normalization := h.1.normalization
    referenceBounds := h.1.referenceBounds
    referencePositive := h.1.referencePositive
    referenceNegative := h.1.referenceNegative
    referencePartition := h.1.referencePartition
    referenceDomain := h.1.referenceDomain
    domains := h.1.domains
    partition := h.1.partition
    charts := h.1.charts
    boundary := h.1.boundary
    reflection := h.1.reflection
    inverseReflection := h.1.inverseReflection }

/-- Through04 keeps the same physical construction, with only its unused
normalizer parameter retyped. The full N05 graph is transported separately. -/
theorem n06Normalizer_through04 (ψ : (S.height (3 / 4 : ℝ)).Space)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε) :
    NonlinearPropertiesThrough04 D T (n06WithNormalizer S ψ)
      (n06NormalizerGeometry C ψ) (n06NormalizerReturns R ψ)
      (n06NormalizerCorrection L ψ) (n06NormalizerCanonical K ψ) base loss ε := by
  exact ⟨⟨⟨n06Normalizer_N01 ψ h.1.1.1, n06Normalizer_N02 ψ h.1.1.2⟩,
    n06Normalizer_N03 ψ h.1.2⟩, h.2.1, h.2.2.1, h.2.2.2.1,
    n06Normalizer_N04 ψ h.2.2.2.2.1,
    { materialJets := h.2.2.2.2.2.materialJets
      transport := h.2.2.2.2.2.transport
      physicalCoefficients := h.2.2.2.2.2.physicalCoefficients }⟩

theorem n06Normalizer_isVolumeModel (ψ : (S.height (3 / 4 : ℝ)).Space)
    (h : IsVolumeModel T S K V) :
    IsVolumeModel T (n06WithNormalizer S ψ) (n06NormalizerCanonical K ψ)
      (n06NormalizerVolume V ψ) :=
  h

end ContinuousFlexibility.Statements
