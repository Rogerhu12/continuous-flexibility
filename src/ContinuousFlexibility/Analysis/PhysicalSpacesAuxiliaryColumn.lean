module

public import ContinuousFlexibility.Analysis.SpacesSources
public import ContinuousFlexibility.Statements.Nonlinear

/-!
# Replacing only the auxiliary source column

The height and circle realizations, their gradings, the compatibility
functional, and the endpoint cutoff are retained. The new normalizer
has its own genuine continuous tame rank-one projection. Parameterized
records are repackaged field by field; no state, source, coefficient,
flow, chart, or inverse function is changed by that repackaging.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

def physicalSpacesReplaceAuxiliaryColumn (S : PhysicalSpacesData)
    (ψ : (S.height (3 / 4 : ℝ)).Space) : PhysicalSpacesData :=
  { S with psi := ψ }

def geometryReplaceAuxiliaryColumn {S : PhysicalSpacesData}
    (C : NonlinearGeometryData S) (ψ : (S.height (3 / 4 : ℝ)).Space) :
    NonlinearGeometryData (physicalSpacesReplaceAuxiliaryColumn S ψ) where
  control := C.control
  cell := C.cell
  left := C.left
  right := C.right
  travel := C.travel
  referenceState := C.referenceState
  minusFlow := C.minusFlow
  minusReturnInverse := C.minusReturnInverse
  rightChartInverse := C.rightChartInverse

def returnReplaceAuxiliaryColumn {S : PhysicalSpacesData}
    (R : ReturnEquationData S) (ψ : (S.height (3 / 4 : ℝ)).Space) :
    ReturnEquationData (physicalSpacesReplaceAuxiliaryColumn S ψ) where
  residual := R.residual
  linearPart := R.linearPart
  inverse := R.inverse
  chartIncrement := R.chartIncrement
  error := R.error

def correctionReplaceAuxiliaryColumn {S : PhysicalSpacesData}
    (L : ReturnCorrectionData S) (ψ : (S.height (3 / 4 : ℝ)).Space) :
    ReturnCorrectionData (physicalSpacesReplaceAuxiliaryColumn S ψ) where
  coefficients := L.coefficients
  minusFlow := L.minusFlow
  error := L.error

def canonicalReplaceAuxiliaryColumn {S : PhysicalSpacesData}
    (K : CanonicalData S) (ψ : (S.height (3 / 4 : ℝ)).Space) :
    CanonicalData (physicalSpacesReplaceAuxiliaryColumn S ψ) where
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

theorem isPhysicalSpaces_replaceAuxiliaryColumn
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (ψ : (S.height (3 / 4 : ℝ)).Space)
    (hcompact : HasCompactRadialSupport D ((S.height (3 / 4 : ℝ)).decode ψ))
    (hnormal : S.Q ψ = 1) :
    IsPhysicalSpaces D T (physicalSpacesReplaceAuxiliaryColumn S ψ) := by
  rcases hS with ⟨hheight, hcircle, hcutoff, htameH, htameC, hmul, htrace,
    hQ, _, _, hQtame, _, hinv, hcomp, hparity⟩
  have hQeq : S.Q = spacesSourceFunctional hT (hheight (3 / 4)) := by
    ext f
    rw [spacesSourceFunctional_apply]
    exact hQ f
  have hnormal' : spacesSourceFunctional hT (hheight (3 / 4)) ψ = 1 := by
    rw [← hQeq]
    exact hnormal
  obtain ⟨P, hP, hPQ, hPid, hPtame⟩ :=
    spaces_source_projection hT (hheight (3 / 4)) ψ hnormal'
  rw [← hQeq] at hP hPQ hPid
  exact ⟨hheight, hcircle, hcutoff, htameH, htameC, hmul, htrace,
    hQ, hcompact, hnormal, hQtame, ⟨P, hP, hPQ, hPid, 0, 2, hPtame⟩,
    hinv, hcomp, hparity⟩

/-- Through03 uses the unchanged height/circle realizations, cutoff and
compatibility functional. Its actual data fields are exactly preserved. -/
theorem nonlinearThrough03_replaceAuxiliaryColumn
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (ψ : (S.height (3 / 4 : ℝ)).Space) :
    NonlinearPropertiesThrough03 D T (physicalSpacesReplaceAuxiliaryColumn S ψ)
      (geometryReplaceAuxiliaryColumn C ψ) (returnReplaceAuxiliaryColumn R ψ)
      (correctionReplaceAuxiliaryColumn L ψ) base loss ε :=
  ⟨⟨hN.1.1, hN.1.2⟩, hN.2⟩

/-- The geometric certificate refers only to the retained fields. The
reference/current auxiliary-column jet conditions are not transported
by this lemma, because their displayed source column really changes. -/
theorem canonicalGeometry_replaceAuxiliaryColumn
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hA : CanonicalGeometry D S C K base ε)
    (ψ : (S.height (3 / 4 : ℝ)).Space) :
    CanonicalGeometry D (physicalSpacesReplaceAuxiliaryColumn S ψ)
      (geometryReplaceAuxiliaryColumn C ψ) (canonicalReplaceAuxiliaryColumn K ψ) base ε where
  normalizationOpen := hA.normalizationOpen
  normalizationSupport := hA.normalizationSupport
  normalization := hA.normalization
  referenceBounds := hA.referenceBounds
  referencePositive := hA.referencePositive
  referenceNegative := hA.referenceNegative
  referencePartition := hA.referencePartition
  referenceDomain := hA.referenceDomain
  domains := hA.domains
  partition := hA.partition
  charts := hA.charts
  boundary := hA.boundary
  reflection := hA.reflection
  inverseReflection := hA.inverseReflection

end ContinuousFlexibility.Analysis
