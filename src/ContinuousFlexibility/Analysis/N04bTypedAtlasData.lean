import ContinuousFlexibility.Analysis.N04bActualDomainGeometry
import ContinuousFlexibility.Analysis.N04bReferenceMetadata
import ContinuousFlexibility.Analysis.N04CanonicalAtlas
import ContinuousFlexibility.Analysis.N04bCanonicalOperator

/-!
# The concrete typed atlas record

Positive pieces use their actual affine Liouville maps. Negative pieces
use the supplied constructed maps, with physical domains fixed by the
actual corrected travel chart. One equivalence indexes every field.
Reference metadata use the specified optical cut, and the operator fields
are the actual coordinate formulas for these very charts and heights.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements

def n04bTypedAtlasChart {D : ReferenceData} {S : PhysicalSpacesData}
    (C : NonlinearGeometryData S)
    (F : (AnnularState S × ℝ) → ℕ → Bool → PolarPoint → PolarPoint)
    (z : AnnularState S × ℝ) : N04PieceIndex D → PolarPoint → PolarPoint
  | .inl i => F z i.1 i.2
  | .inr i => n04UnitChart (n04TypedPieceLeft C (.inr i))
      (n04TypedPieceRight C (.inr i)) false

def n04bTypedAtlasInverse {D : ReferenceData} {S : PhysicalSpacesData}
    (C : NonlinearGeometryData S)
    (J : (AnnularState S × ℝ) → ℕ → Bool → PolarPoint → PolarPoint)
    (z : AnnularState S × ℝ) : N04PieceIndex D → PolarPoint → PolarPoint
  | .inl i => J z i.1 i.2
  | .inr i => n04UnitInverseChart (n04TypedPieceLeft C (.inr i))
      (n04TypedPieceRight C (.inr i)) false

def n04bTypedAtlasHeight (D : ReferenceData) {S : PhysicalSpacesData}
    (C : NonlinearGeometryData S)
    (h : (AnnularState S × ℝ) → ℕ → Bool → PolarPoint → ℝ)
    (z : AnnularState S × ℝ) : N04PieceIndex D → PolarPoint → ℝ
  | .inl i => h z i.1 i.2
  | .inr i => n04LiouvilleHeight D.w (n04TypedPieceLeft C (.inr i))
      (n04TypedPieceRight C (.inr i))

/-- The typed maps are inserted into the existing actual affine atlas,
then the reference metadata and genuine operator formulas are computed. -/
def n04bTypedAtlasData (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (L : ReturnCorrectionData S)
    (cut : ℕ → ℝ) (e : ℕ ≃ N04PieceIndex D)
    (F : (AnnularState S × ℝ) → ℕ → Bool → PolarPoint → PolarPoint)
    (h : (AnnularState S × ℝ) → ℕ → Bool → PolarPoint → ℝ)
    (J : (AnnularState S × ℝ) → ℕ → Bool → PolarPoint → PolarPoint) : CanonicalData S :=
  let P := n04bReferencePieces C cut e
  let K : CanonicalData S :=
    { n04CanonicalAtlas D S C L P with
      physicalDomain := fun z m => n04bTypedPhysicalDomain C
        (n04bActualTravelChart S C L z) (e m)
      chart := fun z m => n04bTypedAtlasChart C F z (e m)
      inverseChart := fun z m => n04bTypedAtlasInverse C J z (e m)
      height := fun z m => n04bTypedAtlasHeight D C h z (e m)
      normalizationRegion := n04bNormalizationRegion D }
  n04bCanonicalOperatorData S L (n04bReferenceMetadata C cut e C.travel K)

variable {D : ReferenceData} {S : PhysicalSpacesData}
  (C : NonlinearGeometryData S) (L : ReturnCorrectionData S)
  (cut : ℕ → ℝ) (e : ℕ ≃ N04PieceIndex D)
  (F : (AnnularState S × ℝ) → ℕ → Bool → PolarPoint → PolarPoint)
  (h : (AnnularState S × ℝ) → ℕ → Bool → PolarPoint → ℝ)
  (J : (AnnularState S × ℝ) → ℕ → Bool → PolarPoint → PolarPoint)

@[simp] theorem n04bTypedAtlasData_physicalPieceOpen (z : AnnularState S × ℝ) (m : ℕ) :
    physicalPieceOpen S (n04bTypedAtlasData D S C L cut e F h J) z m =
      n04bTypedPhysicalDomain C (n04bActualTravelChart S C L z) (e m) := rfl

@[simp] theorem n04bTypedAtlasData_referencePhysicalPieceOpen (m : ℕ) :
    referencePhysicalPieceOpen S (n04bTypedAtlasData D S C L cut e F h J) m =
      Ioo (n04bReferenceTypedLeft C cut (e m))
        (n04bReferenceTypedRight C cut (e m)) ×ˢ univ := rfl

@[simp] theorem n04bTypedAtlasData_chart (z : AnnularState S × ℝ) (m : ℕ) :
    (n04bTypedAtlasData D S C L cut e F h J).chart z m =
      n04bTypedAtlasChart C F z (e m) := rfl

@[simp] theorem n04bTypedAtlasData_inverseChart (z : AnnularState S × ℝ) (m : ℕ) :
    (n04bTypedAtlasData D S C L cut e F h J).inverseChart z m =
      n04bTypedAtlasInverse C J z (e m) := rfl

@[simp] theorem n04bTypedAtlasData_height (z : AnnularState S × ℝ) (m : ℕ) :
    (n04bTypedAtlasData D S C L cut e F h J).height z m =
      n04bTypedAtlasHeight D C h z (e m) := rfl

@[simp] theorem n04bTypedAtlasData_positive (m : ℕ) :
    (n04bTypedAtlasData D S C L cut e F h J).positive m = n04TypedPiecePositive (e m) := rfl

@[simp] theorem n04bTypedAtlasData_left (m : ℕ) :
    (n04bTypedAtlasData D S C L cut e F h J).left m = 0 := by
  cases hi : e m <;> simp [n04bTypedAtlasData, n04bCanonicalOperatorData,
    n04bReferenceMetadata, n04CanonicalAtlas, hi]

@[simp] theorem n04bTypedAtlasData_right (m : ℕ) :
    (n04bTypedAtlasData D S C L cut e F h J).right m =
      match e m with
      | .inl i => n04bRootCutRadius (C.travel i.1)
      | .inr _ => 1 := by
  cases hi : e m <;> simp [n04bTypedAtlasData, n04bCanonicalOperatorData,
    n04bReferenceMetadata, n04CanonicalAtlas, hi]

@[simp] theorem n04bTypedAtlasData_cutPair (m : ℕ) :
    (n04bTypedAtlasData D S C L cut e F h J).cutPair m =
      (e.symm (.inl (m, false)), e.symm (.inl (m, true))) := rfl

@[simp] theorem n04bTypedAtlasData_cutRadius (m : ℕ) :
    (n04bTypedAtlasData D S C L cut e F h J).cutRadius m =
      n04bRootCutRadius (C.travel m) := rfl

@[simp] theorem n04bTypedAtlasData_normalizationRegion :
    (n04bTypedAtlasData D S C L cut e F h J).normalizationRegion =
      n04bNormalizationRegion D := rfl

/-- On a positive index the concrete atlas retains the complete affine
piece, including both fixed closed canonical endpoints. -/
theorem n04bTypedAtlasData_positive_fields
    (z : AnnularState S × ℝ) (m : ℕ) (i : N04PositivePieceIndex D)
    (hi : e m = .inr i) :
    let K := n04bTypedAtlasData D S C L cut e F h J
    let K₀ := n04CanonicalAtlas D S C L (n04bReferencePieces C cut e)
    physicalPieceOpen S K z m = physicalPieceOpen S K₀ z m ∧
      canonicalOpen S K m = canonicalOpen S K₀ m ∧
      canonicalClosed S K m = canonicalClosed S K₀ m ∧
      K.chart z m = K₀.chart z m ∧
      K.inverseChart z m = K₀.inverseChart z m ∧
      K.height z m = K₀.height z m := by
  simp only [n04bTypedAtlasData, n04bCanonicalOperatorData,
    n04bReferenceMetadata, n04CanonicalAtlas, physicalPieceOpen,
    canonicalOpen, canonicalClosed, n04bReferencePieces, hi,
    n04bTypedPhysicalDomain, n04bReferenceTypedLeft, n04bReferenceTypedRight,
    n04bTypedAtlasChart, n04bTypedAtlasInverse, n04bTypedAtlasHeight,
    n04TypedPieceReversed, n04TypedPieceLeft, n04TypedPieceRight, and_self]

end ContinuousFlexibility.Analysis
