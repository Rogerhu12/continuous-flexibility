import ContinuousFlexibility.Analysis.N04bTypedAtlasDomains

/-!
# The actual positive pieces retain their proved affine geometry

The concrete typed constructor agrees, field by field, with the existing
proved reference atlas on every positive index. The complete open-chart,
closed-boundary, and reflection clauses therefore transfer to the same
actual constructor without introducing a new geometric assumption.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff

variable {D : ReferenceData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S}
  (e : ℕ ≃ N04PieceIndex D)
  (F : (AnnularState S × ℝ) → ℕ → Bool → PolarPoint → PolarPoint)
  (h : (AnnularState S × ℝ) → ℕ → Bool → PolarPoint → ℝ)
  (J : (AnnularState S × ℝ) → ℕ → Bool → PolarPoint → PolarPoint)
  (hD : RadialProfileGeometry D) (hC : controlGeometryConditions D S C)
  (cut : ℕ → ℝ) (hcut : ∀ m, cut m ∈ Ioo (C.left m) (C.right m))
  {base : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}
  (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
  (m : ℕ) (i : N04PositivePieceIndex D) (hi : e m = .inr i)

include hD hC hcut hz hs hi

theorem n04bTypedAtlasData_positive_charts :
    let K := n04bTypedAtlasData D S C L cut e F h J
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
      K.height z m (p + (0, Real.pi)) = K.height z m p) := by
  have hA := n04CanonicalAtlas_partA (C := C) (L := L) (base := base) (ε := ε)
    hD (n04bReferencePieces_geometry hD hC hcut e)
  obtain ⟨hΩ, hCan, _, hF, hJ, hh⟩ :=
    n04bTypedAtlasData_positive_fields C L cut e F h J z m i hi
  simpa only [hΩ, hCan, hF, hJ, hh] using hA.charts z hz hs m

theorem n04bTypedAtlasData_positive_boundary :
    let K := n04bTypedAtlasData D S C L cut e F h J
    MapsTo (K.chart z m) (physicalPieceClosed S K z m) (canonicalClosed S K m) ∧
    MapsTo (K.inverseChart z m) (canonicalClosed S K m) (physicalPieceClosed S K z m) ∧
    (∀ p ∈ physicalPieceClosed S K z m, K.inverseChart z m (K.chart z m p) = p) ∧
    (∀ p ∈ canonicalClosed S K m, K.chart z m (K.inverseChart z m p) = p) ∧
    (∀ p ∈ physicalPieceClosed S K z m,
      ContDiffAt ℝ ∞ (K.chart z m) p ∧ ContDiffAt ℝ ∞ (K.height z m) p ∧
        planeJacobian (K.chart z m) p ≠ 0 ∧ 0 < K.height z m p) ∧
    (∀ p ∈ frontier (physicalPieceOpen S K z m),
      CanonicalBoundaryInverseGerm (K.chart z m) (K.inverseChart z m) p) := by
  have hA := n04CanonicalAtlas_partA (C := C) (L := L) (base := base) (ε := ε)
    hD (n04bReferencePieces_geometry hD hC hcut e)
  obtain ⟨hΩ, _, hCan, hF, hJ, hh⟩ :=
    n04bTypedAtlasData_positive_fields C L cut e F h J z m i hi
  simpa only [physicalPieceClosed, hΩ, hCan, hF, hJ, hh] using hA.boundary z hz hs m

theorem n04bTypedAtlasData_positive_reflection :
    let K := n04bTypedAtlasData D S C L cut e F h J
    ∀ p ∈ physicalPieceOpen S K z m,
      K.chart z m (p.1, -p.2) = ((K.chart z m p).1, -(K.chart z m p).2) ∧
      K.height z m (p.1, -p.2) = K.height z m p ∧
      planeJacobian (K.chart z m) (p.1, -p.2) = planeJacobian (K.chart z m) p := by
  have hA := n04CanonicalAtlas_partA (C := C) (L := L) (base := base) (ε := ε)
    hD (n04bReferencePieces_geometry hD hC hcut e)
  obtain ⟨hΩ, _, _, hF, _, hh⟩ :=
    n04bTypedAtlasData_positive_fields C L cut e F h J z m i hi
  simpa only [hΩ, hF, hh] using hA.reflection z hz hs m

theorem n04bTypedAtlasData_positive_inverseReflection :
    let K := n04bTypedAtlasData D S C L cut e F h J
    ∀ p ∈ canonicalOpen S K m,
      K.inverseChart z m (p.1, -p.2) =
        ((K.inverseChart z m p).1, -(K.inverseChart z m p).2) := by
  have hA := n04CanonicalAtlas_partA (C := C) (L := L) (base := base) (ε := ε)
    hD (n04bReferencePieces_geometry hD hC hcut e)
  obtain ⟨_, hCan, _, _, hJ, _⟩ :=
    n04bTypedAtlasData_positive_fields C L cut e F h J z m i hi
  simpa only [hCan, hJ] using hA.inverseReflection z hz hs m

end ContinuousFlexibility.Analysis
