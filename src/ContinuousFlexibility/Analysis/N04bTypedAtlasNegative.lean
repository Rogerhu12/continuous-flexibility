module

public import ContinuousFlexibility.Analysis.N04bTypedAtlasPositive
public import ContinuousFlexibility.Analysis.N04bNegativePieceGeometry

/-!
# Negative fields of the same concrete typed atlas

At a negative typed index the record contains the actual constructed
negative functions. Their proved geometric output gives the four
remaining chart clauses of CanonicalGeometry, without changing either
the moving physical domain or its fixed canonical interval.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
  (e : ℕ ≃ N04PieceIndex D)
  (F : (AnnularState S × ℝ) → ℕ → Bool → PolarPoint → PolarPoint)
  (h : (AnnularState S × ℝ) → ℕ → Bool → PolarPoint → ℝ)
  (J : (AnnularState S × ℝ) → ℕ → Bool → PolarPoint → PolarPoint)
  (cut : ℕ → ℝ) {z : AnnularState S × ℝ}
  (k m : ℕ) (side : Bool) (hi : e k = .inl (m, side))

include hi in
theorem n04bTypedAtlasData_negative_fields :
    let K := n04bTypedAtlasData D S C L cut e F h J
    physicalPieceOpen S K z k = n04bActualNegativeDomain S C L z m side ∧
      canonicalOpen S K k =
        Ioo (0 : ℝ) (n04bRootCutRadius (C.travel m)) ×ˢ (univ : Set ℝ) ∧
      canonicalClosed S K k =
        Icc (0 : ℝ) (n04bRootCutRadius (C.travel m)) ×ˢ (univ : Set ℝ) ∧
      K.chart z k = F z m side ∧ K.inverseChart z k = J z m side ∧
      K.height z k = h z m side := by
  simp only [n04bTypedAtlasData_physicalPieceOpen,
    n04bTypedAtlasData_chart, n04bTypedAtlasData_inverseChart,
    n04bTypedAtlasData_height, canonicalOpen, canonicalClosed,
    n04bTypedAtlasData_left, n04bTypedAtlasData_right, hi,
    n04bTypedAtlasChart, n04bTypedAtlasInverse, n04bTypedAtlasHeight,
    n04bTypedPhysicalDomain, n04bActualNegativeDomain, and_self]

variable
  (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
  (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
  (hfield : N04bFieldRegularity D S C L base ε)
  (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
  (H : N04bNegativePieceProperties S C L z m side (F z m side) (h z m side) (J z m side))

include hi hN hS hT hfield hz hs H

theorem n04bTypedAtlasData_negative_charts :
    let K := n04bTypedAtlasData D S C L cut e F h J
    MapsTo (K.chart z k) (physicalPieceOpen S K z k) (canonicalOpen S K k) ∧
    MapsTo (K.inverseChart z k) (canonicalOpen S K k) (physicalPieceOpen S K z k) ∧
    (∀ p ∈ physicalPieceOpen S K z k, K.inverseChart z k (K.chart z k p) = p) ∧
    (∀ p ∈ canonicalOpen S K k, K.chart z k (K.inverseChart z k p) = p) ∧
    ContDiffOn ℝ ∞ (K.chart z k) (physicalPieceOpen S K z k) ∧
    ContDiffOn ℝ ∞ (K.inverseChart z k) (canonicalOpen S K k) ∧
    ContDiffOn ℝ ∞ (K.height z k) (physicalPieceOpen S K z k) ∧
    (∀ p ∈ physicalPieceOpen S K z k,
      0 < K.height z k p ∧ planeJacobian (K.chart z k) p ≠ 0 ∧
      K.chart z k (p + (0, Real.pi)) = K.chart z k p + (0, Real.pi) ∧
      K.height z k (p + (0, Real.pi)) = K.height z k p) := by
  obtain ⟨hΩ, hCan, _, hF, hJ, hh⟩ :=
    n04bTypedAtlasData_negative_fields (C := C) (L := L) (z := z)
      e F h J cut k m side hi
  simpa only [hΩ, hCan, hF, hJ, hh] using H.charts hN hS hT hfield hz hs

theorem n04bTypedAtlasData_negative_boundary :
    let K := n04bTypedAtlasData D S C L cut e F h J
    MapsTo (K.chart z k) (physicalPieceClosed S K z k) (canonicalClosed S K k) ∧
    MapsTo (K.inverseChart z k) (canonicalClosed S K k) (physicalPieceClosed S K z k) ∧
    (∀ p ∈ physicalPieceClosed S K z k, K.inverseChart z k (K.chart z k p) = p) ∧
    (∀ p ∈ canonicalClosed S K k, K.chart z k (K.inverseChart z k p) = p) ∧
    (∀ p ∈ physicalPieceClosed S K z k,
      ContDiffAt ℝ ∞ (K.chart z k) p ∧ ContDiffAt ℝ ∞ (K.height z k) p ∧
        planeJacobian (K.chart z k) p ≠ 0 ∧ 0 < K.height z k p) ∧
    (∀ p ∈ frontier (physicalPieceOpen S K z k),
      CanonicalBoundaryInverseGerm (K.chart z k) (K.inverseChart z k) p) := by
  obtain ⟨hΩ, _, hCan, hF, hJ, hh⟩ :=
    n04bTypedAtlasData_negative_fields (C := C) (L := L) (z := z)
      e F h J cut k m side hi
  simpa only [physicalPieceClosed, hΩ, hCan, hF, hJ, hh] using
    H.boundary hN hS hT hfield hz hs

theorem n04bTypedAtlasData_negative_reflection :
    let K := n04bTypedAtlasData D S C L cut e F h J
    ∀ p ∈ physicalPieceOpen S K z k,
      K.chart z k (p.1, -p.2) = ((K.chart z k p).1, -(K.chart z k p).2) ∧
      K.height z k (p.1, -p.2) = K.height z k p ∧
      planeJacobian (K.chart z k) (p.1, -p.2) = planeJacobian (K.chart z k) p := by
  obtain ⟨hΩ, _, _, hF, _, hh⟩ :=
    n04bTypedAtlasData_negative_fields (C := C) (L := L) (z := z)
      e F h J cut k m side hi
  simpa only [hΩ, hF, hh] using
    (fun p hp => H.reflection hN hS hT hfield hz hs (p := p) hp)

theorem n04bTypedAtlasData_negative_inverseReflection :
    let K := n04bTypedAtlasData D S C L cut e F h J
    ∀ p ∈ canonicalOpen S K k,
      K.inverseChart z k (p.1, -p.2) =
        ((K.inverseChart z k p).1, -(K.inverseChart z k p).2) := by
  obtain ⟨_, hCan, _, _, hJ, _⟩ :=
    n04bTypedAtlasData_negative_fields (C := C) (L := L) (z := z)
      e F h J cut k m side hi
  simpa only [hCan, hJ] using
    (fun p hp => H.inverseReflection hN hS hT hfield hz hs (q := p) hp)

end ContinuousFlexibility.Analysis
