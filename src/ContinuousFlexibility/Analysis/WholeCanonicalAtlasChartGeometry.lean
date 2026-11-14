module

public import ContinuousFlexibility.Analysis.WholeCanonicalAtlasData

/-!
# Open and closed chart fields of the whole-component atlas

Negative halves retain their actual stored functions and domains. Positive
pieces use the proved global inverse transport and its reciprocal height.
Every statement here is about the single atlas data constructor.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

variable {D : ReferenceData} {S : PhysicalSpacesData}
  (C : NonlinearGeometryData S) (L : ReturnCorrectionData S) (K : CanonicalData S)
  (e : ℕ ≃ N04WholePieceIndex D)
  (cell : N04PositiveComponent D.a D.b (deriv D.w) → ℕ)
  (F G : (AnnularState S × ℝ) →
    N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → PolarPoint)
  (Q : (AnnularState S × ℝ) →
    N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → ℝ)
  (N : Set ℝ) {base : ℕ} {ε : ℝ}
  (hK : CanonicalGeometry D S C K base ε)
  {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
  (hs : stateSector S z.1)
  {c d : N04PositiveComponent D.a D.b (deriv D.w) → ℝ}
  (hpositive : ∀ i, WholePositiveChartGeometry (F z i) (G z i)
    (wholePositiveChartHeight (F z i) (Q z i))
    (n04PositiveLeft i) (n04PositiveRight i) (c i) (d i))

include hK hz hs hpositive in
theorem n04WholeCanonicalAtlasData_charts (m : ℕ) :
    let W := n04WholeCanonicalAtlasData C L K e cell F G Q N
    MapsTo (W.chart z m) (physicalPieceOpen S W z m) (canonicalOpen S W m) ∧
    MapsTo (W.inverseChart z m) (canonicalOpen S W m) (physicalPieceOpen S W z m) ∧
    (∀ p ∈ physicalPieceOpen S W z m, W.inverseChart z m (W.chart z m p) = p) ∧
    (∀ p ∈ canonicalOpen S W m, W.chart z m (W.inverseChart z m p) = p) ∧
    ContDiffOn ℝ ∞ (W.chart z m) (physicalPieceOpen S W z m) ∧
    ContDiffOn ℝ ∞ (W.inverseChart z m) (canonicalOpen S W m) ∧
    ContDiffOn ℝ ∞ (W.height z m) (physicalPieceOpen S W z m) ∧
    (∀ p ∈ physicalPieceOpen S W z m,
      0 < W.height z m p ∧ planeJacobian (W.chart z m) p ≠ 0 ∧
      W.chart z m (p + (0, Real.pi)) = W.chart z m p + (0, Real.pi) ∧
      W.height z m (p + (0, Real.pi)) = W.height z m p) := by
  cases hi : e m with
  | inl j =>
      simpa only [n04WholeCanonicalAtlasData, n04bWithInteriorDivision,
        physicalPieceOpen, canonicalOpen, hi] using
        hK.charts z hz hs (if j.2 then (K.cutPair j.1).2 else (K.cutPair j.1).1)
  | inr i =>
      simpa only [n04WholeCanonicalAtlasData, n04bWithInteriorDivision,
        physicalPieceOpen, canonicalOpen, hi] using (hpositive i).open_fields

include hK hz hs hpositive in
theorem n04WholeCanonicalAtlasData_boundary
    (hf : Continuous (deriv D.w)) (m : ℕ) :
    let W := n04WholeCanonicalAtlasData C L K e cell F G Q N
    MapsTo (W.chart z m) (physicalPieceClosed S W z m) (canonicalClosed S W m) ∧
    MapsTo (W.inverseChart z m) (canonicalClosed S W m) (physicalPieceClosed S W z m) ∧
    (∀ p ∈ physicalPieceClosed S W z m, W.inverseChart z m (W.chart z m p) = p) ∧
    (∀ p ∈ canonicalClosed S W m, W.chart z m (W.inverseChart z m p) = p) ∧
    (∀ p ∈ physicalPieceClosed S W z m,
      ContDiffAt ℝ ∞ (W.chart z m) p ∧ ContDiffAt ℝ ∞ (W.height z m) p ∧
      planeJacobian (W.chart z m) p ≠ 0 ∧ 0 < W.height z m p) ∧
    (∀ p ∈ frontier (physicalPieceOpen S W z m),
      CanonicalBoundaryInverseGerm (W.chart z m) (W.inverseChart z m) p) := by
  cases hi : e m with
  | inl j =>
      simpa only [n04WholeCanonicalAtlasData, n04bWithInteriorDivision,
        physicalPieceOpen, physicalPieceClosed, canonicalClosed, hi] using
        hK.boundary z hz hs (if j.2 then (K.cutPair j.1).2 else (K.cutPair j.1).1)
  | inr i =>
      simpa only [n04WholeCanonicalAtlasData, n04bWithInteriorDivision,
        physicalPieceOpen, physicalPieceClosed, canonicalClosed, hi] using
        (hpositive i).boundary_fields (n04PositiveComponent_bounds hf i).2.1

include hK hz hs hpositive in
theorem n04WholeCanonicalAtlasData_reflection (m : ℕ) :
    let W := n04WholeCanonicalAtlasData C L K e cell F G Q N
    ∀ p ∈ physicalPieceOpen S W z m,
      W.chart z m (p.1, -p.2) = ((W.chart z m p).1, -(W.chart z m p).2) ∧
      W.height z m (p.1, -p.2) = W.height z m p ∧
      planeJacobian (W.chart z m) (p.1, -p.2) = planeJacobian (W.chart z m) p := by
  cases hi : e m with
  | inl j =>
      simpa only [n04WholeCanonicalAtlasData, n04bWithInteriorDivision,
        physicalPieceOpen, hi] using
        hK.reflection z hz hs (if j.2 then (K.cutPair j.1).2 else (K.cutPair j.1).1)
  | inr i =>
      dsimp only
      intro p hp
      simpa only [n04WholeCanonicalAtlasData, n04bWithInteriorDivision, hi] using
        And.intro ((hpositive i).reflect p)
          ⟨(hpositive i).height_even p, (hpositive i).jacobian_even p⟩

include hK hz hs hpositive in
theorem n04WholeCanonicalAtlasData_inverseReflection (m : ℕ) :
    let W := n04WholeCanonicalAtlasData C L K e cell F G Q N
    ∀ p ∈ canonicalOpen S W m,
      W.inverseChart z m (p.1, -p.2) =
        ((W.inverseChart z m p).1, -(W.inverseChart z m p).2) := by
  cases hi : e m with
  | inl j =>
      simpa only [n04WholeCanonicalAtlasData, n04bWithInteriorDivision,
        canonicalOpen, hi] using
        hK.inverseReflection z hz hs
          (if j.2 then (K.cutPair j.1).2 else (K.cutPair j.1).1)
  | inr i =>
      dsimp only
      intro p hp
      simpa only [n04WholeCanonicalAtlasData, n04bWithInteriorDivision, hi] using
        (hpositive i).inverse_reflect p

include hK in
theorem n04WholeCanonicalAtlasData_referenceDomain (m : ℕ) :
    let W := n04WholeCanonicalAtlasData C L K e cell F G Q N
    physicalPieceOpen S W (C.referenceState, 0) m = referencePhysicalPieceOpen S W m := by
  cases hi : e m with
  | inl j =>
      simpa only [n04WholeCanonicalAtlasData, n04bWithInteriorDivision,
        physicalPieceOpen, referencePhysicalPieceOpen, hi] using
        hK.referenceDomain (if j.2 then (K.cutPair j.1).2 else (K.cutPair j.1).1)
  | inr i =>
      simp only [n04WholeCanonicalAtlasData, n04bWithInteriorDivision,
        physicalPieceOpen, referencePhysicalPieceOpen, hi]

end ContinuousFlexibility.Analysis
