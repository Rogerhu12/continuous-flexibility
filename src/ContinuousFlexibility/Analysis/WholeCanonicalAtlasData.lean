import ContinuousFlexibility.Analysis.N04WholeComponentPieces
import ContinuousFlexibility.Analysis.WholePositiveCanonicalFields
import ContinuousFlexibility.Analysis.N04bPositiveDivision
import ContinuousFlexibility.Analysis.CanonicalClosedTransport

/-!
# One atlas with the retained negative halves and whole positive pieces

One enumeration indexes all fields. Negative pieces retain the actual
stored charts, domains, heights and operator fields of the supplied atlas.
Positive pieces use the constructed inverse transport and relative height.
The existing interior-division constructor supplies the actual quotient.
The positive material labels and normalization region are chosen once by
the reference construction and remain explicit data here.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements

def n04WholeCanonicalAtlasData
    {D : ReferenceData} {S : PhysicalSpacesData}
    (C : NonlinearGeometryData S) (L : ReturnCorrectionData S) (K : CanonicalData S)
    (e : ℕ ≃ N04WholePieceIndex D)
    (cell : N04PositiveComponent D.a D.b (deriv D.w) → ℕ)
    (F G : (AnnularState S × ℝ) →
      N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → PolarPoint)
    (Q : (AnnularState S × ℝ) →
      N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → ℝ)
    (N : Set ℝ) : CanonicalData S :=
  let neg : ℕ × Bool → ℕ := fun j =>
    if j.2 then (K.cutPair j.1).2 else (K.cutPair j.1).1
  let B : CanonicalData S := {
    left := fun m => match e m with
      | .inl j => K.left (neg j)
      | .inr i => n04PositiveLeft i
    right := fun m => match e m with
      | .inl j => K.right (neg j)
      | .inr i => n04PositiveRight i
    physicalLeft := fun m => match e m with
      | .inl j => K.physicalLeft (neg j)
      | .inr i => n04PositiveLeft i
    physicalRight := fun m => match e m with
      | .inl j => K.physicalRight (neg j)
      | .inr i => n04PositiveRight i
    physicalDomain := fun z m => match e m with
      | .inl j => K.physicalDomain z (neg j)
      | .inr i => Ioo (n04PositiveLeft i) (n04PositiveRight i) ×ˢ univ
    cell := fun m => match e m with
      | .inl j => K.cell (neg j)
      | .inr i => cell i
    positive := fun m => n04WholePiecePositive (e m)
    chart := fun z m => match e m with
      | .inl j => K.chart z (neg j)
      | .inr i => F z i
    inverseChart := fun z m => match e m with
      | .inl j => K.inverseChart z (neg j)
      | .inr i => G z i
    height := fun z m => match e m with
      | .inl j => K.height z (neg j)
      | .inr i => wholePositiveChartHeight (F z i) (Q z i)
    coefficients := fun z m => match e m with
      | .inl j => K.coefficients z (neg j)
      | .inr i => wholePositiveCanonicalCoefficients (L.coefficients z)
          (G z i) (F z i) (Q z i)
    potential := fun z m => match e m with
      | .inl j => K.potential z (neg j)
      | .inr i => wholePositiveCanonicalPotential (L.coefficients z)
          (G z i) (F z i) (Q z i)
    dividedDifference := fun _ _ => ⟨fun _ => 0, fun _ => 0, fun _ => 0⟩
    cutPair := n04WholeCutPair e
    cutRadius := K.cutRadius
    normalizationRegion := N }
  n04bWithInteriorDivision C B

variable {D : ReferenceData} {S : PhysicalSpacesData}
  (C : NonlinearGeometryData S) (L : ReturnCorrectionData S) (K : CanonicalData S)
  (e : ℕ ≃ N04WholePieceIndex D)
  (cell : N04PositiveComponent D.a D.b (deriv D.w) → ℕ)
  (F G : (AnnularState S × ℝ) →
    N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → PolarPoint)
  (Q : (AnnularState S × ℝ) →
    N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → ℝ)
  (N : Set ℝ)

theorem n04WholeCanonicalAtlasData_negative_fields
    (z : AnnularState S × ℝ) (m : ℕ) (j : ℕ × Bool) (hi : e m = .inl j) :
    let W := n04WholeCanonicalAtlasData C L K e cell F G Q N
    let k := if j.2 then (K.cutPair j.1).2 else (K.cutPair j.1).1
    W.left m = K.left k ∧ W.right m = K.right k ∧
      W.physicalLeft m = K.physicalLeft k ∧ W.physicalRight m = K.physicalRight k ∧
      physicalPieceOpen S W z m = physicalPieceOpen S K z k ∧
      W.cell m = K.cell k ∧ W.positive m = false ∧
      W.chart z m = K.chart z k ∧ W.inverseChart z m = K.inverseChart z k ∧
      W.height z m = K.height z k ∧ W.coefficients z m = K.coefficients z k ∧
      W.potential z m = K.potential z k := by
  simp only [n04WholeCanonicalAtlasData, n04bWithInteriorDivision,
    physicalPieceOpen, n04WholePiecePositive, hi, and_self]

theorem n04WholeCanonicalAtlasData_positive_fields
    (z : AnnularState S × ℝ) (m : ℕ)
    (i : N04PositiveComponent D.a D.b (deriv D.w)) (hi : e m = .inr i) :
    let W := n04WholeCanonicalAtlasData C L K e cell F G Q N
    W.left m = n04PositiveLeft i ∧ W.right m = n04PositiveRight i ∧
      W.physicalLeft m = n04PositiveLeft i ∧ W.physicalRight m = n04PositiveRight i ∧
      physicalPieceOpen S W z m =
        Ioo (n04PositiveLeft i) (n04PositiveRight i) ×ˢ (univ : Set ℝ) ∧
      W.cell m = cell i ∧ W.positive m = true ∧
      W.chart z m = F z i ∧ W.inverseChart z m = G z i ∧
      W.height z m = wholePositiveChartHeight (F z i) (Q z i) ∧
      W.coefficients z m = wholePositiveCanonicalCoefficients (L.coefficients z)
        (G z i) (F z i) (Q z i) ∧
      W.potential z m = wholePositiveCanonicalPotential (L.coefficients z)
        (G z i) (F z i) (Q z i) := by
  simp only [n04WholeCanonicalAtlasData, n04bWithInteriorDivision,
    physicalPieceOpen, n04WholePiecePositive, hi, and_self]

theorem n04WholeCanonicalAtlasData_cut_metadata :
    (n04WholeCanonicalAtlasData C L K e cell F G Q N).cutPair = n04WholeCutPair e ∧
      (n04WholeCanonicalAtlasData C L K e cell F G Q N).cutRadius = K.cutRadius ∧
      (n04WholeCanonicalAtlasData C L K e cell F G Q N).normalizationRegion = N :=
  ⟨rfl, rfl, rfl⟩

/-- The frozen coefficient factorization is the existing interior quotient
of this very record, before any endpoint estimates are asserted. -/
theorem n04WholeCanonicalAtlasData_factorization
    (z : AnnularState S × ℝ) (m : ℕ) (p : PolarPoint)
    (hp : p ∈ canonicalOpen S (n04WholeCanonicalAtlasData C L K e cell F G Q N) m) :
    let W := n04WholeCanonicalAtlasData C L K e cell F G Q N
    let d := (p.1 - W.left m) * (W.right m - p.1)
    (W.coefficients z m).a p - (W.coefficients (C.referenceState, 0) m).a p =
        d ^ 3 * (W.dividedDifference z m).a p ∧
    (W.coefficients z m).b p - (W.coefficients (C.referenceState, 0) m).b p =
        d ^ 3 * (W.dividedDifference z m).b p ∧
    (W.coefficients z m).c p - (W.coefficients (C.referenceState, 0) m).c p =
        d ^ 3 * (W.dividedDifference z m).c p :=
  n04bWithInteriorDivision_factorization C
    (n04WholeCanonicalAtlasData C L K e cell F G Q N) z m hp

/-- Reference identity and the actual inverse law identify the stored
positive relative fields with the transport and height originally chosen. -/
theorem n04WholeCanonicalAtlasData_positive_relative_fields
    (z : AnnularState S × ℝ) (m : ℕ)
    (i : N04PositiveComponent D.a D.b (deriv D.w)) (hi : e m = .inr i)
    (hFref : F (C.referenceState, 0) i = id)
    (hQref : Q (C.referenceState, 0) i = (fun _ => (1 : ℝ)))
    (hleft : Function.LeftInverse (F z i) (G z i)) :
    canonicalCurrentPoint C (n04WholeCanonicalAtlasData C L K e cell F G Q N) z m =
        G z i ∧
      n04CoordinatesCurrentHeightRatio C
        (n04WholeCanonicalAtlasData C L K e cell F G Q N) z m = Q z i := by
  constructor
  · funext p
    simp only [canonicalCurrentPoint, n04WholeCanonicalAtlasData,
      n04bWithInteriorDivision, hi, hFref, id_eq]
  · funext p
    simp only [n04CoordinatesCurrentHeightRatio, canonicalCurrentPoint,
      n04WholeCanonicalAtlasData, n04bWithInteriorDivision, hi,
      wholePositiveChartHeight, hFref, hQref, id_eq, hleft,
      inv_one, one_div, inv_inv]

end ContinuousFlexibility.Analysis
