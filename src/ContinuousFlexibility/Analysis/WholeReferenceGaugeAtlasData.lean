import ContinuousFlexibility.Analysis.WholeCanonicalAtlasData
import ContinuousFlexibility.Analysis.WholePositiveReferenceGauge

/-!
# One whole atlas with the actual fixed positive reference gauge

The negative fields and all physical domains are retained from the same
whole-component atlas. On each positive piece the fixed reference chart
maps the physical interval to `(0,1)`. Its composite with the existing
relative transport gives the raw chart, inverse and height, and their
actual coordinate formulas define the principal field and potential.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements

def n04WholeReferenceGaugeAtlasData
    {D : ReferenceData} {S : PhysicalSpacesData}
    (C : NonlinearGeometryData S) (L : ReturnCorrectionData S) (K : CanonicalData S)
    (e : ℕ ≃ N04WholePieceIndex D)
    (cell : N04PositiveComponent D.a D.b (deriv D.w) → ℕ)
    (ψ χ : N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → PolarPoint)
    (h₀ : N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → ℝ)
    (τ σ : (AnnularState S × ℝ) →
      N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → PolarPoint)
    (Q : (AnnularState S × ℝ) →
      N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → ℝ)
    (N : Set ℝ) : CanonicalData S :=
  let W := n04WholeCanonicalAtlasData C L K e cell σ τ Q N
  let F := fun z i => wholePositiveReferenceGaugeChart (ψ i) (σ z i)
  let G := fun z i => wholePositiveReferenceGaugeInverse (τ z i) (χ i)
  let h := fun z i => wholePositiveReferenceGaugeHeight (h₀ i) (σ z i) (Q z i)
  let B : CanonicalData S := { W with
    left := fun m => match e m with
      | .inl _ => W.left m
      | .inr _ => 0
    right := fun m => match e m with
      | .inl _ => W.right m
      | .inr _ => 1
    chart := fun z m => match e m with
      | .inl _ => W.chart z m
      | .inr i => F z i
    inverseChart := fun z m => match e m with
      | .inl _ => W.inverseChart z m
      | .inr i => G z i
    height := fun z m => match e m with
      | .inl _ => W.height z m
      | .inr i => h z i
    coefficients := fun z m => match e m with
      | .inl _ => W.coefficients z m
      | .inr i => inverseChartPrincipalCoefficients (L.coefficients z) (F z i) (G z i) (h z i)
    potential := fun z m => match e m with
      | .inl _ => W.potential z m
      | .inr i => fun p => -inverseChartPotential (L.coefficients z) (F z i) (G z i) (h z i) p }
  n04bWithInteriorDivision C B

variable {D : ReferenceData} {S : PhysicalSpacesData}
  (C : NonlinearGeometryData S) (L : ReturnCorrectionData S) (K : CanonicalData S)
  (e : ℕ ≃ N04WholePieceIndex D)
  (cell : N04PositiveComponent D.a D.b (deriv D.w) → ℕ)
  (ψ χ : N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → PolarPoint)
  (h₀ : N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → ℝ)
  (τ σ : (AnnularState S × ℝ) →
    N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → PolarPoint)
  (Q : (AnnularState S × ℝ) →
    N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → ℝ)
  (N : Set ℝ)

theorem n04WholeReferenceGaugeAtlasData_physical_fields :
    let W := n04WholeCanonicalAtlasData C L K e cell σ τ Q N
    let V := n04WholeReferenceGaugeAtlasData C L K e cell ψ χ h₀ τ σ Q N
    V.physicalLeft = W.physicalLeft ∧ V.physicalRight = W.physicalRight ∧
      V.physicalDomain = W.physicalDomain ∧ V.positive = W.positive ∧ V.cell = W.cell ∧
      V.cutPair = W.cutPair ∧ V.cutRadius = W.cutRadius ∧
      V.normalizationRegion = W.normalizationRegion := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem n04WholeReferenceGaugeAtlasData_negative_fields
    (z : AnnularState S × ℝ) (m : ℕ) (j : ℕ × Bool) (hi : e m = .inl j) :
    let V := n04WholeReferenceGaugeAtlasData C L K e cell ψ χ h₀ τ σ Q N
    let k := if j.2 then (K.cutPair j.1).2 else (K.cutPair j.1).1
    V.left m = K.left k ∧ V.right m = K.right k ∧
      V.physicalLeft m = K.physicalLeft k ∧ V.physicalRight m = K.physicalRight k ∧
      physicalPieceOpen S V z m = physicalPieceOpen S K z k ∧
      V.cell m = K.cell k ∧ V.positive m = false ∧
      V.chart z m = K.chart z k ∧ V.inverseChart z m = K.inverseChart z k ∧
      V.height z m = K.height z k ∧ V.coefficients z m = K.coefficients z k ∧
      V.potential z m = K.potential z k := by
  simp only [n04WholeReferenceGaugeAtlasData, n04WholeCanonicalAtlasData,
    n04bWithInteriorDivision, physicalPieceOpen, n04WholePiecePositive, hi, and_self]

theorem n04WholeReferenceGaugeAtlasData_positive_fields
    (z : AnnularState S × ℝ) (m : ℕ)
    (i : N04PositiveComponent D.a D.b (deriv D.w)) (hi : e m = .inr i) :
    let V := n04WholeReferenceGaugeAtlasData C L K e cell ψ χ h₀ τ σ Q N
    let F := wholePositiveReferenceGaugeChart (ψ i) (σ z i)
    let G := wholePositiveReferenceGaugeInverse (τ z i) (χ i)
    let h := wholePositiveReferenceGaugeHeight (h₀ i) (σ z i) (Q z i)
    V.left m = 0 ∧ V.right m = 1 ∧
      V.physicalLeft m = n04PositiveLeft i ∧ V.physicalRight m = n04PositiveRight i ∧
      physicalPieceOpen S V z m =
        Ioo (n04PositiveLeft i) (n04PositiveRight i) ×ˢ (univ : Set ℝ) ∧
      V.cell m = cell i ∧ V.positive m = true ∧
      V.chart z m = F ∧ V.inverseChart z m = G ∧ V.height z m = h ∧
      V.coefficients z m = inverseChartPrincipalCoefficients (L.coefficients z) F G h ∧
      V.potential z m = (fun p => -inverseChartPotential (L.coefficients z) F G h p) := by
  simp only [n04WholeReferenceGaugeAtlasData, n04WholeCanonicalAtlasData,
    n04bWithInteriorDivision, physicalPieceOpen, n04WholePiecePositive, hi, and_self]

/-- The divided field is the actual interior quotient of the new raw
principal field, using its own canonical endpoints. -/
theorem n04WholeReferenceGaugeAtlasData_factorization
    (z : AnnularState S × ℝ) (m : ℕ) (p : PolarPoint)
    (hp : p ∈ canonicalOpen S
      (n04WholeReferenceGaugeAtlasData C L K e cell ψ χ h₀ τ σ Q N) m) :
    let V := n04WholeReferenceGaugeAtlasData C L K e cell ψ χ h₀ τ σ Q N
    let d := (p.1 - V.left m) * (V.right m - p.1)
    (V.coefficients z m).a p - (V.coefficients (C.referenceState, 0) m).a p =
        d ^ 3 * (V.dividedDifference z m).a p ∧
      (V.coefficients z m).b p - (V.coefficients (C.referenceState, 0) m).b p =
        d ^ 3 * (V.dividedDifference z m).b p ∧
      (V.coefficients z m).c p - (V.coefficients (C.referenceState, 0) m).c p =
        d ^ 3 * (V.dividedDifference z m).c p :=
  n04bWithInteriorDivision_factorization C
    (n04WholeReferenceGaugeAtlasData C L K e cell ψ χ h₀ τ σ Q N) z m hp

end ContinuousFlexibility.Analysis
