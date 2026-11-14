module

public import ContinuousFlexibility.Analysis.WholeReferenceGaugeAtlasData

/-!
# The original relative fields in the reference-gauged whole atlas

The fixed reference chart and height cancel from the actual current-point,
reference-point and height-ratio definitions. The same relative maps and
height remain in the record; no new family or width is selected.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

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

theorem n04WholeReferenceGaugeAtlasData_positive_reference_fields
    (m : ℕ) (i : N04PositiveComponent D.a D.b (deriv D.w)) (hi : e m = .inr i)
    (hτref : τ (C.referenceState, 0) i = id)
    (hσref : σ (C.referenceState, 0) i = id)
    (hQref : Q (C.referenceState, 0) i = (fun _ => 1)) :
    let V := n04WholeReferenceGaugeAtlasData C L K e cell ψ χ h₀ τ σ Q N
    V.chart (C.referenceState, 0) m = ψ i ∧
      V.inverseChart (C.referenceState, 0) m = χ i ∧
      V.height (C.referenceState, 0) m = h₀ i := by
  obtain ⟨_, _, _, _, _, _, _, hF, hG, hh, _, _⟩ :=
    n04WholeReferenceGaugeAtlasData_positive_fields C L K e cell ψ χ h₀ τ σ Q N
      (C.referenceState, 0) m i hi
  have href := wholePositiveReferenceGauge_reference (ψ i) (χ i) (h₀ i)
    hτref hσref hQref
  exact ⟨hF.trans href.1, hG.trans href.2.1, hh.trans href.2.2⟩

theorem n04WholeReferenceGaugeAtlasData_positive_relative_fields
    (z : AnnularState S × ℝ) (m : ℕ)
    (i : N04PositiveComponent D.a D.b (deriv D.w)) (hi : e m = .inr i)
    (hτref : τ (C.referenceState, 0) i = id)
    (hσref : σ (C.referenceState, 0) i = id)
    (hQref : Q (C.referenceState, 0) i = (fun _ => 1))
    (hχψ : Function.LeftInverse (χ i) (ψ i))
    (hστ : Function.LeftInverse (σ z i) (τ z i)) (hh₀ : ∀ p, h₀ i p ≠ 0) :
    let V := n04WholeReferenceGaugeAtlasData C L K e cell ψ χ h₀ τ σ Q N
    canonicalCurrentPoint C V z m = τ z i ∧
      canonicalReferencePoint C V z m = σ z i ∧
      n04CoordinatesCurrentHeightRatio C V z m = Q z i := by
  let V := n04WholeReferenceGaugeAtlasData C L K e cell ψ χ h₀ τ σ Q N
  obtain ⟨hF₀, hG₀, hh₀field⟩ :=
    n04WholeReferenceGaugeAtlasData_positive_reference_fields
      C L K e cell ψ χ h₀ τ σ Q N m i hi hτref hσref hQref
  obtain ⟨_, _, _, _, _, _, _, hF, hG, hh, _, _⟩ :=
    n04WholeReferenceGaugeAtlasData_positive_fields C L K e cell ψ χ h₀ τ σ Q N z m i hi
  have hrelative := wholePositiveReferenceGauge_relative_fields (Q := Q z i) hχψ hστ hh₀
  have hcurrent : canonicalCurrentPoint C V z m = τ z i := by
    funext p
    change V.inverseChart z m (V.chart (C.referenceState, 0) m p) = τ z i p
    rw [hF₀, hG]
    exact congrFun hrelative.1 p
  have hreference : canonicalReferencePoint C V z m = σ z i := by
    funext p
    change V.inverseChart (C.referenceState, 0) m (V.chart z m p) = σ z i p
    rw [hG₀, hF]
    exact congrFun hrelative.2.1 p
  refine ⟨hcurrent, hreference, ?_⟩
  funext p
  change V.height (C.referenceState, 0) m p /
    V.height z m (canonicalCurrentPoint C V z m p) = Q z i p
  rw [hh₀field, hh, hcurrent]
  exact hrelative.2.2 p

theorem n04WholeReferenceGaugeAtlasData_negative_relative_fields
    (z : AnnularState S × ℝ) (m : ℕ) (j : ℕ × Bool) (hi : e m = .inl j) :
    let V := n04WholeReferenceGaugeAtlasData C L K e cell ψ χ h₀ τ σ Q N
    let k := if j.2 then (K.cutPair j.1).2 else (K.cutPair j.1).1
    canonicalCurrentPoint C V z m = canonicalCurrentPoint C K z k ∧
      canonicalReferencePoint C V z m = canonicalReferencePoint C K z k ∧
      n04CoordinatesCurrentHeightRatio C V z m = n04CoordinatesCurrentHeightRatio C K z k := by
  obtain ⟨_, _, _, _, _, _, _, hF₀, hG₀, hh₀field, _, _⟩ :=
    n04WholeReferenceGaugeAtlasData_negative_fields C L K e cell ψ χ h₀ τ σ Q N
      (C.referenceState, 0) m j hi
  obtain ⟨_, _, _, _, _, _, _, hF, hG, hh, _, _⟩ :=
    n04WholeReferenceGaugeAtlasData_negative_fields C L K e cell ψ χ h₀ τ σ Q N z m j hi
  refine ⟨?_, ?_, ?_⟩
  · funext p
    simp only [canonicalCurrentPoint, hF₀, hG]
  · funext p
    simp only [canonicalReferencePoint, hF, hG₀]
  · funext p
    simp only [n04CoordinatesCurrentHeightRatio, canonicalCurrentPoint, hh₀field, hh, hF₀, hG]

end ContinuousFlexibility.Analysis
