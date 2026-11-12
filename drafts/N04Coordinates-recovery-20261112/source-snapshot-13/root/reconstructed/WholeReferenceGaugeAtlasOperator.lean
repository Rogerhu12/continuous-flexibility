import ContinuousFlexibility.Analysis.WholeReferenceGaugeAtlasData
import ContinuousFlexibility.Analysis.WholeCanonicalAtlasOperator

/-!
# Actual operator fields after inserting the fixed reference gauge

The negative operator fields remain the old ones. The positive fields
are defined by the coordinate formula for the new raw chart and height.
The operator identity therefore follows from their actual geometry and
the original physical coefficient regularity at the true inverse image.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

theorem n04WholeReferenceGaugeAtlasData_operatorFields
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
    (N : Set ℝ)
    (hfields : ∀ z m,
      let W := n04WholeCanonicalAtlasData C L K e cell σ τ Q N
      W.coefficients z m = inverseChartPrincipalCoefficients (L.coefficients z)
        (W.chart z m) (W.inverseChart z m) (W.height z m) ∧
      ∀ p, W.potential z m p = (if W.positive m then -1 else (1 : ℝ)) *
        inverseChartPotential (L.coefficients z)
          (W.chart z m) (W.inverseChart z m) (W.height z m) p)
    (z : AnnularState S × ℝ) (m : ℕ) :
    let V := n04WholeReferenceGaugeAtlasData C L K e cell ψ χ h₀ τ σ Q N
    V.coefficients z m = inverseChartPrincipalCoefficients (L.coefficients z)
      (V.chart z m) (V.inverseChart z m) (V.height z m) ∧
      ∀ p, V.potential z m p = (if V.positive m then -1 else (1 : ℝ)) *
        inverseChartPotential (L.coefficients z)
          (V.chart z m) (V.inverseChart z m) (V.height z m) p := by
  cases hi : e m with
  | inl j =>
      simpa only [n04WholeReferenceGaugeAtlasData, n04WholeCanonicalAtlasData,
        n04bWithInteriorDivision, hi] using hfields z m
  | inr i =>
      simp only [n04WholeReferenceGaugeAtlasData, n04WholeCanonicalAtlasData,
        n04bWithInteriorDivision, n04WholePiecePositive, hi, ite_true, neg_one_mul]

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
  (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
  (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
  (hfield : N04bFieldRegularity D S C L base ε)
  (e₀ : ℕ ≃ N04PieceIndex D) (e : ℕ ≃ N04WholePieceIndex D)
  (cell : N04PositiveComponent D.a D.b (deriv D.w) → ℕ)
  (ψ χ : N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → PolarPoint)
  (h₀ : N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → ℝ)
  (τ σ : (AnnularState S × ℝ) →
    N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → PolarPoint)
  (Q : (AnnularState S × ℝ) →
    N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → ℝ)
  (N : Set ℝ)

theorem n04WholeReferenceGaugeAtlasData_actual_operatorFields
    (z : AnnularState S × ℝ) (m : ℕ) :
    let V := n04WholeReferenceGaugeAtlasData C L (n04bActualTypedAtlas hT hS hN hfield e₀)
      e cell ψ χ h₀ τ σ Q N
    V.coefficients z m = inverseChartPrincipalCoefficients (L.coefficients z)
      (V.chart z m) (V.inverseChart z m) (V.height z m) ∧
      ∀ p, V.potential z m p = (if V.positive m then -1 else (1 : ℝ)) *
        inverseChartPotential (L.coefficients z)
          (V.chart z m) (V.inverseChart z m) (V.height z m) p :=
  n04WholeReferenceGaugeAtlasData_operatorFields C L
    (n04bActualTypedAtlas hT hS hN hfield e₀) e cell ψ χ h₀ τ σ Q N
    (n04WholeCanonicalAtlasData_actual_operatorFields hT hS hN hfield e₀ e cell σ τ Q N) z m

theorem n04WholeReferenceGaugeAtlasData_actual_operator
    (hA : CanonicalGeometry D S C
      (n04WholeReferenceGaugeAtlasData C L (n04bActualTypedAtlas hT hS hN hfield e₀)
        e cell ψ χ h₀ τ σ Q N) base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (u : PolarPoint → ℝ) (hu : ContDiff ℝ ∞ u)
    (p : PolarPoint) (hp : p ∈ canonicalOpen S
      (n04WholeReferenceGaugeAtlasData C L (n04bActualTypedAtlas hT hS hN hfield e₀)
        e cell ψ χ h₀ τ σ Q N) m) :
    let V := n04WholeReferenceGaugeAtlasData C L (n04bActualTypedAtlas hT hS hN hfield e₀)
      e cell ψ χ h₀ τ σ Q N
    canonicalOperator S V L z m u p =
      (if V.positive m then -1 else (1 : ℝ)) *
        divergenceOperator (V.coefficients z m) u p + V.potential z m p * u p := by
  have hx := (hA.charts z hz hs m).2.1 hp
  obtain ⟨ha, hb, hc⟩ := n04b_field_contDiffAt_on_piece hA hfield hz hs m hx
  have hop := n04b_canonicalOperator_explicit_fields hA hz hs m hp ha hb hc u hu
  have hf := n04WholeReferenceGaugeAtlasData_actual_operatorFields
    hT hS hN hfield e₀ e cell ψ χ h₀ τ σ Q N z m
  rw [← hf.1, ← hf.2 p] at hop
  exact hop

end ContinuousFlexibility.Analysis
