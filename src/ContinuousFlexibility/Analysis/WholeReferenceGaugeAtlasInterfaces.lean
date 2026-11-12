import ContinuousFlexibility.Analysis.WholeReferenceGaugeAtlasData
import ContinuousFlexibility.Analysis.WholeCanonicalInterfaceClassification
import ContinuousFlexibility.Analysis.ActualAtlasCutFirstJets

/-!
# Retained physical interfaces and middle-cut jets after reference gauging

The new positive reference gauge changes no physical endpoint and no
negative field. Hence the actual interface classification is the former
one, and the forward middle-cut first jets are those of the same
original negative atlas. Root matching is a separate assertion.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements

theorem n04WholeReferenceGaugeAtlasData_actual_interfaceClassification
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
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
    (N : Set ℝ) :
    CanonicalGeometry.PhysicalInterfaceClassification D
      (n04WholeReferenceGaugeAtlasData C L
        (n04bActualTypedAtlas hT hS hN hfield e₀) e cell ψ χ h₀ τ σ Q N) := by
  change CanonicalGeometry.PhysicalInterfaceClassification D
    (n04WholeCanonicalAtlasData C L
      (n04bActualTypedAtlas hT hS hN hfield e₀) e cell σ τ Q N)
  exact n04WholeCanonicalAtlasData_actual_interfaceClassification
    hT hS hN hfield e₀ e cell σ τ Q N

/-- The displayed new record retains the actual negative cut pair,
cut radius, inverse cut curve, forward charts and heights. -/
theorem n04WholeReferenceGaugeAtlasData_cutFirstJetMatching
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
    (N : Set ℝ) {base : ℕ} {ε : ℝ}
    (hcut : CanonicalGeometry.CutFirstJetMatching S C K base ε) :
    CanonicalGeometry.CutFirstJetMatching S C
      (n04WholeReferenceGaugeAtlasData C L K e cell ψ χ h₀ τ σ Q N) base ε := by
  intro m z hz θ
  have hE (V : CanonicalData S) (j : ℕ) (ρ s : ℝ) :
      CanonicalGeometry.endpointAlignedChart V z j ρ s =
        (fun p : PolarPoint => (s * ((V.chart z j p).1 - ρ), (V.chart z j p).2)) := rfl
  simpa only [hE, canonicalCutPoint,
    n04WholeReferenceGaugeAtlasData, n04WholeCanonicalAtlasData, n04bWithInteriorDivision,
    n04WholeCutPair, Equiv.apply_symm_apply, Bool.false_eq_true, ite_false, ite_true]
    using hcut m z hz θ

end ContinuousFlexibility.Analysis

