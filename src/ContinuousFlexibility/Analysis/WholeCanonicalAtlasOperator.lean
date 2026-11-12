import ContinuousFlexibility.Analysis.WholeCanonicalAtlasData
import ContinuousFlexibility.Analysis.N04bActualAtlasCuts
import ContinuousFlexibility.Analysis.N04bGeometricCompletion

/-!
# Actual operator fields of the whole-component atlas

The retained negative fields and the inserted positive fields both use
the same inverse-coordinate formulas. Establish that fact on the one
stored record, then apply the full coordinate operator identity with
physical regularity at its actual inverse image.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped ContDiff
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint

theorem n04WholeCanonicalAtlasData_operatorFields
    {D : ReferenceData} {S : PhysicalSpacesData}
    (C : NonlinearGeometryData S) (L : ReturnCorrectionData S) (K : CanonicalData S)
    (e : ℕ ≃ N04WholePieceIndex D)
    (cell : N04PositiveComponent D.a D.b (deriv D.w) → ℕ)
    (F G : (AnnularState S × ℝ) →
      N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → PolarPoint)
    (Q : (AnnularState S × ℝ) →
      N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → ℝ)
    (N : Set ℝ) (hcut : CanonicalReferenceCutPairs S C K)
    (hfields : ∀ z m,
      K.coefficients z m = inverseChartPrincipalCoefficients (L.coefficients z)
        (K.chart z m) (K.inverseChart z m) (K.height z m) ∧
      ∀ p, K.potential z m p = (if K.positive m then -1 else (1 : ℝ)) *
        inverseChartPotential (L.coefficients z)
          (K.chart z m) (K.inverseChart z m) (K.height z m) p)
    (z : AnnularState S × ℝ) (m : ℕ) :
    let W := n04WholeCanonicalAtlasData C L K e cell F G Q N
    W.coefficients z m = inverseChartPrincipalCoefficients (L.coefficients z)
      (W.chart z m) (W.inverseChart z m) (W.height z m) ∧
      ∀ p, W.potential z m p = (if W.positive m then -1 else (1 : ℝ)) *
        inverseChartPotential (L.coefficients z)
          (W.chart z m) (W.inverseChart z m) (W.height z m) p := by
  dsimp only
  cases hi : e m with
  | inl j =>
      let k := if j.2 then (K.cutPair j.1).2 else (K.cutPair j.1).1
      have hneg : K.positive k = false := by
        rcases j with ⟨j, side⟩
        cases side
        · exact (hcut j).1
        · exact (hcut j).2.1
      simpa only [n04WholeCanonicalAtlasData, n04bWithInteriorDivision, hi,
        n04WholePiecePositive, hneg, Bool.false_eq_true, ite_false] using hfields z k
  | inr i =>
      simp only [n04WholeCanonicalAtlasData, n04bWithInteriorDivision, hi,
        n04WholePiecePositive, ite_true, wholePositiveCanonicalCoefficients,
        wholePositiveCanonicalPotential, neg_one_mul]

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
  (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
  (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
  (hfield : N04bFieldRegularity D S C L base ε)
  (e₀ : ℕ ≃ N04PieceIndex D) (e : ℕ ≃ N04WholePieceIndex D)
  (cell : N04PositiveComponent D.a D.b (deriv D.w) → ℕ)
  (F G : (AnnularState S × ℝ) →
    N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → PolarPoint)
  (Q : (AnnularState S × ℝ) →
    N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → ℝ)
  (N : Set ℝ)

theorem n04WholeCanonicalAtlasData_actual_operatorFields
    (z : AnnularState S × ℝ) (m : ℕ) :
    let W := n04WholeCanonicalAtlasData C L (n04bActualTypedAtlas hT hS hN hfield e₀)
      e cell F G Q N
    W.coefficients z m = inverseChartPrincipalCoefficients (L.coefficients z)
      (W.chart z m) (W.inverseChart z m) (W.height z m) ∧
      ∀ p, W.potential z m p = (if W.positive m then -1 else (1 : ℝ)) *
        inverseChartPotential (L.coefficients z)
          (W.chart z m) (W.inverseChart z m) (W.height z m) p := by
  apply n04WholeCanonicalAtlasData_operatorFields C L
    (n04bActualTypedAtlas hT hS hN hfield e₀) e cell F G Q N
    (n04bActualTypedAtlas_cutGeometry hT hS hN hfield e₀).1
  intro z m
  exact ⟨rfl, fun _ => rfl⟩

theorem n04WholeCanonicalAtlasData_actual_operator
    (hA : CanonicalGeometry D S C
      (n04WholeCanonicalAtlasData C L (n04bActualTypedAtlas hT hS hN hfield e₀)
        e cell F G Q N) base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (u : PolarPoint → ℝ) (hu : ContDiff ℝ ∞ u)
    (p : PolarPoint) (hp : p ∈ canonicalOpen S
      (n04WholeCanonicalAtlasData C L (n04bActualTypedAtlas hT hS hN hfield e₀)
        e cell F G Q N) m) :
    let W := n04WholeCanonicalAtlasData C L (n04bActualTypedAtlas hT hS hN hfield e₀)
      e cell F G Q N
    canonicalOperator S W L z m u p =
      (if W.positive m then -1 else (1 : ℝ)) *
        divergenceOperator (W.coefficients z m) u p + W.potential z m p * u p := by
  have hx := (hA.charts z hz hs m).2.1 hp
  obtain ⟨ha, hb, hc⟩ := n04b_field_contDiffAt_on_piece hA hfield hz hs m hx
  have hop := n04b_canonicalOperator_explicit_fields hA hz hs m hp ha hb hc u hu
  have hf := n04WholeCanonicalAtlasData_actual_operatorFields
    hT hS hN hfield e₀ e cell F G Q N z m
  rw [← hf.1, ← hf.2 p] at hop
  exact hop

end ContinuousFlexibility.Analysis
