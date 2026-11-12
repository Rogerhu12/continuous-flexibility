import ContinuousFlexibility.Analysis.WholeCanonicalAtlasCuts
import ContinuousFlexibility.Analysis.WholeCanonicalAtlasOperator
import ContinuousFlexibility.Analysis.WholeCanonicalAtlasPrincipalDensity
import ContinuousFlexibility.Analysis.N04ActualAtlasTransmission

/-!
# Complete cut and operator conditions on the actual whole atlas

Assemble the stored cut geometry, actual physical transmission, full
coordinate operator identity, negative Airy density and the existing
positive interior quotient. The conclusion concerns the same single
record whose geometry is supplied; its fields are never replaced.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements

theorem n04WholeCanonicalAtlasData_actual_cutOperator
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
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
    (hA : CanonicalGeometry D S C
      (n04WholeCanonicalAtlasData C L (n04bActualTypedAtlas hT hS hN hfield e₀)
        e cell F G Q N) base ε) :
    CanonicalCutOperatorProperties S C L
      (n04WholeCanonicalAtlasData C L (n04bActualTypedAtlas hT hS hN hfield e₀)
        e cell F G Q N) base ε := by
  let K := n04bActualTypedAtlas hT hS hN hfield e₀
  let W := n04WholeCanonicalAtlasData C L K e cell F G Q N
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact n04WholeCanonicalAtlasData_cutGeometry C L K e cell F G Q N
      (n04bActualTypedAtlas_cutGeometry hT hS hN hfield e₀)
  · intro z hz hs u hu m θ
    exact n04WholeCanonicalAtlasData_transmission C L K e cell F G Q N
      (fun z hz hs u hu m θ => n04ActualAtlas_transmission
        hT hS hN hfield e₀ hz hs u hu m θ) hz hs u hu m θ
  · intro z hz hs m u hu p hp
    exact n04WholeCanonicalAtlasData_actual_operator
      hT hS hN hfield e₀ e cell F G Q N hA hz hs m u hu p hp
  · intro z hz hs m hm p hp
    have hx : W.inverseChart z m p ∈ physicalPieceOpen S W z m :=
      (hA.charts z hz hs m).2.1 hp
    have hFx : W.chart z m (W.inverseChart z m p) = p :=
      (hA.charts z hz hs m).2.2.2.1 p hp
    have hd := n04WholeCanonicalAtlasData_actual_negativePrincipalDensity
      hT hS hN hfield e₀ e cell F G Q N hz hs m hm _ hx
    have hf := n04WholeCanonicalAtlasData_actual_operatorFields
      hT hS hN hfield e₀ e cell F G Q N z m
    rw [hf.1]
    simpa only [inverseChartPrincipalCoefficients, hFx] using hd
  · intro z hz hs m hm p hp
    exact n04WholeCanonicalAtlasData_factorization C L K e cell F G Q N z m p hp

end ContinuousFlexibility.Analysis
