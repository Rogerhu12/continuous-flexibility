import ContinuousFlexibility.Analysis.WholeReferenceGaugeAtlasOperator
import ContinuousFlexibility.Analysis.CanonicalSourceConversion

/-!
# Cut operator conditions and source pairing for the reference-gauged atlas

All cuts use the same negative fields. The new positive operator uses
the actual gauged coordinate formulas and its divided coefficients are
their own interior quotients. Source pairing follows from the geometry
of this same record on its true physical and canonical domains.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

theorem n04WholeReferenceGaugeAtlasData_actual_cutOperator_and_sourcePairing
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
    (N : Set ℝ)
    (hB : CanonicalCutOperatorProperties S C L
      (n04WholeCanonicalAtlasData C L (n04bActualTypedAtlas hT hS hN hfield e₀)
        e cell σ τ Q N) base ε)
    (hA : CanonicalGeometry D S C
      (n04WholeReferenceGaugeAtlasData C L (n04bActualTypedAtlas hT hS hN hfield e₀)
        e cell ψ χ h₀ τ σ Q N) base ε) :
    let V := n04WholeReferenceGaugeAtlasData C L (n04bActualTypedAtlas hT hS hN hfield e₀)
      e cell ψ χ h₀ τ σ Q N
    CanonicalCutOperatorProperties S C L V base ε ∧
      CanonicalSourcePairing D S C V base ε := by
  let K := n04bActualTypedAtlas hT hS hN hfield e₀
  let W := n04WholeCanonicalAtlasData C L K e cell σ τ Q N
  let V := n04WholeReferenceGaugeAtlasData C L K e cell ψ χ h₀ τ σ Q N
  constructor
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · constructor
      · intro m
        simpa only [V, W, n04WholeReferenceGaugeAtlasData, n04WholeCanonicalAtlasData,
          n04bWithInteriorDivision, n04WholeCutPair, Equiv.apply_symm_apply,
          n04WholePiecePositive, Bool.false_eq_true, ite_false, ite_true] using hB.1.1 m
      · intro z hz hs m
        simpa only [CanonicalCurrentCutPair, canonicalCutPoint, physicalPieceOpen,
          V, W, n04WholeReferenceGaugeAtlasData, n04WholeCanonicalAtlasData,
          n04bWithInteriorDivision, n04WholeCutPair, Equiv.apply_symm_apply,
          Bool.false_eq_true, ite_false, ite_true] using hB.1.2 z hz hs m
    · intro z hz hs u hu m θ
      simpa only [canonicalHeight, V, W,
        n04WholeReferenceGaugeAtlasData, n04WholeCanonicalAtlasData, n04bWithInteriorDivision,
        n04WholeCutPair, Equiv.apply_symm_apply, Bool.false_eq_true, ite_false, ite_true]
        using hB.2.1 z hz hs u hu m θ
    · intro z hz hs m u hu p hp
      exact n04WholeReferenceGaugeAtlasData_actual_operator
        hT hS hN hfield e₀ e cell ψ χ h₀ τ σ Q N hA hz hs m u hu p hp
    · intro z hz hs m hm p hp
      cases hi : e m with
      | inl j =>
          have hmW : W.positive m = false := hm
          have hpW : p ∈ canonicalOpen S W m := by
            simpa only [V, W, canonicalOpen,
              n04WholeReferenceGaugeAtlasData, n04WholeCanonicalAtlasData,
              n04bWithInteriorDivision, hi] using hp
          simpa only [V, W, n04WholeReferenceGaugeAtlasData, n04WholeCanonicalAtlasData,
            n04bWithInteriorDivision, hi] using hB.2.2.2.1 z hz hs m hmW p hpW
      | inr i =>
          simp only [V, n04WholeReferenceGaugeAtlasData, n04WholeCanonicalAtlasData,
            n04bWithInteriorDivision, hi, n04WholePiecePositive, Bool.true_eq_false] at hm
    · intro z hz hs m hm p hp
      exact n04WholeReferenceGaugeAtlasData_factorization
        C L K e cell ψ χ h₀ τ σ Q N z m p hp
  · intro z hz hs m u f _ _ _ _ _ _
    exact canonicalSource_pairing_of_partA hA hz hs m u f

end ContinuousFlexibility.Analysis
