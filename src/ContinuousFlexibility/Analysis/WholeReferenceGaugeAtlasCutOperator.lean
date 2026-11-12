import ContinuousFlexibility.Analysis.WholeReferenceGaugeAtlasOperator
import ContinuousFlexibility.Analysis.CanonicalSourceConversion
import ContinuousFlexibility.Analysis.CanonicalNeighborhoodRestriction

/-!
# Cut operator conditions and source pairing for the reference-gauged atlas

All cuts use the same negative fields. The new positive operator uses
the actual gauged coordinate formulas and its divided coefficients are
their own interior quotients. The original negative witness is retained
when the common state neighborhood is restricted. Source pairing follows
from the geometry of this same record on its actual domains.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

theorem n04WholeReferenceGaugeAtlasData_actual_cutOperator_and_sourcePairing
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base newBase loss : ℕ} {ε ε' : ℝ}
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
    (N : Set ℝ) (hb : base ≤ newBase) (hε : ε' ≤ ε)
    (hB : CanonicalCutOperatorProperties S C L
      (n04WholeCanonicalAtlasData C L (n04bActualTypedAtlas hT hS hN hfield e₀)
        e cell σ τ Q N) newBase ε')
    (hA : CanonicalGeometry D S C
      (n04WholeReferenceGaugeAtlasData C L (n04bActualTypedAtlas hT hS hN hfield e₀)
        e cell ψ χ h₀ τ σ Q N) newBase ε') :
    let V := n04WholeReferenceGaugeAtlasData C L (n04bActualTypedAtlas hT hS hN hfield e₀)
      e cell ψ χ h₀ τ σ Q N
    CanonicalCutOperatorProperties S C L V newBase ε' ∧
      CanonicalSourcePairing D S C V newBase ε' := by
  let K := n04bActualTypedAtlas hT hS hN hfield e₀
  let W := n04WholeCanonicalAtlasData C L K e cell σ τ Q N
  let V := n04WholeReferenceGaugeAtlasData C L K e cell ψ χ h₀ τ σ Q N
  have hsub := stateNeighborhood_mono S C hb hε
  have hfield' : N04bFieldRegularity D S C L newBase ε' :=
    { smooth_coefficients := fun z hz => hfield.smooth_coefficients z (hsub hz)
      periodic_coefficients := fun z hz => hfield.periodic_coefficients z (hsub hz)
      positive_a := fun z hz => hfield.positive_a z (hsub hz)
      negative_discriminant := fun z hz => hfield.negative_discriminant z (hsub hz) }
  constructor
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · constructor
      · intro m
        simpa only [V, W, n04WholeReferenceGaugeAtlasData, n04WholeCanonicalAtlasData,
          n04bWithInteriorDivision, n04WholeCutPair, Equiv.apply_symm_apply,
          n04WholePiecePositive, Bool.false_eq_true, ite_false, ite_true] using hB.1.1 m
      · intro z hz hs m
        have hcut := hB.1.2 z hz hs m
        have hcurve (A : CanonicalData S) : canonicalCutPoint S A z m =
            (fun θ : ℝ => A.inverseChart z (A.cutPair m).1 (A.cutRadius m, θ)) := rfl
        simpa only [CanonicalCurrentCutPair, hcurve, physicalPieceOpen,
          V, W, n04WholeReferenceGaugeAtlasData, n04WholeCanonicalAtlasData,
          n04bWithInteriorDivision, n04WholeCutPair, Equiv.apply_symm_apply,
          Bool.false_eq_true, ite_false, ite_true] using hcut
    · intro z hz hs u hu m θ
      have htrans := hB.2.1 z hz hs u hu m θ
      have hheight (A : CanonicalData S) (j : ℕ) : canonicalHeight S A z j u =
          (fun p : PolarPoint => u (A.inverseChart z j p) /
            A.height z j (A.inverseChart z j p)) := rfl
      simpa only [hheight, V, W,
        n04WholeReferenceGaugeAtlasData, n04WholeCanonicalAtlasData, n04bWithInteriorDivision,
        n04WholeCutPair, Equiv.apply_symm_apply, Bool.false_eq_true, ite_false, ite_true]
        using htrans
    · intro z hz hs m u hu p hp
      have hx := (hA.charts z hz hs m).2.1 hp
      obtain ⟨ha, hb, hc⟩ := n04b_field_contDiffAt_on_piece hA hfield' hz hs m hx
      have hop := n04b_canonicalOperator_explicit_fields hA hz hs m hp ha hb hc u hu
      have hf := n04WholeReferenceGaugeAtlasData_actual_operatorFields
        hT hS hN hfield e₀ e cell ψ χ h₀ τ σ Q N z m
      rw [← hf.1, ← hf.2 p] at hop
      exact hop
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
