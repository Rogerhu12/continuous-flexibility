import ContinuousFlexibility.Analysis.CanonicalSinglePieceReferenceBounds
import ContinuousFlexibility.Analysis.BufferedAuxiliaryColumnWitness
import ContinuousFlexibility.Analysis.MaterialEnvelopeNormalization
import ContinuousFlexibility.Analysis.StateNeighborhood
import ContinuousFlexibility.Analysis.WholeReferenceGaugeAtlasData

/-!
# Reference jets of the retained auxiliary column

The fixed support interval is the one retained when the actual column
was chosen.  No new column or component is selected here.  Compactness
first gives ordinary finite constants for its actual reference source.
The optional material enlargement is explicit and preserves the same
physical spaces, Q, column, state, coefficient fields, and Through03.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open CanonicalGeometry
open scoped ContDiff

/-- The retained buffer interval lies in its actual indexed positive
piece of the same reference-gauged atlas. -/
theorem wholeReferenceGauge_auxiliary_support_interval
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
    (N : Set ℝ) {F : Set ℝ}
    (B : N04PositiveNormalizationBuffer D.a D.b (deriv D.w) F)
    (i : N04PositiveComponent D.a D.b (deriv D.w)) {l u : ℝ}
    (hinterval : Icc l u ⊆ Ioo (B.normalizationLeft i) (B.normalizationRight i)) :
    let V := n04WholeReferenceGaugeAtlasData C L K e cell ψ χ h₀ τ σ Q N
    Icc l u ⊆ Ioo (V.physicalLeft (e.symm (.inr i)))
      (V.physicalRight (e.symm (.inr i))) := by
  have hfields := n04WholeReferenceGaugeAtlasData_positive_fields
    C L K e cell ψ χ h₀ τ σ Q N (C.referenceState, 0)
    (e.symm (.inr i)) i (e.apply_symm_apply (.inr i))
  dsimp only
  rw [hfields.2.2.1, hfields.2.2.2.1]
  intro r hr
  have hn := hinterval hr
  have ho := B.ordered i
  exact ⟨(ho.1.trans ho.2.1).trans hn.1,
    hn.2.trans (ho.2.2.2.1.trans ho.2.2.2.2)⟩

theorem canonical_auxiliaryReference_uniform_bounds
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hA : CanonicalGeometry D S C K base ε)
    (hR : ReferenceRadial S C K) (hψ : AuxiliaryColumnGauge S K)
    (m₀ : ℕ) {l u : ℝ}
    (hinterval : Icc l u ⊆ Ioo (K.physicalLeft m₀) (K.physicalRight m₀))
    (hsupport : ∀ p : PolarPoint,
      (S.height (3 / 4 : ℝ)).decode S.psi p ≠ 0 → p.1 ∈ Icc l u) :
    (∀ m, ContDiffOn ℝ ∞ (atom D T S C L K (C.referenceState, 0) m .auxiliaryColumn)
      unitStrip ∧ ∀ p ∈ unitStrip,
        atom D T S C L K (C.referenceState, 0) m .auxiliaryColumn (p + (0, Real.pi)) =
          atom D T S C L K (C.referenceState, 0) m .auxiliaryColumn p) ∧
    ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ m p, p ∈ unitStrip →
      ∀ i j : ℕ, i + j ≤ s →
        |mixedDerivative i j
          (atom D T S C L K (C.referenceState, 0) m .auxiliaryColumn) p| ≤ B := by
  have hf : ContDiffOn ℝ ∞ ((S.height (3 / 4 : ℝ)).decode S.psi) (annularOpen D) :=
    ((hS.1 (3 / 4 : ℝ)).2.2.2.1 S.psi).1
  obtain ⟨hregular, hbound⟩ := canonicalReferenceUnitSource_singlePiece_bounds hA
    (reference_mem_stateNeighborhood S C base hN.1.1.2.1)
    hN.1.1.2.2.1.stateSector hR ((S.height (3 / 4 : ℝ)).decode S.psi)
    hf hψ.1 m₀ hinterval hsupport
  refine ⟨hregular, fun s => ?_⟩
  obtain ⟨B, hB, hb⟩ := hbound s
  exact ⟨B, hB, fun m p hp i j hij => hb m i j p hp hij⟩

/-- Only E0 is enlarged.  In particular the displayed atom still uses
the same actual Q-normalized auxiliary column in the same height space. -/
theorem canonical_auxiliaryReferenceJets_enlargedMaterialData
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hA : CanonicalGeometry D S C K base ε)
    (hR : ReferenceRadial S C K) (hψ : AuxiliaryColumnGauge S K)
    (m₀ : ℕ) {l u : ℝ}
    (hinterval : Icc l u ⊆ Ioo (K.physicalLeft m₀) (K.physicalRight m₀))
    (hsupport : ∀ p : PolarPoint,
      (S.height (3 / 4 : ℝ)).decode S.psi p ≠ 0 → p.1 ∈ Icc l u) :
    let T' := enlargedMaterialData T
    IsMaterialData D T' ∧ IsPhysicalSpaces D T' S ∧
      NonlinearPropertiesThrough03 D T' S C R L base loss ε ∧
      (∀ m, ContDiffOn ℝ ∞ (atom D T' S C L K (C.referenceState, 0) m .auxiliaryColumn)
        unitStrip ∧ ∀ p ∈ unitStrip,
          atom D T' S C L K (C.referenceState, 0) m .auxiliaryColumn (p + (0, Real.pi)) =
            atom D T' S C L K (C.referenceState, 0) m .auxiliaryColumn p) ∧
      ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ m p, p ∈ unitStrip →
        ∀ i j : ℕ, i + j ≤ s →
          |mixedDerivative i j
            (atom D T' S C L K (C.referenceState, 0) m .auxiliaryColumn) p| ≤
              B * T'.E0 (T'.sample (K.cell m)) ^ B := by
  have hD : IsAccumulatingProfile D := hN.1.1.1.1
  obtain ⟨hregular, hbound⟩ := canonical_auxiliaryReference_uniform_bounds
    hS hN hA hR hψ m₀ hinterval hsupport
  refine ⟨isMaterialData_enlargedMaterialData hD hT,
    isPhysicalSpaces_enlargedMaterialData hS,
    nonlinearPropertiesThrough03_enlargedMaterialData hT hN, hregular, ?_⟩
  intro s
  obtain ⟨C₀, hC₀, hb⟩ := hbound s
  obtain ⟨B, hB, hpack⟩ := coefficientEnvelope_pack C₀ 0
  refine ⟨B, hB, fun m p hp i j hij => ?_⟩
  have hfloor : 1 ≤ (enlargedMaterialData T).E0
      ((enlargedMaterialData T).sample (K.cell m)) :=
    one_le_enlargedMaterialData_E0 hT (materialSample_mem_interval hD hT (K.cell m))
  have hcost : C₀ ≤ B * (enlargedMaterialData T).E0
      ((enlargedMaterialData T).sample (K.cell m)) ^ B := by
    simpa only [Real.rpow_zero, mul_one] using hpack _ hfloor
  exact (hb m p hp i j hij).trans hcost

end ContinuousFlexibility.Analysis
