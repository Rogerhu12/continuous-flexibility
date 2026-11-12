import ContinuousFlexibility.Analysis.CanonicalAuxiliaryAtomPreservation
import ContinuousFlexibility.Analysis.CanonicalAuxiliaryReferenceJets
import ContinuousFlexibility.Analysis.CanonicalAuxiliaryDifferenceJets

/-!
# One auxiliary column for the actual whole reference-gauged atlas

Choose the buffered component, interval and column once.  The resulting
physical spaces keep their actual Q and every underlying state and
geometric function.  The same column has the reference bounds and zero
current difference tower proved earlier.  Material enlargement is an
explicit returned operation, not a floor imposed on the original E0.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open CanonicalGeometry
open scoped ContDiff

theorem exists_wholeReferenceGauge_auxiliary_package
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (K : CanonicalData S) (e : ℕ ≃ N04WholePieceIndex D)
    (cell : N04PositiveComponent D.a D.b (deriv D.w) → ℕ)
    (ψ χ : N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → PolarPoint)
    (h₀ : N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → ℝ)
    (τ σ : (AnnularState S × ℝ) →
      N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → PolarPoint)
    (Q : (AnnularState S × ℝ) →
      N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → ℝ)
    {F : Set ℝ} (B : N04PositiveNormalizationBuffer D.a D.b (deriv D.w) F)
    (hA : CanonicalGeometry D S C
      (n04WholeReferenceGaugeAtlasData C L K e cell ψ χ h₀ τ σ Q B.region) base ε)
    (hR : ReferenceRadial S C
      (n04WholeReferenceGaugeAtlasData C L K e cell ψ χ h₀ τ σ Q B.region)) :
    let V := n04WholeReferenceGaugeAtlasData C L K e cell ψ χ h₀ τ σ Q B.region
    let T' := enlargedMaterialData T
    ∃ (i : N04PositiveComponent D.a D.b (deriv D.w)) (l u : ℝ)
      (η : (S.height (3 / 4 : ℝ)).Space),
      let S' := physicalSpacesReplaceAuxiliaryColumn S η
      let C' := geometryReplaceAuxiliaryColumn C η
      let R' := returnReplaceAuxiliaryColumn R η
      let L' := correctionReplaceAuxiliaryColumn L η
      let V' := canonicalReplaceAuxiliaryColumn V η
      l < u ∧ Icc l u ⊆ Ioo (B.normalizationLeft i) (B.normalizationRight i) ∧
      IsMaterialData D T' ∧ IsPhysicalSpaces D T' S' ∧
      NonlinearPropertiesThrough03 D T' S' C' R' L' base loss ε ∧
      CanonicalGeometry D S' C' V' base ε ∧ ReferenceRadial S' C' V' ∧
      AuxiliaryColumnGauge S' V' ∧ S'.Q S'.psi = 1 ∧
      HasCompactRadialSupport D ((S'.height (3 / 4 : ℝ)).decode S'.psi) ∧
      (∀ p : PolarPoint, (S'.height (3 / 4 : ℝ)).decode S'.psi p ≠ 0 →
        p.1 ∈ Icc l u) ∧
      Icc l u ⊆ Ioo (V'.physicalLeft (e.symm (.inr i)))
        (V'.physicalRight (e.symm (.inr i))) ∧
      (∀ m, ContDiffOn ℝ ∞
          (atom D T' S' C' L' V' (C'.referenceState, 0) m .auxiliaryColumn) unitStrip ∧
        ∀ p ∈ unitStrip,
          atom D T' S' C' L' V' (C'.referenceState, 0) m .auxiliaryColumn
            (p + (0, Real.pi)) =
          atom D T' S' C' L' V' (C'.referenceState, 0) m .auxiliaryColumn p) ∧
      (∀ s : ℕ, ∃ A : ℝ, 0 < A ∧ ∀ m p, p ∈ unitStrip →
        ∀ a b : ℕ, a + b ≤ s →
          |mixedDerivative a b
            (atom D T' S' C' L' V' (C'.referenceState, 0) m .auxiliaryColumn) p| ≤
            A * T'.E0 (T'.sample (V'.cell m)) ^ A) ∧
      (∀ z ∈ stateNeighborhood S' C' base ε, stateSector S' z.1 → ∀ m,
        EqOn (atom D T' S' C' L' V' z m .auxiliaryColumn)
          (atom D T' S' C' L' V' (C'.referenceState, 0) m .auxiliaryColumn) unitStrip) ∧
      (∀ z ∈ sectorNeighborhood S' base ε ε, ∀ m a b (p : unitStrip),
        differenceJets D T' S' C' L' V' z .auxiliaryColumn m a b p = 0) ∧
      (∃ J : SmoothDirections (sectorNeighborhood S' base ε ε)
          (fun z : Parameter S' => differenceJets D T' S' C' L' V' z .auxiliaryColumn),
        ∀ k z v, J.D k z v = 0) ∧
      ∀ a : Atom, a ≠ .auxiliaryColumn → a ≠ .ratioE0 → a ≠ .ratioE0Inverse →
        ∀ z m, atom D T' S' C' L' V' z m a = atom D T S C L V z m a := by
  let V := n04WholeReferenceGaugeAtlasData C L K e cell ψ χ h₀ τ σ Q B.region
  obtain ⟨i, l, u, η, hlu, hinterval, hSη, hNη, hAη, hgauge, hQη,
      hcompact, hsupport, _⟩ :=
    exists_buffered_auxiliaryColumn_replacement_with_witness
      (K := V) hT hS hN hA B rfl
  let S' := physicalSpacesReplaceAuxiliaryColumn S η
  let C' := geometryReplaceAuxiliaryColumn C η
  let R' := returnReplaceAuxiliaryColumn R η
  let L' := correctionReplaceAuxiliaryColumn L η
  let V' := canonicalReplaceAuxiliaryColumn V η
  have hRη : ReferenceRadial S' C' V' :=
    canonicalReferenceRadial_replaceAuxiliaryColumn hR η
  have hintervalV : Icc l u ⊆ Ioo (V'.physicalLeft (e.symm (.inr i)))
      (V'.physicalRight (e.symm (.inr i))) :=
    wholeReferenceGauge_auxiliary_support_interval C L K e cell ψ χ h₀ τ σ Q
      B.region B i hinterval
  obtain ⟨hT', hS', hN', hregular, hbound⟩ :=
    canonical_auxiliaryReferenceJets_enlargedMaterialData hT hSη hNη hAη hRη
      hgauge (e.symm (.inr i)) hintervalV hsupport
  refine ⟨i, l, u, η, hlu, hinterval, hT', hS', hN', hAη, hRη, hgauge, hQη,
    hcompact, hsupport, hintervalV, hregular, hbound, ?_, ?_, ?_, ?_⟩
  · intro z hz hs m
    exact canonical_auxiliaryColumn_eqOn_reference hN' hAη hgauge hz hs m
  · intro z hz m a b p
    exact canonical_auxiliaryDifferenceJets_eq_zero hN' hAη hgauge hz m a b p
  · exact exists_canonicalAuxiliaryDifference_zero_tower hN' hAη hgauge
  · intro a ha hE hEi z m
    exact canonicalAtom_auxiliaryReplacement_enlarged_of_ne D T S C L V η z m a ha hE hEi

end ContinuousFlexibility.Analysis
