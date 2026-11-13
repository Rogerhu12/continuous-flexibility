import ContinuousFlexibility.Analysis.ActualWholeReferenceNonAuxiliaryJets
import ContinuousFlexibility.Analysis.WholeReferenceGaugeAuxiliaryPackage

/-!
# All thirty-three reference atoms on the same actual construction

The non-auxiliary producer selects the positive family once. For each
actual whole atlas carrying its constructed geometry, the buffered
auxiliary package selects one physical column with integral one. Its
replacement preserves every other atom at the already enlarged material
data, including both E0 ratios. The resulting ReferenceJets certificate
therefore uses that same atlas, sample and auxiliary column throughout.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements ContinuousFlexibility.Radial
open CanonicalGeometry
open scoped ContDiff

theorem n04Coordinates_actual_whole_referenceJets_with_auxiliary
    {S₀ : SelectedTailData} {K₀ : SeedCentralCutoff} {q length : ℝ}
    (P : SeedRetainedPair S₀ K₀ q length) (hSelected : IsSelectedTail S₀)
    (hband : radialFrequencyBand S₀.chain S₀.Cstar S₀.chain.index 2) (hq : 0 < q)
    {Γ : ConnectedReferenceGeometry} (hΓ : Γ.Realizes)
    (hw : Γ.reference.w = P.pair.profile)
    (hcoordinates : R11aRetainedCoordinates P Γ)
    {T : MaterialData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {R : ReturnEquationData S} {L : ReturnCorrectionData S}
    {base loss : ℕ} {ε κ : ℝ}
    (hT : IsMaterialData Γ.reference T) (hS : IsPhysicalSpaces Γ.reference T S)
    (hN : NonlinearPropertiesThrough03 Γ.reference T S C R L base loss ε)
    (hfield : N04bFieldRegularity Γ.reference S C L base ε)
    (e₀ : ℕ ≃ N04PieceIndex Γ.reference)
    (hE0 : ∀ j, 1 ≤ T.E0 (T.sample j)) (hκ : 0 < κ)
    (hhost : ∀ m, Ioo (C.left m) (C.right m) ⊆ Γ.reference.cells (C.cell m))
    (hoptical : ∀ m x, x ∈ Ioo (C.left m) (C.right m) →
      κ⁻¹ * T.E0 (T.sample (C.cell m)) ^ (-κ) *
        min (x - C.left m) (C.right m - x) ≤
          -deriv Γ.reference.w x / (x * Γ.reference.w x))
    (cell : N04PositiveComponent Γ.reference.a Γ.reference.b (deriv Γ.reference.w) → ℕ)
    (hcell : ∀ i, n04PositiveMidpoint i ∈ Γ.reference.cells (cell i))
    (src : ∀ i : N04PositiveComponent Γ.reference.a Γ.reference.b (deriv Γ.reference.w),
      ∀ side, N04PositiveEndpointSource C i side) :
    let A := n04bActualTypedAtlas hT hS hN hfield e₀
    ∃ Y H : N04PositiveComponent Γ.reference.a Γ.reference.b (deriv Γ.reference.w) → ℝ → ℝ,
      N04PositiveReferenceFamily A src 4 Y H ∧
      ∀ (e : ℕ ≃ N04WholePieceIndex Γ.reference)
        (τ σ : (AnnularState S × ℝ) →
          N04PositiveComponent Γ.reference.a Γ.reference.b (deriv Γ.reference.w) →
            PolarPoint → PolarPoint)
        (Q : (AnnularState S × ℝ) →
          N04PositiveComponent Γ.reference.a Γ.reference.b (deriv Γ.reference.w) →
            PolarPoint → ℝ) (F : Set ℝ)
        (buffer : N04PositiveNormalizationBuffer Γ.reference.a Γ.reference.b
          (deriv Γ.reference.w) F),
        (∀ i, τ (C.referenceState, 0) i = id ∧
          σ (C.referenceState, 0) i = id ∧ Q (C.referenceState, 0) i = (fun _ => 1)) →
      let V := n04WholeReferenceGaugeAtlasData C L A e cell
        (fun i => positiveReferenceCylinderChart (Y i))
        (fun i => positiveReferenceCylinderInverse (Y i))
        (fun i p => H i p.1) τ σ Q buffer.region
      CanonicalGeometry Γ.reference S C V base ε → ReferenceRadial S C V →
      let U := enlargedMaterialData T
      ∃ (i : N04PositiveComponent Γ.reference.a Γ.reference.b (deriv Γ.reference.w))
        (l u : ℝ) (η : (S.height (3 / 4 : ℝ)).Space),
        let S' := physicalSpacesReplaceAuxiliaryColumn S η
        let C' := geometryReplaceAuxiliaryColumn C η
        let R' := returnReplaceAuxiliaryColumn R η
        let L' := correctionReplaceAuxiliaryColumn L η
        let V' := canonicalReplaceAuxiliaryColumn V η
        l < u ∧ Icc l u ⊆ Ioo (buffer.normalizationLeft i) (buffer.normalizationRight i) ∧
        IsMaterialData Γ.reference U ∧ IsPhysicalSpaces Γ.reference U S' ∧
        NonlinearPropertiesThrough03 Γ.reference U S' C' R' L' base loss ε ∧
        CanonicalGeometry Γ.reference S' C' V' base ε ∧ ReferenceRadial S' C' V' ∧
        ReferenceJets Γ.reference U S' C' L' V' ∧
        AuxiliaryColumnGauge S' V' ∧ S'.Q S'.psi = 1 ∧
        HasCompactRadialSupport Γ.reference ((S'.height (3 / 4 : ℝ)).decode S'.psi) ∧
        (∀ p : PolarPoint, (S'.height (3 / 4 : ℝ)).decode S'.psi p ≠ 0 → p.1 ∈ Icc l u) ∧
        Icc l u ⊆ Ioo (V'.physicalLeft (e.symm (.inr i)))
          (V'.physicalRight (e.symm (.inr i))) ∧
        (∀ z ∈ stateNeighborhood S' C' base ε, stateSector S' z.1 → ∀ m,
          EqOn (atom Γ.reference U S' C' L' V' z m .auxiliaryColumn)
            (atom Γ.reference U S' C' L' V' (C'.referenceState, 0) m .auxiliaryColumn)
            unitStrip) ∧
        (∀ z ∈ sectorNeighborhood S' base ε ε, ∀ m a b (p : unitStrip),
          differenceJets Γ.reference U S' C' L' V' z .auxiliaryColumn m a b p = 0) ∧
        (∃ J : SmoothDirections (sectorNeighborhood S' base ε ε)
            (fun z : Parameter S' => differenceJets Γ.reference U S' C' L' V' z .auxiliaryColumn),
          ∀ k z v, J.D k z v = 0) ∧
        ∀ v : Atom, v ≠ .auxiliaryColumn → ∀ z m,
          atom Γ.reference U S' C' L' V' z m v = atom Γ.reference U S C L V z m v := by
  have hprod :=
    n04Coordinates_actual_whole_reference_nonAuxiliaryJets
      P hSelected hband hq hΓ hw hcoordinates hT hS hN hfield e₀
      hE0 hκ hhost hoptical cell hcell src
  let Y : N04PositiveComponent Γ.reference.a Γ.reference.b (deriv Γ.reference.w) → ℝ → ℝ :=
    hprod.choose
  let H : N04PositiveComponent Γ.reference.a Γ.reference.b (deriv Γ.reference.w) → ℝ → ℝ :=
    hprod.choose_spec.choose
  have hfamily := hprod.choose_spec.choose_spec.1
  have hother := hprod.choose_spec.choose_spec.2
  refine ⟨Y, H, hfamily, ?_⟩
  intro e τ σ Q F buffer href
  let A := n04bActualTypedAtlas hT hS hN hfield e₀
  let ψ := fun i => positiveReferenceCylinderChart (Y i)
  let χ := fun i => positiveReferenceCylinderInverse (Y i)
  let h₀ := fun i (p : PolarPoint) => H i p.1
  let V := n04WholeReferenceGaugeAtlasData C L A e cell ψ χ h₀ τ σ Q buffer.region
  dsimp only
  intro hA hR
  let U := enlargedMaterialData T
  have hpackage :=
    exists_wholeReferenceGauge_auxiliary_package hT hS hN A e cell ψ χ h₀ τ σ Q buffer hA hR
  let i : N04PositiveComponent Γ.reference.a Γ.reference.b (deriv Γ.reference.w) :=
    hpackage.choose
  let l : ℝ := hpackage.choose_spec.choose
  let u : ℝ := hpackage.choose_spec.choose_spec.choose
  let η : (S.height (3 / 4 : ℝ)).Space :=
    hpackage.choose_spec.choose_spec.choose_spec.choose
  have hprops := hpackage.choose_spec.choose_spec.choose_spec.choose_spec
  have hlu := hprops.1
  have hinterval := hprops.2.1
  have hU := hprops.2.2.1
  have hspaces := hprops.2.2.2
  have hS' := hspaces.1
  have hN' := hspaces.2.1
  have hA' := hspaces.2.2.1
  have hgeometry := hspaces.2.2.2
  have hR' := hgeometry.1
  have hgauge := hgeometry.2.1
  have hQ := hgeometry.2.2.1
  have hsupportData := hgeometry.2.2.2
  have hcompact := hsupportData.1
  have hsupport := hsupportData.2.1
  have hinside := hsupportData.2.2.1
  have hjetData := hsupportData.2.2.2
  have hauxRegular := hjetData.1
  have hauxBound := hjetData.2.1
  have hauxRef := hjetData.2.2.1
  have hdifferenceData := hjetData.2.2.2
  have hauxZero := hdifferenceData.1
  have hauxJ := hdifferenceData.2.1
  let S' := physicalSpacesReplaceAuxiliaryColumn S η
  let C' := geometryReplaceAuxiliaryColumn C η
  let R' := returnReplaceAuxiliaryColumn R η
  let L' := correctionReplaceAuxiliaryColumn L η
  let V' := canonicalReplaceAuxiliaryColumn V η
  have hsame (v : Atom) (hv : v ≠ .auxiliaryColumn) (z : AnnularState S × ℝ) (m : ℕ) :
      atom Γ.reference U S' C' L' V' z m v = atom Γ.reference U S C L V z m v :=
    canonicalAtom_replaceAuxiliaryColumn_of_ne Γ.reference U S C L V η z m v hv
  have hreference : ReferenceJets Γ.reference U S' C' L' V' := by
    refine ⟨?_, ?_⟩
    · have hotherAtZero := (hother e τ σ Q buffer.region href).2 0
      have hother0 := hotherAtZero.choose_spec.2
      intro m v
      by_cases hv : v = .auxiliaryColumn
      · subst v
        exact hauxRegular m
      · rw [hsame v hv (C.referenceState, 0) m]
        exact ⟨(hother0 m v hv).1, (hother0 m v hv).2.1⟩
    · intro s
      have hotherAtOrder := (hother e τ σ Q buffer.region href).2 s
      have hauxAtOrder := hauxBound s
      let B1 : ℝ := hotherAtOrder.choose
      let B2 : ℝ := hauxAtOrder.choose
      have hB1 : 0 < B1 := hotherAtOrder.choose_spec.1
      have hB2 : 0 < B2 := hauxAtOrder.choose_spec.1
      have hrest := hotherAtOrder.choose_spec.2
      have haux := hauxAtOrder.choose_spec.2
      let B : ℝ := max B1 B2
      have hB : 0 < B := hB1.trans_le (le_max_left _ _)
      refine ⟨B, hB, ?_⟩
      intro m v p hp a b hab
      have ht : 1 ≤ U.E0 (U.sample (V'.cell m)) :=
        one_le_enlargedMaterialData_E0 hT (materialSample_mem_interval hΓ.2.1 hT (V'.cell m))
      have hcost {d : ℝ} (hd : d ≤ B) :
          d * U.E0 (U.sample (V'.cell m)) ^ d ≤
            B * U.E0 (U.sample (V'.cell m)) ^ B :=
        mul_le_mul hd (Real.rpow_le_rpow_of_exponent_le ht hd)
          (Real.rpow_nonneg (zero_le_one.trans ht) _) hB.le
      by_cases hv : v = .auxiliaryColumn
      · subst v
        exact (haux m p hp a b hab).trans (hcost (le_max_right _ _))
      · rw [hsame v hv (C.referenceState, 0) m]
        exact ((hrest m v hv).2.2 p hp a b hab).trans (hcost (le_max_left _ _))
  exact ⟨i, l, u, η, hlu, hinterval, hU, hS', hN', hA', hR', hreference,
    hgauge, hQ, hcompact, hsupport, hinside, hauxRef, hauxZero, hauxJ, hsame⟩

end ContinuousFlexibility.Analysis
