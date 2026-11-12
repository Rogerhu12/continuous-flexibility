import ContinuousFlexibility.Analysis.WholePositiveReferencePotentialJets
import ContinuousFlexibility.Analysis.MaterialEnvelopeNormalization
import ContinuousFlexibility.Analysis.MaterialSampleBounds

/-!
# The actual positive reference potential atom

One low endpoint envelope is retained before all spatial orders. The
reference chart and height use its displayed width, and the whole atlas
uses exactly those fields. Positive canonical endpoints are zero and one,
so the actual unit-coordinate atom is the stored reference potential.
Only the explicitly enlarged material envelope is assumed to be at least
one when the finite family of derivative bounds is packaged.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements ContinuousFlexibility.Radial
open CanonicalGeometry
open scoped ContDiff BigOperators

/-- The finite endpoint certificate and every positive potential atom
bound use the same displayed reference interpolation. All material
constants precede the component enumeration, cells and transport family. -/
theorem n04WholeReferenceGauge_positive_potentialReferenceJets_enlargedMaterialData
    {S₀ : SelectedTailData} {K₀ : SeedCentralCutoff} {q length : ℝ}
    (P : SeedRetainedPair S₀ K₀ q length) (hSelected : IsSelectedTail S₀)
    (hband : radialFrequencyBand S₀.chain S₀.Cstar S₀.chain.index 2) (hq : 0 < q)
    {Γ : ConnectedReferenceGeometry} (hΓ : Γ.Realizes)
    (hw : Γ.reference.w = P.pair.profile)
    (hcoordinates : R11aRetainedCoordinates P Γ)
    {T : MaterialData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {R : ReturnEquationData S} {L : ReturnCorrectionData S}
    {base loss : ℕ} {ε K : ℝ}
    (hT : IsMaterialData Γ.reference T) (hS : IsPhysicalSpaces Γ.reference T S)
    (hN : NonlinearPropertiesThrough03 Γ.reference T S C R L base loss ε)
    (hfield : N04bFieldRegularity Γ.reference S C L base ε)
    (e₀ : ℕ ≃ N04PieceIndex Γ.reference) (hK : 0 < K)
    (hhost : ∀ m, Ioo (C.left m) (C.right m) ⊆ Γ.reference.cells (C.cell m))
    (hoptical : ∀ m x, x ∈ Ioo (C.left m) (C.right m) →
      K⁻¹ * T.E0 (T.sample (C.cell m)) ^ (-K) *
        min (x - C.left m) (C.right m - x) ≤
          -deriv Γ.reference.w x / (x * Γ.reference.w x)) :
    ∃ C0 : ℝ, 1 ≤ C0 ∧ (∀ j, 1 ≤ C0 * T.E0 (T.sample j)) ∧
      ∀ n : ℕ, ∃ B : ℝ, 1 ≤ B ∧
      (∀ (i : N04PositiveComponent Γ.reference.a Γ.reference.b (deriv Γ.reference.w))
        (j : ℕ), n04PositiveMidpoint i ∈ Γ.reference.cells j →
        ∀ src : (side : Bool) → N04PositiveEndpointSource C i side,
          let A := n04bActualTypedAtlas hT hS hN hfield e₀
          let U := B * (C0 * T.E0 (T.sample j)) ^ B
          1 ≤ U ∧ (n04PositiveRight i - n04PositiveLeft i)⁻¹ ≤ U ∧
            n04PositiveRight i - n04PositiveLeft i ≤ U ∧
            ∀ side : Bool,
              U⁻¹ ≤ radialBoundaryJet (n04PositiveReferenceSourceCoordinate (src side) A)
                (n04PositiveEndpoint i side) 1 0 ∧
              U⁻¹ ≤ radialBoundaryJet (n04PositiveReferenceSourceHeight (src side) A)
                (n04PositiveEndpoint i side) 0 0 ∧
              (∀ k : ℕ, 1 ≤ k → k ≤ n + 1 →
                |radialBoundaryJet (n04PositiveReferenceSourceCoordinate (src side) A)
                  (n04PositiveEndpoint i side) k 0| ≤ U) ∧
              ∀ k : ℕ, k ≤ n + 1 →
                |radialBoundaryJet (n04PositiveReferenceSourceHeight (src side) A)
                  (n04PositiveEndpoint i side) k 0| ≤ U) ∧
      ∀ s : ℕ, ∃ BM : ℝ, 0 < BM ∧
      ∀ (e : ℕ ≃ N04WholePieceIndex Γ.reference)
        (cell : N04PositiveComponent Γ.reference.a Γ.reference.b (deriv Γ.reference.w) → ℕ),
        (∀ i, n04PositiveMidpoint i ∈ Γ.reference.cells (cell i)) →
      ∀ (src : (i : N04PositiveComponent Γ.reference.a Γ.reference.b (deriv Γ.reference.w)) →
          (side : Bool) → N04PositiveEndpointSource C i side)
        (τ σ : (AnnularState S × ℝ) →
          N04PositiveComponent Γ.reference.a Γ.reference.b (deriv Γ.reference.w) →
            PolarPoint → PolarPoint)
        (Q : (AnnularState S × ℝ) →
          N04PositiveComponent Γ.reference.a Γ.reference.b (deriv Γ.reference.w) →
            PolarPoint → ℝ) (N : Set ℝ),
        (∀ i, τ (C.referenceState, 0) i = id ∧
          σ (C.referenceState, 0) i = id ∧ Q (C.referenceState, 0) i = (fun _ => 1)) →
        let A := n04bActualTypedAtlas hT hS hN hfield e₀
        let U := fun i => B * (C0 * T.E0 (T.sample (cell i))) ^ B
        let δ := fun i => positiveReferenceTaylorWidth n
          (n04PositiveLeft i) (n04PositiveRight i) (U i)⁻¹ (U i)
        let ys := fun i (side : Bool) => radialEndpointTaylorSlice (n + 1)
          (n04PositiveEndpoint i side) (n04PositiveReferenceSourceCoordinate (src i side) A)
        let hs := fun i (side : Bool) => radialEndpointTaylorSlice (n + 1)
          (n04PositiveEndpoint i side) (n04PositiveReferenceSourceHeight (src i side) A)
        let Y := fun i => positiveReferenceCoordinate (n04PositiveLeft i) (n04PositiveRight i)
          (δ i) (deriv (ys i false)) (deriv (ys i true))
        let H := fun i => positiveReferenceHeight (n04PositiveLeft i) (n04PositiveRight i)
          (δ i) (hs i false) (hs i true)
        let V := n04WholeReferenceGaugeAtlasData C L A e cell
          (fun i => positiveReferenceCylinderChart (Y i))
          (fun i => positiveReferenceCylinderInverse (Y i))
          (fun i p => H i p.1) τ σ Q N
        let T' := enlargedMaterialData T
        ∀ m, V.positive m = true → ∀ p ∈ unitStrip, ∀ a b : ℕ, a + b ≤ s →
          |mixedDerivative a b
            (atom Γ.reference T' S C L V (C.referenceState, 0) m .potential) p| ≤
              BM * T'.E0 (T'.sample (V.cell m)) ^ BM := by
  classical
  obtain ⟨C0, hC0, hfloor, hfamily⟩ :=
    n04Coordinates_retained_positive_reference_potential_material_jets
      P hSelected hband hq hΓ hw hcoordinates hT hS hN hfield e₀ hK hhost hoptical
  refine ⟨C0, hC0, hfloor, ?_⟩
  intro n
  obtain ⟨B, hB, hfinite, hpotential⟩ := hfamily n
  refine ⟨B, hB, hfinite, ?_⟩
  choose M hM hactual using hpotential
  intro s
  let D : ℝ := 1 + ∑ k : Fin (s + 1), M k.val
  have hD : 1 ≤ D := le_add_of_nonneg_right
    (Finset.sum_nonneg (fun k _ => zero_le_one.trans (hM k.val)))
  have hMD (a : ℕ) (ha : a ≤ s) : M a ≤ D :=
    (Finset.single_le_sum (f := fun k : Fin (s + 1) => M k.val)
      (fun k _ => zero_le_one.trans (hM k.val))
      (Finset.mem_univ (⟨a, by omega⟩ : Fin (s + 1)))).trans
        (le_add_of_nonneg_left zero_le_one)
  obtain ⟨BM, hBM, hpack⟩ := coefficientEnvelope_pack (D * C0 ^ D) D
  refine ⟨BM, hBM, ?_⟩
  intro e cell hcell src τ σ Q N href
  let A := n04bActualTypedAtlas hT hS hN hfield e₀
  let U := fun i => B * (C0 * T.E0 (T.sample (cell i))) ^ B
  let δ := fun i => positiveReferenceTaylorWidth n
    (n04PositiveLeft i) (n04PositiveRight i) (U i)⁻¹ (U i)
  let ys := fun i (side : Bool) => radialEndpointTaylorSlice (n + 1)
    (n04PositiveEndpoint i side) (n04PositiveReferenceSourceCoordinate (src i side) A)
  let hs := fun i (side : Bool) => radialEndpointTaylorSlice (n + 1)
    (n04PositiveEndpoint i side) (n04PositiveReferenceSourceHeight (src i side) A)
  let Y := fun i => positiveReferenceCoordinate (n04PositiveLeft i) (n04PositiveRight i)
    (δ i) (deriv (ys i false)) (deriv (ys i true))
  let H := fun i => positiveReferenceHeight (n04PositiveLeft i) (n04PositiveRight i)
    (δ i) (hs i false) (hs i true)
  let ψ := fun i => positiveReferenceCylinderChart (Y i)
  let χ := fun i => positiveReferenceCylinderInverse (Y i)
  let h₀ := fun i (p : PolarPoint) => H i p.1
  let V := n04WholeReferenceGaugeAtlasData C L A e cell ψ χ h₀ τ σ Q N
  let T' := enlargedMaterialData T
  change ∀ m, V.positive m = true → ∀ p ∈ unitStrip, ∀ a b : ℕ, a + b ≤ s →
    |mixedDerivative a b
      (atom Γ.reference T' S C L V (C.referenceState, 0) m .potential) p| ≤
        BM * T'.E0 (T'.sample (V.cell m)) ^ BM
  intro m hm p hp a b hab
  cases hi : e m with
  | inl j =>
      have hnegative : V.positive m = false := by
        simp only [V, n04WholeReferenceGaugeAtlasData, n04WholeCanonicalAtlasData,
          n04bWithInteriorDivision, n04WholePiecePositive, hi]
      exact False.elim (Bool.false_ne_true (hnegative.symm.trans hm))
  | inr i =>
      obtain ⟨hl, hr, _, _, _, hsample, _, _, _, _, _, _⟩ :=
        n04WholeReferenceGaugeAtlasData_positive_fields
          C L A e cell ψ χ h₀ τ σ Q N (C.referenceState, 0) m i hi
      have hunit : canonicalUnitPoint V m = id := by
        funext p
        change (V.left m + (V.right m - V.left m) * p.1, p.2) = p
        simp only [hl, hr, sub_zero, one_mul, zero_add, Prod.mk.eta]
      have hatom : atom Γ.reference T' S C L V (C.referenceState, 0) m .potential =
          V.potential (C.referenceState, 0) m := by
        funext p
        change V.potential (C.referenceState, 0) m (canonicalUnitPoint V m p) =
          V.potential (C.referenceState, 0) m p
        exact congrArg (V.potential (C.referenceState, 0) m) (congrFun hunit p)
      have hpCanonical : p ∈ canonicalOpen S V m := by
        simpa only [unitStrip, canonicalOpen, hl, hr] using hp
      have hjet := hactual a i (cell i) (hcell i) (src i)
      have hgeometry : PositiveChartRangeGeometry (positiveReferenceCylinderChart (Y i))
          (positiveReferenceCylinderInverse (Y i)) (fun p : PolarPoint => H i p.1)
          (n04PositiveLeft i) (n04PositiveRight i) 0 1 := hjet.1
      have hmixed : mixedDerivative a b (V.potential (C.referenceState, 0) m) p =
          if b = 0 then iteratedDeriv a
            (fun x => -(H i (Function.invFun (Y i) x) *
              deriv ((fun r => Γ.reference.w r * deriv (H i) r) ∘
                Function.invFun (Y i)) x)) p.1 else 0 :=
        n04WholeReferenceGaugeAtlasData_positive_reference_potential_mixed
          hT hS hN hfield e₀ e cell Y H τ σ Q N m i hi hgeometry (href i)
          hpCanonical a b
      rw [hatom, hmixed]
      let W : ℝ := C0 * T.E0 (T.sample (cell i))
      let t : ℝ := T'.E0 (T'.sample (cell i))
      have hW : 1 ≤ W := hfloor (cell i)
      have hsCore := materialSample_mem_interval hN.1.1.1.1 hT (cell i)
      have ht : 1 ≤ t := one_le_enlargedMaterialData_E0 hT hsCore
      have hWt : W ≤ C0 * t := mul_le_mul_of_nonneg_left
        (le_enlargedMaterialData_E0 T (T.sample (cell i))) (zero_le_one.trans hC0)
      have hcost : M a * W ^ M a ≤ BM * t ^ BM := by
        calc
          _ ≤ D * W ^ D := mul_le_mul (hMD a (by omega))
            (Real.rpow_le_rpow_of_exponent_le hW (hMD a (by omega)))
            (Real.rpow_nonneg (zero_le_one.trans hW) _) (zero_le_one.trans hD)
          _ ≤ D * (C0 * t) ^ D := mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (zero_le_one.trans hW) hWt (zero_le_one.trans hD))
            (zero_le_one.trans hD)
          _ = (D * C0 ^ D) * t ^ D := by
            rw [Real.mul_rpow (zero_le_one.trans hC0) (zero_le_one.trans ht)]
            ring
          _ ≤ BM * t ^ BM := hpack t ht
      have hrhs : 0 ≤ BM * t ^ BM :=
        mul_nonneg hBM.le (Real.rpow_nonneg (zero_le_one.trans ht) _)
      rw [hsample]
      by_cases hb : b = 0
      · rw [if_pos hb]
        exact (hjet.2 p.1 hp.1).trans hcost
      · rw [if_neg hb, abs_zero]
        exact hrhs

end ContinuousFlexibility.Analysis
