import ContinuousFlexibility.Analysis.ActualPositiveReferenceFiveAtoms
import ContinuousFlexibility.Analysis.WholeReferenceGaugePositiveGeometryJets

/-!
# One actual positive family and fifteen reference atoms

The existing five-atom producer is invoked once. Its original finite
certificate gives the physical width and its reciprocal at the same
midpoint sample. Its same all-order family then supplies the ten
geometric atoms. Only the numerical envelope is enlarged, after the
spatial order is fixed; the degree, width, coordinate and height remain
exactly the original ones.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements ContinuousFlexibility.Radial
open CanonicalGeometry
open scoped ContDiff

/-- A single degree-three family supplies its ten geometric and five
coefficient reference atoms, with one numerical bound at every order. -/
theorem n04Coordinates_actual_positive_reference_fifteenAtoms
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
    (e₀ : ℕ ≃ N04PieceIndex Γ.reference)
    (hE0 : ∀ j, 1 ≤ T.E0 (T.sample j)) (hK : 0 < K)
    (hhost : ∀ m, Ioo (C.left m) (C.right m) ⊆ Γ.reference.cells (C.cell m))
    (hoptical : ∀ m x, x ∈ Ioo (C.left m) (C.right m) →
      K⁻¹ * T.E0 (T.sample (C.cell m)) ^ (-K) *
        min (x - C.left m) (C.right m - x) ≤
          -deriv Γ.reference.w x / (x * Γ.reference.w x))
    (cell : N04PositiveComponent Γ.reference.a Γ.reference.b (deriv Γ.reference.w) → ℕ)
    (hcell : ∀ i, n04PositiveMidpoint i ∈ Γ.reference.cells (cell i))
    (src : ∀ i : N04PositiveComponent Γ.reference.a Γ.reference.b (deriv Γ.reference.w),
      ∀ side, N04PositiveEndpointSource C i side) :
    ∃ C0 : ℝ, 1 ≤ C0 ∧ (∀ j, 1 ≤ C0 * T.E0 (T.sample j)) ∧
      ∃ B : ℝ, 1 ≤ B ∧
      (∀ (i : N04PositiveComponent Γ.reference.a Γ.reference.b (deriv Γ.reference.w))
        (j : ℕ), n04PositiveMidpoint i ∈ Γ.reference.cells j →
        ∀ source : (side : Bool) → N04PositiveEndpointSource C i side,
          let A := n04bActualTypedAtlas hT hS hN hfield e₀
          let U := B * (C0 * T.E0 (T.sample j)) ^ B
          1 ≤ U ∧ (n04PositiveRight i - n04PositiveLeft i)⁻¹ ≤ U ∧
            n04PositiveRight i - n04PositiveLeft i ≤ U ∧
            ∀ side : Bool,
              U⁻¹ ≤ radialBoundaryJet (n04PositiveReferenceSourceCoordinate (source side) A)
                (n04PositiveEndpoint i side) 1 0 ∧
              U⁻¹ ≤ radialBoundaryJet (n04PositiveReferenceSourceHeight (source side) A)
                (n04PositiveEndpoint i side) 0 0 ∧
              (∀ k : ℕ, 1 ≤ k → k ≤ 4 →
                |radialBoundaryJet (n04PositiveReferenceSourceCoordinate (source side) A)
                  (n04PositiveEndpoint i side) k 0| ≤ U) ∧
              ∀ k : ℕ, k ≤ 4 →
                |radialBoundaryJet (n04PositiveReferenceSourceHeight (source side) A)
                  (n04PositiveEndpoint i side) k 0| ≤ U) ∧
      let A := n04bActualTypedAtlas hT hS hN hfield e₀
      let U := fun i => B * (C0 * T.E0 (T.sample (cell i))) ^ B
      let δ := fun i => positiveReferenceTaylorWidth 3
        (n04PositiveLeft i) (n04PositiveRight i) (U i)⁻¹ (U i)
      let ys := fun i side => radialEndpointTaylorSlice 4
        (n04PositiveEndpoint i side) (n04PositiveReferenceSourceCoordinate (src i side) A)
      let hs := fun i side => radialEndpointTaylorSlice 4
        (n04PositiveEndpoint i side) (n04PositiveReferenceSourceHeight (src i side) A)
      let Y := fun i => positiveReferenceCoordinate (n04PositiveLeft i) (n04PositiveRight i)
        (δ i) (deriv (ys i false)) (deriv (ys i true))
      let H := fun i => positiveReferenceHeight (n04PositiveLeft i) (n04PositiveRight i)
        (δ i) (hs i false) (hs i true)
      N04PositiveReferenceFamily A src 4 Y H ∧
      (∀ N : ℕ, ∃ M : ℝ, 1 ≤ M ∧ ∀ i,
        (∀ k, k ≤ N → ∀ x : ℝ,
          |iteratedDeriv (k + 1) (Y i) x| ≤ M * (C0 * T.E0 (T.sample (cell i))) ^ M ∧
          |iteratedDeriv k (H i) x| ≤ M * (C0 * T.E0 (T.sample (cell i))) ^ M ∧
          |iteratedDeriv k (fun t => (H i t)⁻¹) x| ≤
            M * (C0 * T.E0 (T.sample (cell i))) ^ M) ∧
        ∀ x : ℝ, |iteratedDeriv (N + 1) (Function.invFun (Y i)) x| ≤
          M * (C0 * T.E0 (T.sample (cell i))) ^ M) ∧
      ∀ s : ℕ, ∃ BM : ℝ, 0 < BM ∧
        ∀ (e : ℕ ≃ N04WholePieceIndex Γ.reference)
          (τ σ : (AnnularState S × ℝ) →
            N04PositiveComponent Γ.reference.a Γ.reference.b (deriv Γ.reference.w) →
              PolarPoint → PolarPoint)
          (Q : (AnnularState S × ℝ) →
            N04PositiveComponent Γ.reference.a Γ.reference.b (deriv Γ.reference.w) →
              PolarPoint → ℝ) (N : Set ℝ),
          (∀ i, τ (C.referenceState, 0) i = id ∧
            σ (C.referenceState, 0) i = id ∧ Q (C.referenceState, 0) i = (fun _ => 1)) →
        let V := n04WholeReferenceGaugeAtlasData C L A e cell
          (fun i => positiveReferenceCylinderChart (Y i))
          (fun i => positiveReferenceCylinderInverse (Y i))
          (fun i p => H i p.1) τ σ Q N
        ∀ m, V.positive m = true → ∀ v : Atom,
          ((v = .chartRadial ∨ v = .chartAngleDefect ∨ v = .inverseRadial ∨
            v = .inverseAngleDefect ∨ v = .height ∨ v = .heightInverse ∨
            v = .jacobian ∨ v = .jacobianInverse ∨
            v = .sourceFactor ∨ v = .sourceFactorInverse) ∨
            (v = .principalA ∨ v = .principalAInverse ∨
              v = .principalB ∨ v = .principalC) ∨ v = .potential) →
          ContDiffOn ℝ ∞ (atom Γ.reference T S C L V (C.referenceState, 0) m v) unitStrip ∧
          (∀ p ∈ unitStrip, atom Γ.reference T S C L V (C.referenceState, 0) m v
            (p + (0, Real.pi)) = atom Γ.reference T S C L V (C.referenceState, 0) m v p) ∧
          ∀ p ∈ unitStrip, ∀ a b : ℕ, a + b ≤ s →
            |mixedDerivative a b (atom Γ.reference T S C L V (C.referenceState, 0) m v) p| ≤
              BM * T.E0 (T.sample (V.cell m)) ^ BM := by
  classical
  obtain ⟨C0, hC0, hfloor, B, hB, hfinite, hfields⟩ :=
    n04Coordinates_actual_positive_reference_fiveAtoms
      P hSelected hband hq hΓ hw hcoordinates hT hS hN hfield e₀
      hE0 hK hhost hoptical cell hcell src
  refine ⟨C0, hC0, hfloor, B, hB, hfinite, ?_⟩
  let A := n04bActualTypedAtlas hT hS hN hfield e₀
  let U := fun i => B * (C0 * T.E0 (T.sample (cell i))) ^ B
  let δ := fun i => positiveReferenceTaylorWidth 3
    (n04PositiveLeft i) (n04PositiveRight i) (U i)⁻¹ (U i)
  let ys := fun i side => radialEndpointTaylorSlice 4
    (n04PositiveEndpoint i side) (n04PositiveReferenceSourceCoordinate (src i side) A)
  let hs := fun i side => radialEndpointTaylorSlice 4
    (n04PositiveEndpoint i side) (n04PositiveReferenceSourceHeight (src i side) A)
  let Y := fun i => positiveReferenceCoordinate (n04PositiveLeft i) (n04PositiveRight i)
    (δ i) (deriv (ys i false)) (deriv (ys i true))
  let H := fun i => positiveReferenceHeight (n04PositiveLeft i) (n04PositiveRight i)
    (δ i) (hs i false) (hs i true)
  obtain ⟨hfamily4, hjets, hfive⟩ := hfields
  have hgeometry (i) : PositiveChartRangeGeometry (positiveReferenceCylinderChart (Y i))
      (positiveReferenceCylinderInverse (Y i)) (fun p : PolarPoint => H i p.1)
      (n04PositiveLeft i) (n04PositiveRight i) 0 1 := (hfamily4 i).1
  have hwidth (i) :
      n04PositiveRight i - n04PositiveLeft i ≤ U i ∧
      (n04PositiveRight i - n04PositiveLeft i)⁻¹ ≤ U i := by
    have hi := hfinite i (cell i) (hcell i) (src i)
    exact ⟨hi.2.2.1, hi.2.1⟩
  have hgeometric := n04WholeReferenceGauge_positive_geometryReferenceJets_fixedFamily
    C L hC0 hfloor hE0 cell hB hwidth Y H hgeometry hjets
  refine ⟨hfamily4, hjets, ?_⟩
  intro s
  obtain ⟨BG, hBG, hgeometricS⟩ := hgeometric s
  obtain ⟨BF, hBF, hfiveS⟩ := hfive s
  let BM : ℝ := max BG BF
  have hBM : 0 < BM := hBG.trans_le (le_max_left BG BF)
  refine ⟨BM, hBM, ?_⟩
  intro e τ σ Q N href
  let V := n04WholeReferenceGaugeAtlasData C L A e cell
    (fun i => positiveReferenceCylinderChart (Y i))
    (fun i => positiveReferenceCylinderInverse (Y i))
    (fun i p => H i p.1) τ σ Q N
  dsimp only
  intro m hm v hv
  have hselected : ∃ D : ℝ, D ≤ BM ∧
      ContDiffOn ℝ ∞ (atom Γ.reference T S C L V (C.referenceState, 0) m v) unitStrip ∧
      (∀ p ∈ unitStrip, atom Γ.reference T S C L V (C.referenceState, 0) m v
        (p + (0, Real.pi)) = atom Γ.reference T S C L V (C.referenceState, 0) m v p) ∧
      ∀ p ∈ unitStrip, ∀ a b : ℕ, a + b ≤ s →
        |mixedDerivative a b (atom Γ.reference T S C L V (C.referenceState, 0) m v) p| ≤
          D * T.E0 (T.sample (V.cell m)) ^ D := by
    rcases hv with hv | hv
    · exact ⟨BG, le_max_left BG BF, hgeometricS A e τ σ Q N href m hm v hv⟩
    · exact ⟨BF, le_max_right BG BF, hfiveS e τ σ Q N href m hm v hv⟩
  obtain ⟨D, hDBM, hsmooth, hperiod, hbound⟩ := hselected
  refine ⟨hsmooth, hperiod, ?_⟩
  intro p hp a b hab
  have ht : 1 ≤ T.E0 (T.sample (V.cell m)) := hE0 (V.cell m)
  exact (hbound p hp a b hab).trans
    (mul_le_mul hDBM (Real.rpow_le_rpow_of_exponent_le ht hDBM)
      (Real.rpow_nonneg (zero_le_one.trans ht) _) hBM.le)

end ContinuousFlexibility.Analysis
