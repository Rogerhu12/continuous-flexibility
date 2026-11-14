module

public import ContinuousFlexibility.Analysis.ActualPositiveReferenceInverseMaterialJets
public import ContinuousFlexibility.Analysis.ActualPositiveReferencePrescribedFamily
public import ContinuousFlexibility.Analysis.WholeReferenceGaugePositivePrincipalJets
public import ContinuousFlexibility.Analysis.WholeReferenceGaugeFixedPotentialReferenceJets

/-!
# One displayed positive family and its five coefficient atoms

The normalized material data and the original midpoint cells are fixed
before choosing one finite endpoint envelope. A single invocation of the
inverse-material producer, at degree three, supplies the exact Taylor
width, coordinate and height. Its finite certificate, full endpoint jet
matching and all-order forward/inverse bounds are retained. The four
principal atoms and the potential use that same family in the same atlas.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements ContinuousFlexibility.Radial
open CanonicalGeometry
open scoped ContDiff

/-- One choice of the degree-three material envelope supplies the actual
degree-four reference family and all five positive coefficient atoms. -/
theorem n04Coordinates_actual_positive_reference_fiveAtoms
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
          ((v = .principalA ∨ v = .principalAInverse ∨
            v = .principalB ∨ v = .principalC) ∨ v = .potential) →
          ContDiffOn ℝ ∞ (atom Γ.reference T S C L V (C.referenceState, 0) m v) unitStrip ∧
          (∀ p ∈ unitStrip, atom Γ.reference T S C L V (C.referenceState, 0) m v
            (p + (0, Real.pi)) = atom Γ.reference T S C L V (C.referenceState, 0) m v p) ∧
          ∀ p ∈ unitStrip, ∀ a b : ℕ, a + b ≤ s →
            |mixedDerivative a b (atom Γ.reference T S C L V (C.referenceState, 0) m v) p| ≤
              BM * T.E0 (T.sample (V.cell m)) ^ BM := by
  classical
  obtain ⟨C0, hC0, hfloor, hfamily⟩ :=
    n04Coordinates_retained_positive_reference_inverse_material_jets
      P hSelected hband hq hΓ hw hcoordinates hT hS hN hfield e₀ hK hhost hoptical
  obtain ⟨B, hB, hfinite, hall⟩ := hfamily 3
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
  have hfamily4 : N04PositiveReferenceFamily A src 4 Y H :=
    n04Coordinates_actual_positive_prescribed_reference_family
      hT hS hN hfield e₀ 3 C0 B cell hcell src hfinite
  have hjets : ∀ N : ℕ, ∃ M : ℝ, 1 ≤ M ∧ ∀ i,
      (∀ k, k ≤ N → ∀ x : ℝ,
        |iteratedDeriv (k + 1) (Y i) x| ≤ M * (C0 * T.E0 (T.sample (cell i))) ^ M ∧
        |iteratedDeriv k (H i) x| ≤ M * (C0 * T.E0 (T.sample (cell i))) ^ M ∧
        |iteratedDeriv k (fun t => (H i t)⁻¹) x| ≤
          M * (C0 * T.E0 (T.sample (cell i))) ^ M) ∧
      ∀ x : ℝ, |iteratedDeriv (N + 1) (Function.invFun (Y i)) x| ≤
        M * (C0 * T.E0 (T.sample (cell i))) ^ M := by
    intro N
    obtain ⟨M, hM, hactual⟩ := hall N
    exact ⟨M, hM, fun i => hactual i (cell i) (hcell i) (src i)⟩
  have hgeometry (i) := (hfamily4 i).1
  have hheight : ∀ N : ℕ, ∃ M : ℝ, 1 ≤ M ∧ ∀ i,
      (∀ k, k ≤ N → ∀ x : ℝ,
        |iteratedDeriv k (H i) x| ≤ M * (C0 * T.E0 (T.sample (cell i))) ^ M) ∧
      ∀ x : ℝ, |iteratedDeriv (N + 1) (Function.invFun (Y i)) x| ≤
        M * (C0 * T.E0 (T.sample (cell i))) ^ M := by
    intro N
    obtain ⟨M, hM, hactual⟩ := hjets N
    exact ⟨M, hM, fun i =>
      ⟨fun k hk x => ((hactual i).1 k hk x).2.1, (hactual i).2⟩⟩
  have hprincipal := n04WholeReferenceGauge_positive_principalReferenceJets_fixedFamily
    P hSelected hband hq hΓ hw hcoordinates hT hS hN hfield e₀
    hC0 hfloor hE0 cell hcell Y H hgeometry hjets
  have hpotential := n04WholeReferenceGauge_positive_potentialReferenceJets_fixedFamily
    hT hS hN hfield e₀ hC0 hfloor hE0 cell Y H hgeometry hheight
  refine ⟨hfamily4, hjets, ?_⟩
  intro s
  obtain ⟨BP, hBP, hprincipalS⟩ := hprincipal s
  obtain ⟨BV, hBV, hpotentialS⟩ := hpotential s
  let BM : ℝ := max BP BV
  have hBM : 0 < BM := hBP.trans_le (le_max_left BP BV)
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
    rcases hv with hv | rfl
    · exact ⟨BP, le_max_left BP BV, hprincipalS e τ σ Q N href m hm v hv⟩
    · exact ⟨BV, le_max_right BP BV, hpotentialS e τ σ Q N href m hm⟩
  obtain ⟨D, hDBM, hsmooth, hperiod, hbound⟩ := hselected
  refine ⟨hsmooth, hperiod, ?_⟩
  intro p hp a b hab
  have ht : 1 ≤ T.E0 (T.sample (V.cell m)) := hE0 (V.cell m)
  exact (hbound p hp a b hab).trans
    (mul_le_mul hDBM (Real.rpow_le_rpow_of_exponent_le ht hDBM)
      (Real.rpow_nonneg (zero_le_one.trans ht) _) hBM.le)

end ContinuousFlexibility.Analysis
