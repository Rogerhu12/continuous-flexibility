module

public import ContinuousFlexibility.Analysis.ActualPositiveReferencePrincipalMaterialCost
public import ContinuousFlexibility.Analysis.WholeReferenceGaugePrincipalLower

/-!
# Reference principal certificate for the displayed material family

The material envelope is normalized before the finite endpoint family is
chosen. Its original C0 and B determine the same Taylor width, coordinate
and height throughout this proof. The actual retained physical profile
and those fields supply the physical costs of the whole atlas. The
geometric certificate is for that very record, on its chosen smaller
state neighborhood; the original typed atlas is retained.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements ContinuousFlexibility.Radial
open scoped ContDiff

/-- The physical costs of the displayed reference family imply the full
reference principal predicate for the same actual whole-gauge atlas. -/
theorem n04WholeReferenceGauge_actual_prescribed_referencePrincipal
    {S₀ : SelectedTailData} {K₀ : SeedCentralCutoff} {q length : ℝ}
    (P : SeedRetainedPair S₀ K₀ q length) (hSelected : IsSelectedTail S₀)
    (hband : radialFrequencyBand S₀.chain S₀.Cstar S₀.chain.index 2) (hq : 0 < q)
    {Γ : ConnectedReferenceGeometry} (hΓ : Γ.Realizes)
    (hw : Γ.reference.w = P.pair.profile)
    (hcoordinates : R11aRetainedCoordinates P Γ)
    {T : MaterialData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {R : ReturnEquationData S} {L : ReturnCorrectionData S}
    {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData Γ.reference T) (hS : IsPhysicalSpaces Γ.reference T S)
    (hN : NonlinearPropertiesThrough03 Γ.reference T S C R L base loss ε)
    (hfield : N04bFieldRegularity Γ.reference S C L base ε)
    (e₀ : ℕ ≃ N04PieceIndex Γ.reference) (n : ℕ)
    {C0 B : ℝ} (hC0 : 1 ≤ C0) (hB : 1 ≤ B)
    (hE0 : ∀ j, 1 ≤ T.E0 (T.sample j))
    (hfinite : ∀ (i : N04PositiveComponent Γ.reference.a Γ.reference.b (deriv Γ.reference.w))
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
                  (n04PositiveEndpoint i side) k 0| ≤ U)
    (e : ℕ ≃ N04WholePieceIndex Γ.reference)
    (cell : N04PositiveComponent Γ.reference.a Γ.reference.b (deriv Γ.reference.w) → ℕ)
    (hcell : ∀ i, n04PositiveMidpoint i ∈ Γ.reference.cells (cell i))
    (src : (i : N04PositiveComponent Γ.reference.a Γ.reference.b (deriv Γ.reference.w)) →
      (side : Bool) → N04PositiveEndpointSource C i side)
    (τ σ : (AnnularState S × ℝ) →
      N04PositiveComponent Γ.reference.a Γ.reference.b (deriv Γ.reference.w) →
        PolarPoint → PolarPoint)
    (Q : (AnnularState S × ℝ) →
      N04PositiveComponent Γ.reference.a Γ.reference.b (deriv Γ.reference.w) →
        PolarPoint → ℝ) (N : Set ℝ)
    (href : ∀ i, τ (C.referenceState, 0) i = id ∧
      σ (C.referenceState, 0) i = id ∧ Q (C.referenceState, 0) i = (fun _ => 1)) :
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
    ∀ {newBase : ℕ} {ε' : ℝ}, 0 < ε' →
      CanonicalGeometry Γ.reference S C V newBase ε' →
        CanonicalGeometry.ReferencePrincipal T S C V := by
  classical
  obtain ⟨K, hK, hcosts⟩ :=
    n04Coordinates_retained_positive_reference_principal_material_cost
      P hSelected hband hq hΓ hw hcoordinates hT hS hN hfield e₀ n
      hC0 hB hE0 hfinite
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
  have hactual (i : N04PositiveComponent Γ.reference.a Γ.reference.b
      (deriv Γ.reference.w)) :
      PositiveChartRangeGeometry (positiveReferenceCylinderChart (Y i))
        (positiveReferenceCylinderInverse (Y i)) (fun p : PolarPoint => H i p.1)
        (n04PositiveLeft i) (n04PositiveRight i) 0 1 ∧
      ∃ h k M : ℝ, 0 < h ∧ 0 < k ∧ 0 < M ∧
        (∀ x ∈ Ioo (n04PositiveLeft i) (n04PositiveRight i),
          h ≤ H i x ∧ deriv (Y i) x ≤ M ∧
            k * min (x - n04PositiveLeft i) (n04PositiveRight i - x) ≤
              deriv Γ.reference.w x / x) ∧
        M ^ 2 ≤ (K * T.E0 (T.sample (cell i)) ^ K) * (h ^ 2 * k) :=
    hcosts i (cell i) (hcell i) (src i)
  have hgeometry (i : N04PositiveComponent Γ.reference.a Γ.reference.b
      (deriv Γ.reference.w)) := (hactual i).1
  choose h k M hh hk hM hb hcost using fun i => (hactual i).2
  change ∀ {newBase : ℕ} {ε' : ℝ}, 0 < ε' →
    CanonicalGeometry Γ.reference S C V newBase ε' →
      CanonicalGeometry.ReferencePrincipal T S C V
  intro newBase ε' hε' hA
  exact n04WholeReferenceGaugeAtlasData_referencePrincipal_of_physical_costs
    hT hS hN hfield e₀ e cell Y H τ σ Q N hε' href hgeometry hA
    h k M (fun i => ⟨hh i, hk i, hM i, hb i⟩) hK hcost

end ContinuousFlexibility.Analysis
