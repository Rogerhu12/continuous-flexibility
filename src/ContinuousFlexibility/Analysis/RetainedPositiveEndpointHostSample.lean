module

public import ContinuousFlexibility.Analysis.RetainedPositiveEndpointMidpointX
public import ContinuousFlexibility.Analysis.MaterialClosedHostEndpointX
public import ContinuousFlexibility.Analysis.MaterialSampleBounds

/-!
# Original negative host samples at the true positive midpoint

The actual shared root lies in the closed original negative component.
Its host-index estimate extends to that root by continuity. The proved
whole-family endpoint-to-midpoint bound then compares the original
host sample with any cell containing the actual positive midpoint.
The central exceptions and both tails use this same argument.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set
open ContinuousFlexibility.Statements ContinuousFlexibility.Analysis

theorem retainedReference_positive_endpoint_host_sample_bound
    {S : SelectedTailData} {K : SeedCentralCutoff} {q length : ℝ}
    (P : SeedRetainedPair S K q length) (hS : IsSelectedTail S)
    (hband : radialFrequencyBand S.chain S.Cstar S.chain.index 2) (hq : 0 < q)
    {Γ : ConnectedReferenceGeometry} (hΓ : Γ.Realizes)
    (hw : Γ.reference.w = P.pair.profile)
    (hcoordinates : R11aRetainedCoordinates P Γ)
    {E : PhysicalSpacesData} {C : NonlinearGeometryData E}
    (hC : controlGeometryConditions Γ.reference E C)
    {T : MaterialData} (hT : IsMaterialData Γ.reference T)
    {R : ℝ} (hR : 0 ≤ R) :
    ∃ K₁ A : ℝ, 0 < K₁ ∧ 0 ≤ A ∧
      ∀ (i : N04PositiveComponent Γ.reference.a Γ.reference.b (deriv Γ.reference.w))
        (side : Bool) (m j k : ℕ),
        Ioo (C.left m) (C.right m) ⊆ Γ.reference.cells j →
        n04PositiveEndpoint i side = (if side then C.left m else C.right m) →
        n04PositiveMidpoint i ∈ Γ.reference.cells k →
        T.E0 (T.sample j) ^ R ≤ K₁ * T.E0 (T.sample k) ^ A := by
  obtain ⟨L, hL, hgap⟩ := retainedReference_positive_endpoint_midpointX_bound
    P hS hband hq hΓ hw hcoordinates hC hT
  obtain ⟨B, hB, hcell, hclosed⟩ := material_cell_endpointX_closed_interval hT
  obtain ⟨CH, AH, K₁, A, _, _, hK₁, hA, hmaterial⟩ :=
    material_oneSided_endpoint_comparison hT hΓ.2.1 hR
      (show 0 ≤ L + 4 * B by positivity)
  have hdata := hT
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hsample, _, _⟩ := hdata
  refine ⟨K₁, A, hK₁, hA, ?_⟩
  intro i side m j k hhost hend hmid
  have hcomponent := hC.1 m
  have hc : n04PositiveEndpoint i side ∈ Icc (C.left m) (C.right m) := by
    rw [hend]
    cases side
    · exact ⟨hcomponent.2.1.le, le_rfl⟩
    · exact ⟨le_rfl, hcomponent.2.1.le⟩
  have hsJ := abs_le.mp (hcell j (T.sample j) (hsample j))
  have hcJ := abs_le.mp (hclosed (C.left m) (C.right m) j
    hcomponent.1 hcomponent.2.1 hcomponent.2.2 hhost (n04PositiveEndpoint i side) hc)
  have hcm := (abs_le.mp (hgap i side)).2
  have hmK := abs_le.mp (hcell k (n04PositiveMidpoint i) hmid)
  have hsK := abs_le.mp (hcell k (T.sample k) (hsample k))
  have hshift : endpointX 1 (Statements.endpointDistance Γ.reference (T.sample j)) ≤
      endpointX 1 (Statements.endpointDistance Γ.reference (T.sample k)) + (L + 4 * B) := by
    linarith only [hsJ.2, hcJ.1, hcm, hmK.2, hsK.1]
  exact (hmaterial (T.sample k) (T.sample j)
    (materialSample_mem_interval hΓ.2.1 hT k)
    (materialSample_mem_interval hΓ.2.1 hT j) hshift).2

end ContinuousFlexibility.Radial
