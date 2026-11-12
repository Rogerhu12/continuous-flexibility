import ContinuousFlexibility.Analysis.WholeReferenceGaugeRootFirstJets
import ContinuousFlexibility.Analysis.WholeReferenceGaugeRootInterfaces

/-!
# Root transmission for the same actual reference-gauged whole atlas

The actual partition identifies the two possible ordered root interfaces.
One fixed canonical endpoint and orientation is then used on each side
for the reference and every admissible current state. The raw first jets
come from the actual reference interpolation and the already selected
relative family. The original negative atlas is never reconstructed on
the smaller neighborhood.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

theorem n04WholeReferenceGaugeAtlasData_actual_rootFirstJetMatching
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss newBase n : ℕ} {ε ε' : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    (e₀ : ℕ ≃ N04PieceIndex D) (e : ℕ ≃ N04WholePieceIndex D)
    (cell : N04PositiveComponent D.a D.b (deriv D.w) → ℕ)
    (Y H : N04PositiveComponent D.a D.b (deriv D.w) → ℝ → ℝ)
    (τ σ : (AnnularState S × ℝ) →
      N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → PolarPoint)
    (Q : (AnnularState S × ℝ) →
      N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → ℝ)
    (N : Set ℝ)
    (j : ∀ i : N04PositiveComponent D.a D.b (deriv D.w),
      ∀ side, N04PositiveEndpointSource C i side)
    (hgeometry : ∀ i, PositiveChartRangeGeometry (positiveReferenceCylinderChart (Y i))
      (positiveReferenceCylinderInverse (Y i)) (fun p : PolarPoint => H i p.1)
      (n04PositiveLeft i) (n04PositiveRight i) 0 1)
    (hYjets : ∀ i side θ a, a ≤ 1 →
      iteratedFDeriv ℝ a (fun p : PolarPoint => Y i p.1)
          (n04PositiveEndpoint i side, θ) =
        iteratedFDeriv ℝ a (n04PositiveReferenceSourceCoordinate (j i side)
          (n04bActualTypedAtlas hT hS hN hfield e₀)) (n04PositiveEndpoint i side, θ))
    (hHjets : ∀ i side θ a, a ≤ 1 →
      iteratedFDeriv ℝ a (fun p : PolarPoint => H i p.1)
          (n04PositiveEndpoint i side, θ) =
        iteratedFDeriv ℝ a (n04PositiveReferenceSourceHeight (j i side)
          (n04bActualTypedAtlas hT hS hN hfield e₀)) (n04PositiveEndpoint i side, θ))
    (hb : base ≤ newBase) (hε' : 0 < ε') (hε'ε : ε' ≤ ε) (hn : 1 ≤ n)
    (c d J Hbound : N04PositiveComponent D.a D.b (deriv D.w) → ℝ)
    (hmatching : ∀ z ∈ stateNeighborhood S C newBase ε', stateSector S z.1 → ∀ i,
      WholePositiveTransportMatching n
        (fun side => n04PositiveSourceMap (j i side)
          (n04bActualTypedAtlas hT hS hN hfield e₀) z)
        (fun side => n04PositiveSourceHeight (j i side)
          (n04bActualTypedAtlas hT hS hN hfield e₀) z)
        (τ z i) (σ z i) (Q z i) (n04PositiveLeft i) (n04PositiveRight i)
        (c i) (d i) (J i) (Hbound i)) :
    CanonicalGeometry.RootFirstJetMatching D S C
      (n04WholeReferenceGaugeAtlasData C L (n04bActualTypedAtlas hT hS hN hfield e₀)
        e cell (fun i => positiveReferenceCylinderChart (Y i))
        (fun i => positiveReferenceCylinderInverse (Y i)) (fun i p => H i p.1) τ σ Q N)
      newBase ε' := by
  let K := n04bActualTypedAtlas hT hS hN hfield e₀
  let ψ := fun i => positiveReferenceCylinderChart (Y i)
  let χ := fun i => positiveReferenceCylinderInverse (Y i)
  let h₀ := fun i (p : PolarPoint) => H i p.1
  let V := n04WholeReferenceGaugeAtlasData C L K e cell ψ χ h₀ τ σ Q N
  have hcut : CanonicalCutGeometry S C K base ε :=
    n04bActualTypedAtlas_cutGeometry hT hS hN hfield e₀
  have hnegativeLeft (k m : ℕ) (side : Bool) (hk : e k = .inl (m, side)) :
      V.left k = 0 := by
    have hf := n04WholeReferenceGaugeAtlasData_negative_fields
      C L K e cell ψ χ h₀ τ σ Q N (C.referenceState, 0) k (m, side) hk
    apply hf.1.trans
    obtain ⟨_, _, _, _, _, _, hl, hr, _, _⟩ := hcut.1 m
    cases side <;> assumption
  have hpositiveMetadata (k : ℕ) (i : N04PositiveComponent D.a D.b (deriv D.w))
      (hk : e k = .inr i) :
      V.left k = 0 ∧ V.right k = 1 ∧
        V.physicalRight k = n04PositiveRight i := by
    have hf := n04WholeReferenceGaugeAtlasData_positive_fields
      C L K e cell ψ χ h₀ τ σ Q N (C.referenceState, 0) k i hk
    exact ⟨hf.1, hf.2.1, hf.2.2.2.1⟩
  have hvalid (z : AnnularState S × ℝ)
      (hz : CanonicalGeometry.TransmissionParameter S C newBase ε' z) :
      z ∈ stateNeighborhood S C newBase ε' ∧ stateSector S z.1 := by
    rcases hz with rfl | hz
    · exact ⟨reference_mem_stateNeighborhood S C newBase hε',
        hN.1.1.2.2.1.stateSector⟩
    · exact hz
  intro il ir _hne hadj hzero
  have htypes := n04WholeReferenceGaugeAtlasData_actual_root_types
    hT hS hN hfield e₀ e cell ψ χ h₀ τ σ Q N il ir hadj hzero
  rcases htypes with ⟨m, i, hl, hr, hroot⟩ | ⟨i, m, hl, hr, hroot⟩
  · refine ⟨0, 0, -1, 1, Or.inl (hnegativeLeft il m true hl).symm,
      Or.inl (hpositiveMetadata ir i hr).1.symm, Or.inr rfl, Or.inl rfl, ?_⟩
    intro z hz θ
    have hz' := hvalid z hz
    have hzold := stateNeighborhood_mono S C hb hε'ε hz'.1
    have hpair := n04WholeReferenceGaugeAtlasData_actual_root_firstJets
      hT hS hN hfield e₀ e cell Y H τ σ Q N i (j i)
      (hgeometry i) (hYjets i) (hHjets i) hzold hz'.2 hn
      (hmatching z hz'.1 hz'.2 i) ir il m true hr hl hroot θ
    have hrad := n04WholeCanonicalAtlasData_actual_reference_radii
      hT hS hN hfield e₀ e cell σ τ Q N il
    have hp : V.physicalRight il = C.right m := by
      simpa only [hl, n04WholePieceRight, n04bNegativeRight, ↓reduceIte] using hrad.2
    dsimp only
    rw [hp]
    exact ⟨(congrArg Prod.fst hpair.2.1.value).symm.trans hpair.1,
      hpair.2.1.value.symm, hpair.2.1.fderiv.value.symm,
      hpair.2.2.value.symm, hpair.2.2.fderiv.value.symm⟩
  · refine ⟨1, 0, 1, 1, Or.inr (hpositiveMetadata il i hl).2.1.symm,
      Or.inl (hnegativeLeft ir m false hr).symm, Or.inl rfl, Or.inl rfl, ?_⟩
    intro z hz θ
    have hz' := hvalid z hz
    have hzold := stateNeighborhood_mono S C hb hε'ε hz'.1
    have hpair := n04WholeReferenceGaugeAtlasData_actual_root_firstJets
      hT hS hN hfield e₀ e cell Y H τ σ Q N i (j i)
      (hgeometry i) (hYjets i) (hHjets i) hzold hz'.2 hn
      (hmatching z hz'.1 hz'.2 i) il ir m false hl hr hroot θ
    have hp : V.physicalRight il = C.left m :=
      (hpositiveMetadata il i hl).2.2.trans hroot
    dsimp only
    rw [hp]
    exact ⟨hpair.1, hpair.2.1.value, hpair.2.1.fderiv.value,
      hpair.2.2.value, hpair.2.2.fderiv.value⟩

end ContinuousFlexibility.Analysis
