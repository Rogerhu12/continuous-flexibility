module

public import ContinuousFlexibility.Analysis.ConstructedRootCutFirstJets
public import ContinuousFlexibility.Analysis.N04bActualAtlasCuts
public import ContinuousFlexibility.Analysis.N04bActualCharacteristics
public import ContinuousFlexibility.Analysis.WholeCanonicalAtlasData

/-!
# The actual atlas has the forward first jets at every middle cut

The cut point is the genuine middle-travel inverse. The stored forward
charts and heights have the constructed germs there on the whole
negative component. This gives the new forward transmission condition
directly, and the whole-component enumeration retains exactly these
negative fields and cuts.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

private theorem n04Coordinates_actualAtlas_middle_firstJets
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    (e : ℕ ≃ N04PieceIndex D)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (θ : ℝ) :
    let K := n04bActualTypedAtlas hT hS hN hfield e
    let p := n04bActualTravelInverse S C L z m (C.travel m / 2, θ)
    let ρ := n04bRootCutRadius (C.travel m)
    let Fi := CanonicalGeometry.endpointAlignedChart K z (e.symm (.inl (m, false))) ρ 1
    let Fj := CanonicalGeometry.endpointAlignedChart K z (e.symm (.inl (m, true))) ρ (-1)
    (Fi p).1 = 0 ∧ Fi p = Fj p ∧ fderiv ℝ Fi p = fderiv ℝ Fj p ∧
      K.height z (e.symm (.inl (m, false))) p =
        K.height z (e.symm (.inl (m, true))) p ∧
      fderiv ℝ (K.height z (e.symm (.inl (m, true)))) p -
        fderiv ℝ (K.height z (e.symm (.inl (m, false)))) p =
          (-(K.height z (e.symm (.inl (m, false))) p / (2 * ρ))) •
            fderiv ℝ (fun q => (K.chart z (e.symm (.inl (m, false))) q).1) p := by
  let K := n04bActualTypedAtlas hT hS hN hfield e
  let F := n04bActualTravelChart S C L z m
  let x := n04bActualTravelInverse S C L z m (C.travel m / 2, θ)
  let ρ := n04bRootCutRadius (C.travel m)
  let X := n04bRootPhysicalChart F (C.travel m)
  let H := n04bRootPhysicalHeight (L.coefficients z)
    (n04bCharacteristicHalfGap (L.coefficients z)) F (C.travel m)
  let piece := fun side : Bool => e.symm (.inl (m, side))
  have hpos := n04b_actualTravel_positive hN hS hT hfield hz hs m
  have hmid : (C.travel m / 2, θ) ∈
      Ioo (0 : ℝ) (C.travel m) ×ˢ (univ : Set ℝ) :=
    ⟨⟨half_pos hpos, half_lt_self hpos⟩, mem_univ _⟩
  have hInv := n04b_actualTravelInverse_spec hN hS hT hfield hz hs m
  have hx : x ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ) := hInv.1 hmid
  have hpoint : F x = (C.travel m / 2, θ) := hInv.2.2.1 hmid
  have hF : ContDiffAt ℝ ∞ F x :=
    (n04b_actualTravelChart_smooth hN hS hT hfield hz hs m).contDiffAt
      ((isOpen_Ioo.prod isOpen_univ).mem_nhds hx)
  have hcontrol : controlGeometryConditions D S C := hN.1.1.2.2.2.1
  have hxD : x ∈ annularOpen D :=
    ⟨⟨(hcontrol.1 m).1.trans hx.1.1, hx.1.2.trans (hcontrol.1 m).2.2⟩, mem_univ _⟩
  have ha := (hfield.smooth_coefficients z hz hs).1.contDiffAt
    ((isOpen_Ioo.prod isOpen_univ).mem_nhds hxD)
  have hv := (n04b_corrected_characteristics_contDiffAt hN hfield hz hs m hx).2.1
  have hB : ContDiffAt ℝ ∞
      (fun y => (L.coefficients z).a y * n04bCharacteristicHalfGap (L.coefficients z) y) x :=
    ha.mul hv
  have hBp : 0 < (L.coefficients z).a x * n04bCharacteristicHalfGap (L.coefficients z) x :=
    mul_pos (hfield.positive_a z hz hs x hxD)
      (n04b_actualCharacteristic_halfGap_pos hN hfield hz hs m hx)
  have hmath := n04Coordinates_constructedRoot_cut_firstJets (L.coefficients z)
    (n04bCharacteristicHalfGap (L.coefficients z)) F hpos (x := x) (θ := θ)
    hpoint hF hB hBp
  have hg (side : Bool) :
      K.chart z (piece side) =ᶠ[𝓝 x] X side ∧
        K.height z (piece side) =ᶠ[𝓝 x] H side :=
    n04bActualTypedAtlas_negative_component_germs hT hS hN hfield e hz hs
      (piece side) m side (e.apply_symm_apply _) hx
  have hFl : CanonicalGeometry.endpointAlignedChart K z (piece false) ρ 1 =ᶠ[𝓝 x]
      (fun y => ((X false y).1 - ρ, (X false y).2)) := by
    filter_upwards [(hg false).1] with y hy
    simp only [CanonicalGeometry.endpointAlignedChart, hy, one_mul]
  have hFr : CanonicalGeometry.endpointAlignedChart K z (piece true) ρ (-1) =ᶠ[𝓝 x]
      (fun y => (-((X true y).1 - ρ), (X true y).2)) := by
    filter_upwards [(hg true).1] with y hy
    simp only [CanonicalGeometry.endpointAlignedChart, hy, neg_one_mul]
  have hrad : (fun y => (K.chart z (piece false) y).1) =ᶠ[𝓝 x]
      (fun y => (X false y).1) := by
    filter_upwards [(hg false).1] with y hy
    exact congrArg Prod.fst hy
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (congrArg Prod.fst hFl.self_of_nhds).trans (congrArg Prod.fst hmath.1)
  · exact hFl.self_of_nhds.trans (hmath.2.1.symm.trans hFr.self_of_nhds.symm)
  · exact hFl.fderiv_eq.trans (hmath.2.2.1.trans hFr.fderiv_eq.symm)
  · exact (hg false).2.self_of_nhds.trans
      (hmath.2.2.2.1.trans (hg true).2.self_of_nhds.symm)
  · rw [(hg true).2.fderiv_eq, (hg false).2.fderiv_eq,
      (hg false).2.self_of_nhds, hrad.fderiv_eq]
    exact hmath.2.2.2.2

theorem n04Coordinates_actualAtlas_cutFirstJetMatching
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    (e : ℕ ≃ N04PieceIndex D) :
    CanonicalGeometry.CutFirstJetMatching S C
      (n04bActualTypedAtlas hT hS hN hfield e) base ε := by
  intro m z hz θ
  have hvalid : z ∈ stateNeighborhood S C base ε ∧ stateSector S z.1 := by
    rcases hz with rfl | hz
    · exact n04b_reference_valid_of_through03 hN
    · exact hz
  dsimp only
  rw [n04bActualTypedAtlas_cutPoint hT hS hN hfield e hvalid.1 hvalid.2 m]
  simpa only [n04bActualTypedAtlas, n04bTypedAtlasData_cutPair,
    n04bTypedAtlasData_cutRadius] using
      n04Coordinates_actualAtlas_middle_firstJets hT hS hN hfield e hvalid.1 hvalid.2 m θ

theorem n04WholeCanonicalAtlasData_cutFirstJetMatching
    {D : ReferenceData} {S : PhysicalSpacesData}
    (C : NonlinearGeometryData S) (L : ReturnCorrectionData S) (K : CanonicalData S)
    (e : ℕ ≃ N04WholePieceIndex D)
    (cell : N04PositiveComponent D.a D.b (deriv D.w) → ℕ)
    (F G : (AnnularState S × ℝ) →
      N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → PolarPoint)
    (Q : (AnnularState S × ℝ) →
      N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → ℝ)
    (N : Set ℝ) {base : ℕ} {ε : ℝ}
    (hcut : CanonicalGeometry.CutFirstJetMatching S C K base ε) :
    CanonicalGeometry.CutFirstJetMatching S C
      (n04WholeCanonicalAtlasData C L K e cell F G Q N) base ε := by
  intro m z hz θ
  have hE (V : CanonicalData S) (j : ℕ) (ρ s : ℝ) :
      CanonicalGeometry.endpointAlignedChart V z j ρ s =
        (fun p : PolarPoint => (s * ((V.chart z j p).1 - ρ), (V.chart z j p).2)) := rfl
  simpa only [hE, canonicalCutPoint,
    n04WholeCanonicalAtlasData, n04bWithInteriorDivision,
    n04WholeCutPair, Equiv.apply_symm_apply,
    Bool.false_eq_true, ite_false, ite_true] using hcut m z hz θ

end ContinuousFlexibility.Analysis
