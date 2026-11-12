import ContinuousFlexibility.Analysis.CanonicalWholeNegativeTransport
import ContinuousFlexibility.Analysis.MaterialEndpointWeightRatios
import ContinuousFlexibility.Analysis.N01ReturnMargins
import Mathlib.Topology.Order.OrderClosed

/-!
# Actual material ratios for the closed negative transport

The return-margin clause of the same N01 witness supplies a genuine
containing cell for each open negative component. Its uniform endpoint
coordinate bound extends to the true roots by continuity. The actual
closed transport remains in that component, so no new material data,
control geometry, or prescribed cell assignment is needed.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped Topology

private theorem continuousOn_endpointX_one_core (D : ReferenceData) :
    ContinuousOn (fun r => endpointX 1 (endpointDistance D r)) (Ioo D.a D.b) := by
  have hd : Continuous (endpointDistance D) :=
    (continuous_id.sub continuous_const).min (continuous_const.sub continuous_id)
  have hp (r : ℝ) (hr : r ∈ Ioo D.a D.b) : 0 < endpointDistance D r :=
    lt_min (sub_pos.mpr hr.1) (sub_pos.mpr hr.2)
  exact ((continuousOn_const.div hd.continuousOn
    (fun r hr => (hp r hr).ne')).log
      (fun r hr => (div_pos zero_lt_one (hp r hr)).ne')).sqrt

/-- One bound, before all components, controls the actual endpoint
coordinate over each closed negative interval of the same N01 witness. -/
theorem n01_negativeComponent_endpointX_oscillation
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hN : N01Properties D T S C base loss ε) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ m r s,
      r ∈ Icc (C.left m) (C.right m) → s ∈ Icc (C.left m) (C.right m) →
      |endpointX 1 (endpointDistance D r) - endpointX 1 (endpointDistance D s)| ≤ L := by
  have hdata := hT
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hcell⟩ := hdata
  obtain ⟨B, A, hB, _, hindex⟩ := hcell
  obtain ⟨_, _, hmargin⟩ := n01Properties_returnMargins hN
  refine ⟨2 * B, mul_nonneg (by norm_num) hB.le, ?_⟩
  intro m r s hr hs
  obtain ⟨j, hhost, _⟩ := (hmargin m).2
  have hb := hN.2.2.2.1.1 m
  have hsub : Icc (C.left m) (C.right m) ⊆ Ioo D.a D.b :=
    fun x hx => ⟨hb.1.trans_le hx.1, hx.2.trans_lt hb.2.2⟩
  have hcont : ContinuousOn
      (fun x => |endpointX 1 (endpointDistance D x) - (D.cellIndex j : ℝ)|)
      (closure (Ioo (C.left m) (C.right m))) := by
    rw [closure_Ioo hb.2.1.ne]
    exact ((continuousOn_endpointX_one_core D).sub continuousOn_const).abs.mono hsub
  have hclosed (x : ℝ) (hx : x ∈ Icc (C.left m) (C.right m)) :
      |endpointX 1 (endpointDistance D x) - (D.cellIndex j : ℝ)| ≤ B :=
    le_on_closure (fun y hy => (hindex j y (hhost hy)).1) hcont continuousOn_const
      (by simpa only [closure_Ioo hb.2.1.ne] using hx)
  calc
    _ ≤ |endpointX 1 (endpointDistance D r) - (D.cellIndex j : ℝ)| +
        |(D.cellIndex j : ℝ) - endpointX 1 (endpointDistance D s)| := abs_sub_le _ _ _
    _ ≤ B + B := add_le_add (hclosed r hr)
      (by simpa only [abs_sub_comm] using hclosed s hs)
    _ = 2 * B := (two_mul B).symm

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
  (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
  (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
  (hfield : N04bFieldRegularity D S C L base ε)
  (e : ℕ ≃ N04PieceIndex D)

theorem canonicalWholeNegativeTransport_root_radial
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (side : Bool) (θ : ℝ) :
    let K := n04bActualTypedAtlas hT hS hN hfield e
    (canonicalWholeNegativeTransport C K z m
      (if side then C.right m else C.left m, θ)).1 =
        if side then C.right m else C.left m := by
  let K := n04bActualTypedAtlas hT hS hN hfield e
  have hab : C.left m < C.right m := (hN.1.1.2.2.2.1.1 m).2.1
  have hg := closedComponentField_root_germ
    (fun s => canonicalCurrentPoint C K z
      (if s then (K.cutPair m).2 else (K.cutPair m).1)) hab side θ
  have he : canonicalWholeNegativeTransport C K z m
      (if side then C.right m else C.left m, θ) =
      canonicalCurrentPoint C K z (if side then (K.cutPair m).2 else (K.cutPair m).1)
        (if side then C.right m else C.left m, θ) := hg.eq_of_nhds
  exact (congrArg (fun p : PolarPoint => p.1) he).trans
    ((n04Coordinates_actualAtlas_endpoint_fields hT hS hN hfield e hz hs m side).root_radial θ)

theorem canonicalWholeNegativeTransport_mapsTo_closed
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) :
    let K := n04bActualTypedAtlas hT hS hN hfield e
    MapsTo (canonicalWholeNegativeTransport C K z m)
      (Icc (C.left m) (C.right m) ×ˢ (univ : Set ℝ))
      (Icc (C.left m) (C.right m) ×ˢ (univ : Set ℝ)) := by
  let K := n04bActualTypedAtlas hT hS hN hfield e
  have hab : C.left m < C.right m := (hN.1.1.2.2.2.1.1 m).2.1
  have hroot := canonicalWholeNegativeTransport_root_radial hT hS hN hfield e hz hs m
  have heq : EqOn (canonicalWholeNegativeTransport C K z m)
      (n04CoordinatesNegativeTravelTransition S C L z m)
      (Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ)) :=
    (canonicalWholeNegativeTransport_eq_travel hT hS hN hfield e hz hs m).1
  intro p hp
  refine ⟨?_, mem_univ _⟩
  by_cases hl : p.1 = C.left m
  · have he : p = (C.left m, p.2) := Prod.ext hl rfl
    have hv : (canonicalWholeNegativeTransport C K z m p).1 = C.left m :=
      (congrArg (fun q => (canonicalWholeNegativeTransport C K z m q).1) he).trans
        (hroot false p.2)
    rw [hv]
    exact ⟨le_rfl, hab.le⟩
  by_cases hr : p.1 = C.right m
  · have he : p = (C.right m, p.2) := Prod.ext hr rfl
    have hv : (canonicalWholeNegativeTransport C K z m p).1 = C.right m :=
      (congrArg (fun q => (canonicalWholeNegativeTransport C K z m q).1) he).trans
        (hroot true p.2)
    rw [hv]
    exact ⟨hab.le, le_rfl⟩
  have hpin : p ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ) :=
    ⟨⟨lt_of_le_of_ne hp.1.1 (Ne.symm hl), lt_of_le_of_ne hp.1.2 hr⟩, mem_univ _⟩
  have himage := n04CoordinatesNegativeTravelTransition_mapsTo hT hS hN hfield hz hs m hpin
  rw [heq hpin]
  exact ⟨himage.1.1.le, himage.1.2.le⟩

/-- The same actual atlas and same Through03 witness yield both requested
ratios, uniformly before the state, component and physical point. -/
theorem canonicalWholeNegativeTransport_material_ratios :
    ∃ B A : ℝ, 0 < B ∧ 0 ≤ A ∧
      ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 → ∀ m p,
      p ∈ Icc (C.left m) (C.right m) ×ˢ (univ : Set ℝ) →
      let K := n04bActualTypedAtlas hT hS hN hfield e
      let q := canonicalWholeNegativeTransport C K z m p
      T.H q.1 / T.H p.1 ≤ B * T.E0 p.1 ^ A ∧
        T.M q.1 / T.M p.1 ≤ B * T.E0 p.1 ^ A := by
  obtain ⟨V, hV, hosc⟩ := n01_negativeComponent_endpointX_oscillation hT hN.1.1
  obtain ⟨B, A, hB, hA, hweights⟩ :=
    material_H_M_ratios_of_bounded_endpointX_shift hT hN.1.1.1.1 hV
  refine ⟨B, A, hB, hA, ?_⟩
  intro z hz hs m p hp
  let K := n04bActualTypedAtlas hT hS hN hfield e
  let q := canonicalWholeNegativeTransport C K z m p
  have hq : q ∈ Icc (C.left m) (C.right m) ×ˢ (univ : Set ℝ) :=
    canonicalWholeNegativeTransport_mapsTo_closed hT hS hN hfield e hz hs m hp
  have hb := hN.1.1.2.2.2.1.1 m
  have hpcore : p.1 ∈ Ioo D.a D.b :=
    ⟨hb.1.trans_le hp.1.1, hp.1.2.trans_lt hb.2.2⟩
  have hqcore : q.1 ∈ Ioo D.a D.b :=
    ⟨hb.1.trans_le hq.1.1, hq.1.2.trans_lt hb.2.2⟩
  exact hweights q.1 p.1 hqcore hpcore (hosc m q.1 p.1 hq.1 hp.1)

end ContinuousFlexibility.Analysis
