module

public import ContinuousFlexibility.Analysis.CanonicalWholeNegativeBoundary
public import ContinuousFlexibility.Analysis.MaterialEndpointWeightRatios
public import ContinuousFlexibility.Analysis.N01ReturnMargins
public import Mathlib.Topology.Order.OrderClosed

/-!
# Actual material ratios for the closed negative transport

The return-margin clause of the same N01 witness supplies a genuine
containing cell for each open negative component. Its uniform endpoint
coordinate bound extends to the true roots by continuity. The actual
closed transport remains in that component, so no new material data,
control geometry, or prescribed cell assignment is needed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped Topology

private theorem continuousOn_endpointX_one_core (D : ReferenceData) :
    ContinuousOn (fun r => endpointX 1 (Statements.endpointDistance D r)) (Ioo D.a D.b) := by
  have hd : Continuous (Statements.endpointDistance D) :=
    (continuous_id.sub continuous_const).min (continuous_const.sub continuous_id)
  have hp (r : ℝ) (hr : r ∈ Ioo D.a D.b) : 0 < Statements.endpointDistance D r :=
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
      |endpointX 1 (Statements.endpointDistance D r) - endpointX 1 (Statements.endpointDistance D s)| ≤ L := by
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
      (fun x => |endpointX 1 (Statements.endpointDistance D x) - (D.cellIndex j : ℝ)|)
      (closure (Ioo (C.left m) (C.right m))) := by
    rw [closure_Ioo hb.2.1.ne]
    exact ((continuousOn_endpointX_one_core D).sub continuousOn_const).abs.mono hsub
  have hclosed (x : ℝ) (hx : x ∈ Icc (C.left m) (C.right m)) :
      |endpointX 1 (Statements.endpointDistance D x) - (D.cellIndex j : ℝ)| ≤ B :=
    le_on_closure (fun y hy => (hindex j y (hhost hy)).1) hcont continuousOn_const
      (by simpa only [closure_Ioo hb.2.1.ne] using hx)
  calc
    _ ≤ |endpointX 1 (Statements.endpointDistance D r) - (D.cellIndex j : ℝ)| +
        |(D.cellIndex j : ℝ) - endpointX 1 (Statements.endpointDistance D s)| := abs_sub_le _ _ _
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
