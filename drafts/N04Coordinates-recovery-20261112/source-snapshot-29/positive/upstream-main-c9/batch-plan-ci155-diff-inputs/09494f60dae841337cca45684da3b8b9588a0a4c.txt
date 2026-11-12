import ContinuousFlexibility.Analysis.N05ReferenceSymbolClosure
import ContinuousFlexibility.Analysis.N05CanonicalGeometryAccess

/-!
# The actual image of the negative cut

Continuity sends a physical endpoint to the closed canonical interval.
An interior canonical image is impossible because the actual smooth inverse
would extend the interior inverse identity to that endpoint.  At the cut,
the reference determinant is strictly negative, so the image is the nonzero
canonical endpoint.  The argument treats both physical halves uniformly.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

/-- A point on the actual current physical boundary maps to a canonical
endpoint. Closed inverse identities rule out an interior image. -/
theorem n05_chart_physical_boundary_image
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S}
    {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
    (h04 : N04Properties D T S C L K base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) {m : ℕ} {x : PolarPoint}
    (hx : x ∈ frontier (physicalPieceOpen S K z m)) :
    (K.chart z m x).1 = K.left m ∨ (K.chart z m x).1 = K.right m := by
  have hopen := (h04.1.domains z hz hs m).1
  rw [hopen.frontier_eq] at hx
  have hboundary := h04.1.boundary z hz hs m
  have hxClosed : x ∈ physicalPieceClosed S K z m := hx.1
  have himage : (K.chart z m x).1 ∈ Icc (K.left m) (K.right m) :=
    (hboundary.1 hxClosed).1
  by_cases hleftEnd : (K.chart z m x).1 = K.left m
  · exact Or.inl hleftEnd
  by_cases hrightEnd : (K.chart z m x).1 = K.right m
  · exact Or.inr hrightEnd
  have hy : K.chart z m x ∈ canonicalOpen S K m :=
    ⟨⟨lt_of_le_of_ne himage.1 (Ne.symm hleftEnd),
      lt_of_le_of_ne himage.2 hrightEnd⟩, mem_univ _⟩
  have hinside := (h04.1.charts z hz hs m).2.1 hy
  have hinverse := hboundary.2.2.1 x hxClosed
  rw [hinverse] at hinside
  exact (hx.2 hinside).elim

/-- The stored radial endpoints describe the physical boundary only at
reference. This specialization preserves the reference cut-image interface. -/
theorem n05_reference_chart_physical_boundary_image
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S}
    {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hs : stateSector S C.referenceState) {m : ℕ} {x : PolarPoint}
    (hx : x.1 = K.physicalLeft m ∨ x.1 = K.physicalRight m) :
    (K.chart (C.referenceState, 0) m x).1 = K.left m ∨
      (K.chart (C.referenceState, 0) m x).1 = K.right m := by
  have hxClosed : x.1 ∈ Icc (K.physicalLeft m) (K.physicalRight m) := by
    rcases hx with hxl | hxr
    · rw [hxl]
      exact ⟨le_rfl, (h04.1.referenceBounds m).1.le⟩
    · rw [hxr]
      exact ⟨(h04.1.referenceBounds m).1.le, le_rfl⟩
  have hxFrontier : x ∈ frontier (physicalPieceOpen S K (C.referenceState, 0) m) := by
    rw [(h04.1.domains (C.referenceState, 0) hz hs m).1.frontier_eq]
    refine ⟨?_, ?_⟩
    · change x ∈ physicalPieceClosed S K (C.referenceState, 0) m
      rw [n05_reference_physicalClosed_eq h04 m]
      exact ⟨hxClosed, mem_univ _⟩
    · intro hinside
      rw [h04.1.referenceDomain m] at hinside
      have hr : x.1 ∈ Ioo (K.physicalLeft m) (K.physicalRight m) := hinside.1
      rcases hx with hxl | hxr
      · rw [hxl] at hr
        exact lt_irrefl _ hr.1
      · rw [hxr] at hr
        exact lt_irrefl _ hr.2
  exact n05_chart_physical_boundary_image h04 hz hs hxFrontier

/-- Strict negative physical slope forces positive canonical radius, even at
a physical endpoint lying inside the annulus. -/
theorem n05_negative_reference_radius_pos
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    {m : ℕ} (hm : K.positive m = false) {x : PolarPoint}
    (hx : x.1 ∈ Icc (K.physicalLeft m) (K.physicalRight m))
    (hxD : x ∈ annularOpen D) (hd : deriv D.w x.1 < 0) :
    0 < (K.chart (C.referenceState, 0) m x).1 := by
  have h01 := h.1.1.1
  obtain ⟨B, hB⟩ := h01.1.1
  have hr : 0 < x.1 := hB.1.1.trans hxD.1.1
  have hw : 0 < D.w x.1 := hB.1.2.2.2.2.1 x.1 hxD.1
  have h04 := h.2.2.2.2.1
  have hh := (n05_reference_closed_properties h04 (n05_referenceState_mem h01.2.1)
    (n05_referenceState_sector h01.2.2.1) m x hx).2.2.2
  have hnegative : K.height (C.referenceState, 0) m x ^ 4 *
      (D.w x.1 * (deriv D.w x.1 / x.1)) < 0 :=
    mul_neg_of_pos_of_neg (pow_pos hh 4) (mul_neg_of_pos_of_neg hw
      (div_neg_of_neg_of_pos hd hr))
  have heq := n05_negative_reference_determinant_closed hT hS h hm hx
  linarith only [heq, hnegative]

/-- The two physical halves have the same actual canonical cut image.
The index argument treats both halves with one proof. -/
theorem n05_cut_reference_image
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (m : ℕ) {i : ℕ} (hi : i = (K.cutPair m).1 ∨ i = (K.cutPair m).2) (θ : ℝ) :
    (K.chart (C.referenceState, 0) i (K.physicalRight (K.cutPair m).1, θ)).1 =
      K.cutRadius m := by
  have h01 := h.1.1.1
  have h04 := h.2.2.2.2.1
  have hpieces := h04.1.referenceBounds
  have hcutpair := h04.2.1.1.1
  obtain ⟨hnegL, hnegR, hleft, hright, hmeet, _, hzeroL, hzeroR, hendL, hendR⟩ :=
    hcutpair m
  let c : ℝ := K.physicalRight (K.cutPair m).1
  have hcut : c ∈ Ioo (C.left m) (C.right m) := by
    constructor
    · simpa only [c, hleft] using (hpieces (K.cutPair m).1).1
    · simpa only [c, ← hmeet, hright] using (hpieces (K.cutPair m).2).1
  have hdata : K.positive i = false ∧ K.left i = 0 ∧ K.right i = K.cutRadius m ∧
      (c = K.physicalLeft i ∨ c = K.physicalRight i) := by
    rcases hi with rfl | rfl
    · exact ⟨hnegL, hzeroL, hendL, Or.inr rfl⟩
    · exact ⟨hnegR, hzeroR, hendR, Or.inl hmeet⟩
  have hcClosed : c ∈ Icc (K.physicalLeft i) (K.physicalRight i) := by
    rcases hdata.2.2.2 with hcl | hcr
    · rw [hcl]
      exact ⟨le_rfl, (hpieces i).1.le⟩
    · rw [hcr]
      exact ⟨(hpieces i).1.le, le_rfl⟩
  have hgeom := h01.2.2.2.1
  have hcD : (c, θ) ∈ annularOpen D :=
    ⟨⟨(hgeom.1 m).1.trans hcut.1, hcut.2.trans (hgeom.1 m).2.2⟩, mem_univ _⟩
  have hd : deriv D.w c < 0 := hgeom.2.2.2.1 m c hcut
  have hpositive := n05_negative_reference_radius_pos hT hS h hdata.1
    (x := (c, θ)) hcClosed hcD hd
  have himage := n05_reference_chart_physical_boundary_image h.2.2.2.2.1
    (n05_referenceState_mem h01.2.1) (n05_referenceState_sector h01.2.2.1)
    (x := (c, θ)) hdata.2.2.2
  rw [hdata.2.1, hdata.2.2.1] at himage
  exact himage.resolve_left hpositive.ne'

end ContinuousFlexibility.Statements
