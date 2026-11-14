module

public import ContinuousFlexibility.Analysis.N05CanonicalGeometryAccess
public import ContinuousFlexibility.Analysis.N05TricomiNullCoordinates
public import ContinuousFlexibility.Analysis.N05DerivativeOrientation

/-!
# Orientation of the actual reference null and radial coordinates

For each fixed physical radius, the null coordinates are degree-one
pi-periodic lifts with continuous nonzero angular derivative.  Hence their
angular derivatives are positive.  The first principal identity makes the
radial derivative of the canonical radius nonzero; the actual root and cut
values then fix its sign on either half by one oriented mean-value argument.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}

theorem n05_negative_reference_null_angular_pos
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    {m : ℕ} (hm : K.positive m = false) {x : PolarPoint}
    (hx : x ∈ referencePhysicalPieceOpen S K m) {σ : ℝ} (hσ : σ ^ 2 = 1) :
    0 < angularPartial (n05NullCoordinate (K.chart (C.referenceState, 0) m) σ) x := by
  let N : PolarPoint → ℝ := n05NullCoordinate (K.chart (C.referenceState, 0) m) σ
  have h01 := h.1.1.1
  have h04 := h.2.2.2.2.1
  have hpieces := h04.1.referenceBounds
  have hnegative := h04.1.referenceNegative
  have hclosed := n05_reference_closed_properties h04
  have hxClosed : x.1 ∈ Icc (K.physicalLeft m) (K.physicalRight m) :=
    ⟨hx.1.1.le, hx.1.2.le⟩
  have hmem : (C.referenceState, 0) ∈ stateNeighborhood S C base ε :=
    n05_referenceState_mem h01.2.1
  have hsector := n05_referenceState_sector h01.2.2.1
  have hN (θ : ℝ) : ContDiffAt ℝ ∞ N (x.1, θ) := by
    have hp : (x.1, θ) ∈ annularOpen D := ⟨(hpieces m).2.2 hx.1, mem_univ _⟩
    have hpositive := n05_negative_reference_radius_pos hT hS h hm
      (x := (x.1, θ)) hxClosed hp (hnegative m hm x.1 hx.1)
    exact n05NullCoordinate_contDiffAt
      (hclosed hmem hsector m (x.1, θ) hxClosed).1 hpositive σ
  have hd (θ : ℝ) : HasDerivAt (fun t => N (x.1, t))
      (angularPartial N (x.1, θ)) θ :=
    Radial.hasDerivAt_angularSlice ((hN θ).differentiableAt (by simp))
  have hc : Continuous (fun θ : ℝ => angularPartial N (x.1, θ)) :=
    continuous_iff_continuousAt.mpr fun θ =>
      (contDiffAt_angularPartial (m := 0) (hN θ) (by simp)).continuousAt.comp
        (f := fun t : ℝ => (x.1, t))
        (continuousAt_const.prodMk continuousAt_id)
  have hne (θ : ℝ) : angularPartial N (x.1, θ) ≠ 0 :=
    n05_negative_reference_null_angular_ne_zero hT hS h hm
      (x := (x.1, θ)) ⟨hx.1, mem_univ _⟩ hσ
  have hlift (θ : ℝ) : N (x.1, θ + Real.pi) = N (x.1, θ) + Real.pi := by
    have hchart : K.chart (C.referenceState, 0) m (x.1, θ + Real.pi) =
        K.chart (C.referenceState, 0) m (x.1, θ) + (0, Real.pi) := by
      simpa only [Prod.mk_add_mk, add_zero] using
        (n05_reference_closed_periodicity h.2.2.2.2.1 hmem hsector m
          (p := (x.1, θ)) hxClosed).1
    simp only [N, n05NullCoordinate, hchart, Prod.fst_add, Prod.snd_add, add_zero]
    ring
  exact n05_derivative_pos_of_periodic_lift Real.pi_pos hd hc hne hlift x.2

theorem n05_negative_reference_radial_ne_zero
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    {m : ℕ} (hm : K.positive m = false) {x : PolarPoint}
    (hx : x ∈ referencePhysicalPieceOpen S K m) :
    radialPartial (fun p => (K.chart (C.referenceState, 0) m p).1) x ≠ 0 := by
  have h01 := h.1.1.1
  have h04 := h.2.2.2.2.1
  have hnegative := h04.1.referenceNegative
  have hclosed := n05_reference_closed_properties h04
  have hxClosed : x.1 ∈ Icc (K.physicalLeft m) (K.physicalRight m) :=
    ⟨hx.1.1.le, hx.1.2.le⟩
  have hr : 0 < x.1 := n05_physical_closed_radius_pos h01.1.1 h.2.2.2.2.1 hxClosed
  have hc : deriv D.w x.1 / x.1 ≤ 0 :=
    (div_neg_of_neg_of_pos (hnegative m hm x.1 hx.1) hr).le
  have hJ := (hclosed (n05_referenceState_mem h01.2.1)
    (n05_referenceState_sector h01.2.2.1) m x hxClosed).2.2.1
  have hsym := (n05_negative_reference_symbol_closed hT hS h hm hxClosed).1
  intro hzero
  simp only [n05PrincipalPair, n05RadialReferenceCoefficients, hzero,
    zero_mul, mul_zero, zero_add, add_zero] at hsym
  have hnonpos : (deriv D.w x.1 / x.1) *
      angularPartial (fun p => (K.chart (C.referenceState, 0) m p).1) x *
      angularPartial (fun p => (K.chart (C.referenceState, 0) m p).1) x ≤ 0 := by
    simpa only [pow_two, mul_assoc] using
      mul_nonpos_of_nonpos_of_nonneg hc
        (sq_nonneg (angularPartial (fun p => (K.chart (C.referenceState, 0) m p).1) x))
  have hbad := mul_nonpos_of_nonneg_of_nonpos
    (sq_nonneg (K.height (C.referenceState, 0) m x)) hnonpos
  rw [hsym] at hbad
  have hpos : (0 : ℝ) < |planeJacobian (K.chart (C.referenceState, 0) m) x| :=
    abs_pos.mpr hJ
  exact (not_le_of_gt hpos) hbad

/-- An oriented endpoint increment fixes the true radial derivative of the
canonical radius on a negative piece. -/
theorem n05_negative_reference_radial_orientation
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    {m : ℕ} (hm : K.positive m = false) {x : PolarPoint}
    (hx : x ∈ referencePhysicalPieceOpen S K m) {orientation : ℝ}
    (hinc : 0 < orientation *
      ((K.chart (C.referenceState, 0) m (K.physicalRight m, x.2)).1 -
        (K.chart (C.referenceState, 0) m (K.physicalLeft m, x.2)).1)) :
    0 < orientation *
      radialPartial (fun p => (K.chart (C.referenceState, 0) m p).1) x := by
  let ξ : PolarPoint → ℝ := fun p => (K.chart (C.referenceState, 0) m p).1
  have h01 := h.1.1.1
  have h04 := h.2.2.2.2.1
  have hpieces := h04.1.referenceBounds
  have hclosed := n05_reference_closed_properties h04
  have hmem : (C.referenceState, 0) ∈ stateNeighborhood S C base ε :=
    n05_referenceState_mem h01.2.1
  have hsector := n05_referenceState_sector h01.2.2.1
  have hξ (r : ℝ) (hr : r ∈ Icc (K.physicalLeft m) (K.physicalRight m)) :
      ContDiffAt ℝ ∞ ξ (r, x.2) :=
    (hclosed hmem hsector m (r, x.2) hr).1.fst
  have hf : ContinuousOn (fun r => ξ (r, x.2))
      (Icc (K.physicalLeft m) (K.physicalRight m)) := fun r hr =>
    ((hξ r hr).continuousAt.comp (f := fun t : ℝ => (t, x.2))
      (continuousAt_id.prodMk continuousAt_const)).continuousWithinAt
  have hd (r : ℝ) (hr : r ∈ Ioo (K.physicalLeft m) (K.physicalRight m)) :
      HasDerivAt (fun t => ξ (t, x.2)) (radialPartial ξ (r, x.2)) r :=
    Radial.hasDerivAt_radialSlice
      ((hξ r ⟨hr.1.le, hr.2.le⟩).differentiableAt (by simp))
  have hc : ContinuousOn (fun r => radialPartial ξ (r, x.2))
      (Ioo (K.physicalLeft m) (K.physicalRight m)) := fun r hr =>
    ((contDiffAt_radialPartial (m := 0) (hξ r ⟨hr.1.le, hr.2.le⟩) (by simp)).continuousAt.comp
      (f := fun t : ℝ => (t, x.2))
      (continuousAt_id.prodMk continuousAt_const)).continuousWithinAt
  have hne (r : ℝ) (hr : r ∈ Ioo (K.physicalLeft m) (K.physicalRight m)) :
      radialPartial ξ (r, x.2) ≠ 0 :=
    n05_negative_reference_radial_ne_zero hT hS h hm (x := (r, x.2)) ⟨hr, mem_univ _⟩
  exact n05_oriented_derivative_pos isPreconnected_Ioo (hpieces m).1
    hf hd (Subset.rfl) hc hne hinc hx.1

/-- Both cut halves have their inward orientation. The Boolean chooses the
half and its sign; the actual derivative proof is shared. -/
theorem n05_cut_reference_radial_orientation
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (m : ℕ) (right : Bool) {x : PolarPoint}
    (hx : x ∈ referencePhysicalPieceOpen S K
      (if right then (K.cutPair m).2 else (K.cutPair m).1)) :
    0 < (if right then (-1 : ℝ) else 1) *
      radialPartial (fun p => (K.chart (C.referenceState, 0)
        (if right then (K.cutPair m).2 else (K.cutPair m).1) p).1) x := by
  have h01 := h.1.1.1
  have h04 := h.2.2.2.2.1
  have hpieces := h04.1.referenceBounds
  have hcuts := h04.2.1.1.1
  obtain ⟨hnegL, hnegR, hleft, hright, hmeet, hcutpos, _⟩ := hcuts m
  have hroots := h01.2.2.2.1.2.1 m
  have hrootL :
      (K.chart (C.referenceState, 0) (K.cutPair m).1
        (K.physicalLeft (K.cutPair m).1, x.2)).1 = 0 :=
    n05_negative_reference_root_image hT hS h hnegL
      (x := (K.physicalLeft (K.cutPair m).1, x.2))
      ⟨le_rfl, (hpieces (K.cutPair m).1).1.le⟩ (by rw [hleft]; exact hroots.1)
  have hrootR :
      (K.chart (C.referenceState, 0) (K.cutPair m).2
        (K.physicalRight (K.cutPair m).2, x.2)).1 = 0 :=
    n05_negative_reference_root_image hT hS h hnegR
      (x := (K.physicalRight (K.cutPair m).2, x.2))
      ⟨(hpieces (K.cutPair m).2).1.le, le_rfl⟩ (by rw [hright]; exact hroots.2.1)
  have hcutL := n05_cut_reference_image hT hS h m
    (i := (K.cutPair m).1) (Or.inl rfl) x.2
  have hcutR :
      (K.chart (C.referenceState, 0) (K.cutPair m).2
        (K.physicalLeft (K.cutPair m).2, x.2)).1 = K.cutRadius m := by
    simpa only [hmeet] using n05_cut_reference_image hT hS h m
      (i := (K.cutPair m).2) (Or.inr rfl) x.2
  cases right with
  | false =>
    apply n05_negative_reference_radial_orientation hT hS h hnegL hx
    simpa only [Bool.false_eq_true, ↓reduceIte, hrootL, hcutL, sub_zero, one_mul]
      using hcutpos
  | true =>
    apply n05_negative_reference_radial_orientation hT hS h hnegR hx
    simpa only [↓reduceIte, hrootR, hcutR, zero_sub, neg_mul, one_mul, neg_neg]
      using hcutpos

end ContinuousFlexibility.Statements
