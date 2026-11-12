import ContinuousFlexibility.Analysis.N05CanonicalGeometryAccess
import ContinuousFlexibility.Analysis.N05OpticalProfileLipschitz
import ContinuousFlexibility.Analysis.N05ReferenceOpticalBound

/-!
# A genuine reference-cell bound for the negative Jacobian and density

The actual return margins supply a physical cell containing each whole
negative component. The optical Lipschitz estimate on that component
controls both actual canonical halves with one constant. This statement
keeps the genuine carrier cell explicit; it makes no claim equating that
cell with the separate label stored in `K.cell`.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

theorem n05_cut_physical_closed_subset_component
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S}
    {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
    (h04 : N04Properties D T S C L K base loss ε) (m : ℕ) (right : Bool) :
    Icc (K.physicalLeft (if right then (K.cutPair m).2 else (K.cutPair m).1))
        (K.physicalRight (if right then (K.cutPair m).2 else (K.cutPair m).1)) ⊆
      Icc (C.left m) (C.right m) := by
  have hpieces := h04.1.referenceBounds
  have hcuts := h04.2.1.1.1
  obtain ⟨_, _, hleft, hright, hmeet, _⟩ := hcuts m
  cases right with
  | false =>
    change Icc (K.physicalLeft (K.cutPair m).1) (K.physicalRight (K.cutPair m).1) ⊆
      Icc (C.left m) (C.right m)
    apply Icc_subset_Icc hleft.ge
    have hR := (hpieces (K.cutPair m).2).1.le
    simpa only [← hmeet, hright] using hR
  | true =>
    change Icc (K.physicalLeft (K.cutPair m).2) (K.physicalRight (K.cutPair m).2) ⊆
      Icc (C.left m) (C.right m)
    apply Icc_subset_Icc _ hright.le
    have hL := (hpieces (K.cutPair m).1).1.le
    simpa only [hleft, hmeet] using hL

/-- Both true negative half charts have one coefficient-power density
bound in a genuine cell carrying their complete physical component. -/
theorem n05_negative_reference_actualCell_density_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε) :
    ∃ B A : ℝ, 0 < B ∧ 0 < A ∧ ∀ m : ℕ, ∃ j : ℕ,
      Ioo (C.left m) (C.right m) ⊆ D.cells j ∧
      ∀ right : Bool, ∀ x ∈ referencePhysicalPieceOpen S K
          (if right then (K.cutPair m).2 else (K.cutPair m).1),
        let i := if right then (K.cutPair m).2 else (K.cutPair m).1
        let z := (C.referenceState, 0)
        |planeJacobian (K.chart z i) x| ^ 2 ≤ B * radialE (D.cellIndex j) ^ A ∧
          |planeJacobian (K.chart z i) x| / K.height z i x ^ 2 ≤
            B * radialE (D.cellIndex j) ^ A := by
  have hD : IsRadialReference D := h.1.1.1.1
  have hgeom := h.1.1.1.2.2.2.1
  obtain ⟨C₀, A, hC₀, hA, hLip⟩ := n05_opticalRadicand_cell_lipschitz hD.1
  have hw : ContDiff ℝ ∞ D.w := hD.1.choose_spec.1.2.2.1.1
  obtain ⟨M, hM⟩ := isCompact_Icc.bddAbove_image
    (hw.continuous.norm.continuousOn (s := Icc D.a D.b))
  let W : ℝ := |M| + 1
  have hW : 1 ≤ W := by dsimp only [W]; linarith only [abs_nonneg M]
  have hWpos : 0 < W := zero_lt_one.trans_le hW
  refine ⟨4 * C₀ * W, A, by positivity, hA, fun m => ?_⟩
  have hnegative : NegativeRadialComponent D (C.left m) (C.right m) :=
    ⟨(hgeom.1 m).1, (hgeom.1 m).2.1, (hgeom.1 m).2.2,
      (hgeom.2.1 m).1, (hgeom.2.1 m).2.1, hgeom.2.2.2.1 m⟩
  obtain ⟨_, _, hmargin⟩ := hD.2.2.1.2
  obtain ⟨j, hcell, _⟩ := (hmargin (C.left m) (C.right m) hnegative).2
  have hcore : Icc (C.left m) (C.right m) ⊆ radialCore D := fun r hr =>
    ⟨(hgeom.1 m).1.trans_le hr.1, hr.2.trans_lt (hgeom.1 m).2.2⟩
  obtain ⟨P, hP, hPeq, hPLip⟩ :=
    hLip j (C.left m) (C.right m) (hgeom.1 m).2.1 hcell hcore
  refine ⟨j, hcell, fun right x hx => ?_⟩
  have hsub := n05_cut_physical_closed_subset_component h.2.2.2.2.1 m right
  have hb := n05_cut_reference_density_le_of_optical_lipschitz hT hS h m right hP
    (hPLip.mono hsub) hx
  have hxcore : x.1 ∈ radialCore D := hcore (hsub ⟨hx.1.1.le, hx.1.2.le⟩)
  have hxw : D.w x.1 ≤ W := by
    have hh := hM ⟨x.1, Ioo_subset_Icc_self hxcore, rfl⟩
    have hh' : |D.w x.1| ≤ M := by simpa only [Real.norm_eq_abs] using hh
    dsimp only [W]
    linarith only [le_abs_self (D.w x.1), hh', le_abs_self M]
  have hE : 0 ≤ radialE (D.cellIndex j) ^ A :=
    (Real.rpow_pos_of_pos (Real.exp_pos _) A).le
  constructor
  · calc
      _ ≤ 4 * (P : ℝ) := hb.1
      _ = (4 * C₀) * radialE (D.cellIndex j) ^ A := by rw [hPeq]; ring
      _ ≤ ((4 * C₀) * W) * radialE (D.cellIndex j) ^ A :=
        mul_le_mul_of_nonneg_right
          (by simpa only [mul_one] using
            mul_le_mul_of_nonneg_left hW (by positivity : 0 ≤ 4 * C₀)) hE
  · calc
      _ ≤ 4 * (P : ℝ) * D.w x.1 := hb.2
      _ ≤ 4 * (P : ℝ) * W := mul_le_mul_of_nonneg_left hxw (by positivity)
      _ = ((4 * C₀) * W) * radialE (D.cellIndex j) ^ A := by rw [hPeq]; ring

end ContinuousFlexibility.Statements
