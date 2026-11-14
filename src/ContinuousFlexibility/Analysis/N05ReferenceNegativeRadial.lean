module

public import ContinuousFlexibility.Analysis.N05CanonicalGeometryAccess
public import ContinuousFlexibility.Analysis.N05RootAngularRigidity
public import ContinuousFlexibility.Analysis.N05NegativePieceEnumeration

/-!
# The actual negative reference chart is radial

Substitution of the identified root chart into the actual characteristic
transport determines both null coordinates.  Their sum gives the physical
angle, and their difference gives the radial optical time.  Strict
monotonicity of Tricomi time on the nonnegative canonical radius then makes
the first chart coordinate independent of the angle, including endpoints.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

theorem n05TricomiTime_strictMonoOn : StrictMonoOn n05TricomiTime (Ici 0) := by
  intro x hx y hy hxy
  have hs : Real.sqrt x ≤ Real.sqrt y := Real.sqrt_le_sqrt hxy.le
  have hsy : 0 < Real.sqrt y := Real.sqrt_pos.mpr (hx.trans_lt hxy)
  have hmul : x * Real.sqrt x < y * Real.sqrt y :=
    (mul_le_mul_of_nonneg_left hs hx).trans_lt (mul_lt_mul_of_pos_right hxy hsy)
  have hpositive := mul_lt_mul_of_pos_left hmul (by norm_num : (0 : ℝ) < 2 / 3)
  simpa only [n05TricomiTime, mul_assoc] using hpositive

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}

/-- The actual chart maps the closure of its current physical domain into
the closed canonical interval, as recorded by the genuine boundary map. -/
theorem n05_chart_physical_closed_range
    (h04 : N04Properties D T S C L K base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) {m : ℕ} {x : PolarPoint}
    (hx : x ∈ physicalPieceClosed S K z m) :
    (K.chart z m x).1 ∈ Icc (K.left m) (K.right m) := by
  exact ((h04.1.boundary z hz hs m).1 hx).1

theorem n05_reference_chart_physical_closed_range
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hs : stateSector S C.referenceState) {m : ℕ} {x : PolarPoint}
    (hx : x.1 ∈ Icc (K.physicalLeft m) (K.physicalRight m)) :
    (K.chart (C.referenceState, 0) m x).1 ∈ Icc (K.left m) (K.right m) := by
  apply n05_chart_physical_closed_range h04 hz hs
  rw [n05_reference_physicalClosed_eq h04 m]
  exact ⟨hx, mem_univ _⟩

theorem n05_cut_reference_closed_radius_nonneg
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (m : ℕ) (right : Bool) {r : ℝ}
    (hr : r ∈ Icc
      (K.physicalLeft (if right then (K.cutPair m).2 else (K.cutPair m).1))
      (K.physicalRight (if right then (K.cutPair m).2 else (K.cutPair m).1))) (θ : ℝ) :
    0 ≤ (K.chart (C.referenceState, 0)
      (if right then (K.cutPair m).2 else (K.cutPair m).1) (r, θ)).1 := by
  have h04 := h.2.2.2.2.1
  have hcuts := h04.2.1.1.1
  obtain ⟨_, _, _, _, _, _, hzeroL, hzeroR, _⟩ := hcuts m
  have hzero : K.left (if right then (K.cutPair m).2 else (K.cutPair m).1) = 0 := by
    cases right
    · exact hzeroL
    · exact hzeroR
  have himage := n05_reference_chart_physical_closed_range h.2.2.2.2.1
    (n05_referenceState_mem h.1.1.1.2.1) (n05_referenceState_sector h.1.1.1.2.2.1)
    (x := (r, θ)) hr
  simpa only [hzero] using himage.1

/-- Both actual null coordinates equal their explicit optical translations
of the physical angle on the whole closed half. -/
theorem n05_cut_reference_null_formula
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (m : ℕ) (right : Bool) {σ : ℝ} (hσ : σ ^ 2 = 1) {r : ℝ}
    (hr : r ∈ Icc
      (K.physicalLeft (if right then (K.cutPair m).2 else (K.cutPair m).1))
      (K.physicalRight (if right then (K.cutPair m).2 else (K.cutPair m).1))) (θ : ℝ) :
    let i := if right then (K.cutPair m).2 else (K.cutPair m).1
    let root := if right then C.right m else C.left m
    let orientation : ℝ := if right then -1 else 1
    n05NullCoordinate (K.chart (C.referenceState, 0) i) σ (r, θ) =
      θ + σ * (orientation * (opticalTravel D.w (K.physicalLeft i) r -
        opticalTravel D.w (K.physicalLeft i) root)) := by
  let i := if right then (K.cutPair m).2 else (K.cutPair m).1
  let root := if right then C.right m else C.left m
  let orientation : ℝ := if right then -1 else 1
  let Ψ := K.chart (C.referenceState, 0) i
  let angle := θ + (σ * orientation) * opticalTravel D.w (K.physicalLeft i) r -
    (σ * orientation) * opticalTravel D.w (K.physicalLeft i) root
  have ht : n05NullCoordinate Ψ σ (r, θ) = n05NullCoordinate Ψ σ (root, angle) :=
    n05_cut_reference_null_transport hT hS h m right hσ hr
      (n05_cut_physical_root_mem h.2.2.2.2.1 m right) θ
  have hroot : Ψ (root, angle) = (0, angle) :=
    n05_cut_reference_root_chart hT hS h m right angle
  calc
    _ = n05NullCoordinate Ψ σ (root, angle) := ht
    _ = angle := by
      simp only [n05NullCoordinate, hroot, n05TricomiTime_zero, mul_zero, add_zero]
    _ = _ := by dsimp only [angle]; ring

theorem n05_cut_reference_angle_and_time
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (m : ℕ) (right : Bool) {r : ℝ}
    (hr : r ∈ Icc
      (K.physicalLeft (if right then (K.cutPair m).2 else (K.cutPair m).1))
      (K.physicalRight (if right then (K.cutPair m).2 else (K.cutPair m).1))) (θ : ℝ) :
    let i := if right then (K.cutPair m).2 else (K.cutPair m).1
    let root := if right then C.right m else C.left m
    let orientation : ℝ := if right then -1 else 1
    (K.chart (C.referenceState, 0) i (r, θ)).2 = θ ∧
      n05TricomiTime (K.chart (C.referenceState, 0) i (r, θ)).1 =
        orientation * (opticalTravel D.w (K.physicalLeft i) r -
          opticalTravel D.w (K.physicalLeft i) root) := by
  have hp := n05_cut_reference_null_formula hT hS h m right
    (σ := 1) (by norm_num) hr θ
  have hn := n05_cut_reference_null_formula hT hS h m right
    (σ := -1) (by norm_num) hr θ
  dsimp only [n05NullCoordinate] at hp hn ⊢
  constructor <;> linarith only [hp, hn]

theorem n05_cut_reference_chart_radial
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (m : ℕ) (right : Bool) {r : ℝ}
    (hr : r ∈ Icc
      (K.physicalLeft (if right then (K.cutPair m).2 else (K.cutPair m).1))
      (K.physicalRight (if right then (K.cutPair m).2 else (K.cutPair m).1))) (θ : ℝ) :
    let i := if right then (K.cutPair m).2 else (K.cutPair m).1
    K.chart (C.referenceState, 0) i (r, θ) =
      ((K.chart (C.referenceState, 0) i (r, 0)).1, θ) := by
  have hθ := n05_cut_reference_angle_and_time hT hS h m right hr θ
  have hzero := n05_cut_reference_angle_and_time hT hS h m right hr 0
  apply Prod.ext
  · exact n05TricomiTime_strictMonoOn.injOn
      (n05_cut_reference_closed_radius_nonneg h m right hr θ)
      (n05_cut_reference_closed_radius_nonneg h m right hr 0) (hθ.2.trans hzero.2.symm)
  · exact hθ.1

/-- Every actual negative piece is one of the named cut halves, so the
same radial reference chart identity holds for the complete negative atlas. -/
theorem n05_negative_reference_chart_radial
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    {i : ℕ} (hi : K.positive i = false) {r : ℝ}
    (hr : r ∈ Icc (K.physicalLeft i) (K.physicalRight i)) (θ : ℝ) :
    K.chart (C.referenceState, 0) i (r, θ) =
      ((K.chart (C.referenceState, 0) i (r, 0)).1, θ) := by
  obtain ⟨m, hm⟩ := n05_negative_piece_is_cut_half h.1.1.1.2.2.2.1 h.2.2.2.2.1 hi
  rcases hm with rfl | rfl
  · exact n05_cut_reference_chart_radial hT hS h m false hr θ
  · exact n05_cut_reference_chart_radial hT hS h m true hr θ

end ContinuousFlexibility.Statements
