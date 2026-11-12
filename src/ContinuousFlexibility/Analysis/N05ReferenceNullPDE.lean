import ContinuousFlexibility.Analysis.N05NegativeOrientation
import ContinuousFlexibility.Analysis.N05NullOrientationAlgebra
import ContinuousFlexibility.Analysis.OpticalTravelVariation

/-!
# The actual reference null characteristic equations

The true null identities, positive angular derivatives, and inward radial
orientation select opposite characteristic directions.  The speed is the
existing optical speed of the actual reference profile.  Thus no
characteristic equation is added as a hypothesis to the canonical data.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

theorem n05_opticalSpeed_density
    {w : ℝ → ℝ} {r : ℝ} (hr : 0 < r) (hw : 0 < w r) (hd : deriv w r < 0) :
    0 < opticalSpeed w r ∧ w r * opticalSpeed w r ^ 2 = -(deriv w r / r) := by
  have hq : 0 < -deriv w r / (r * w r) :=
    div_pos (neg_pos.mpr hd) (mul_pos hr hw)
  constructor
  · exact Real.sqrt_pos.mpr hq
  · rw [opticalSpeed, Real.sq_sqrt hq.le]
    field_simp [hr.ne', hw.ne'] <;> ring

theorem n05_null_square_of_density
    {a c v nr nt : ℝ} (ha : a ≠ 0) (hv : a * v ^ 2 = -c)
    (hn : a * nr ^ 2 + c * nt ^ 2 = 0) :
    nr ^ 2 = (v * nt) ^ 2 := by
  apply mul_left_cancel₀ ha
  calc
    a * nr ^ 2 = -c * nt ^ 2 := by linarith only [hn]
    _ = (a * v ^ 2) * nt ^ 2 := by rw [hv]
    _ = a * (v * nt) ^ 2 := by ring

theorem n05_null_differential_determinant
    {Ψ : PolarPoint → PolarPoint} {x : PolarPoint}
    (hΨ : DifferentiableAt ℝ Ψ x) (hx : 0 < (Ψ x).1) :
    radialPartial (n05NullCoordinate Ψ 1) x * angularPartial (n05NullCoordinate Ψ (-1)) x -
        angularPartial (n05NullCoordinate Ψ 1) x * radialPartial (n05NullCoordinate Ψ (-1)) x =
      2 * Real.sqrt (Ψ x).1 * planeJacobian Ψ x := by
  have hp := n05NullCoordinate_partials hΨ hx 1
  have hm := n05NullCoordinate_partials hΨ hx (-1)
  rw [hp.1, hp.2, hm.1, hm.2, n05_planeJacobian_eq_partials hΨ]
  ring

theorem n05_null_radial_difference
    {Ψ : PolarPoint → PolarPoint} {x : PolarPoint}
    (hΨ : DifferentiableAt ℝ Ψ x) (hx : 0 < (Ψ x).1) :
    radialPartial (n05NullCoordinate Ψ 1) x - radialPartial (n05NullCoordinate Ψ (-1)) x =
      2 * Real.sqrt (Ψ x).1 * radialPartial (fun p => (Ψ p).1) x := by
  rw [(n05NullCoordinate_partials hΨ hx 1).1,
    (n05NullCoordinate_partials hΨ hx (-1)).1]
  ring

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}

/-- The characteristic equations follow from the actual reference symbols
and an already identified inward orientation. -/
theorem n05_negative_reference_null_PDE
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    {m : ℕ} (hm : K.positive m = false) {x : PolarPoint}
    (hx : x ∈ physicalPieceOpen S K m) {orientation : ℝ}
    (ho : orientation ^ 2 = 1)
    (hξr : 0 < orientation *
      radialPartial (fun p => (K.chart (C.referenceState, 0) m p).1) x) :
    let Ψ := K.chart (C.referenceState, 0) m
    radialPartial (n05NullCoordinate Ψ 1) x =
        orientation * opticalSpeed D.w x.1 * angularPartial (n05NullCoordinate Ψ 1) x ∧
      radialPartial (n05NullCoordinate Ψ (-1)) x =
        -orientation * opticalSpeed D.w x.1 * angularPartial (n05NullCoordinate Ψ (-1)) x := by
  dsimp only
  have h01 := h.1.1.1
  have h04 := h.2.2.2.2
  rcases h04 with ⟨_, _, _, hpieces, _, hnegative, _, _, hclosed, _⟩
  have hxClosed : x.1 ∈ Icc (K.physicalLeft m) (K.physicalRight m) :=
    ⟨hx.1.1.le, hx.1.2.le⟩
  have hxD : x ∈ annularOpen D := ⟨(hpieces m).2.2 hx.1, mem_univ _⟩
  obtain ⟨B, hB⟩ := h01.1.1
  have hw : 0 < D.w x.1 := hB.1.2.2.2.2.1 x.1 hxD.1
  have hr : 0 < x.1 := hB.1.1.trans hxD.1.1
  have hnegativeAt := hnegative m hm x.1 hx.1
  have hpos := n05_negative_reference_radius_pos hT hS h hm hxClosed hxD hnegativeAt
  obtain ⟨hΨ, _, hJ, _⟩ := hclosed (C.referenceState, 0)
    (n05_referenceState_mem h01.2.1) (n05_referenceState_sector h01.2.2.1) m x hxClosed
  have dΨ := hΨ.differentiableAt (by simp)
  obtain ⟨hv, hvdensity⟩ := n05_opticalSpeed_density hr hw hnegativeAt
  have hp := n05_negative_reference_null_identities hT hS h hm hx
    (σ := 1) (by norm_num)
  have hn := n05_negative_reference_null_identities hT hS h hm hx
    (σ := -1) (by norm_num)
  have htp := n05_negative_reference_null_angular_pos hT hS h hm hx
    (σ := 1) (by norm_num)
  have htn := n05_negative_reference_null_angular_pos hT hS h hm hx
    (σ := -1) (by norm_num)
  have hdet : radialPartial (n05NullCoordinate (K.chart (C.referenceState, 0) m) 1) x *
        angularPartial (n05NullCoordinate (K.chart (C.referenceState, 0) m) (-1)) x -
      angularPartial (n05NullCoordinate (K.chart (C.referenceState, 0) m) 1) x *
        radialPartial (n05NullCoordinate (K.chart (C.referenceState, 0) m) (-1)) x ≠ 0 := by
    rw [n05_null_differential_determinant dΨ hpos]
    exact mul_ne_zero (mul_ne_zero (by norm_num) (Real.sqrt_pos.mpr hpos).ne') hJ
  have horder : 0 < orientation *
      (radialPartial (n05NullCoordinate (K.chart (C.referenceState, 0) m) 1) x -
        radialPartial (n05NullCoordinate (K.chart (C.referenceState, 0) m) (-1)) x) := by
    rw [n05_null_radial_difference dΨ hpos]
    have hpositive := mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2)
      (Real.sqrt_pos.mpr hpos)) hξr
    convert hpositive using 1 <;> ring
  have hslopes := n05_oriented_null_slopes hv htp htn ho
    (n05_null_square_of_density hw.ne' hvdensity hp.1)
    (n05_null_square_of_density hw.ne' hvdensity hn.1) hdet horder
  have recover (u v : ℝ) (hu : orientation * u = v) : u = orientation * v := by
    calc
      u = 1 * u := (one_mul u).symm
      _ = orientation ^ 2 * u := by rw [ho]
      _ = orientation * (orientation * u) := by ring
      _ = orientation * v := by rw [hu]
  constructor
  · simpa only [mul_assoc] using recover _ _ hslopes.1
  · simpa only [mul_neg, neg_mul, mul_assoc] using recover _ _ hslopes.2

/-- Each actual cut half satisfies its correct pair of reference
characteristic equations, with one Boolean orientation parameter. -/
theorem n05_cut_reference_null_PDE
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (m : ℕ) (right : Bool) {x : PolarPoint}
    (hx : x ∈ physicalPieceOpen S K
      (if right then (K.cutPair m).2 else (K.cutPair m).1)) :
    let Ψ := K.chart (C.referenceState, 0)
      (if right then (K.cutPair m).2 else (K.cutPair m).1)
    let orientation : ℝ := if right then -1 else 1
    radialPartial (n05NullCoordinate Ψ 1) x =
        orientation * opticalSpeed D.w x.1 * angularPartial (n05NullCoordinate Ψ 1) x ∧
      radialPartial (n05NullCoordinate Ψ (-1)) x =
        -orientation * opticalSpeed D.w x.1 * angularPartial (n05NullCoordinate Ψ (-1)) x := by
  have h04 := h.2.2.2.2
  rcases h04 with ⟨_, _, _, _, _, _, _, _, _, _, _, hcuts, _⟩
  have hnegative : K.positive (if right then (K.cutPair m).2 else (K.cutPair m).1) = false := by
    cases right
    · exact (hcuts m).1
    · exact (hcuts m).2.1
  exact n05_negative_reference_null_PDE hT hS h hnegative hx
    (orientation := if right then (-1 : ℝ) else 1)
    (by cases right <;> norm_num) (n05_cut_reference_radial_orientation hT hS h m right hx)

end ContinuousFlexibility.Statements
