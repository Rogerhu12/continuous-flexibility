import ContinuousFlexibility.Analysis.WholeComponentCriticalCover

/-!
# The positive neighbor of each actual negative root

The actual second-derivative sign determines the positive side of each
negative endpoint. Taking the genuine positive connected component on
that side forces its endpoint to be exactly the original root. This
supplies the local two-piece geometry needed for finite jet gluing.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

theorem n04NegativeEndpoint_exists_positive_neighbor
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε) (m : ℕ) (side : Bool) :
    ∃ i : N04PositiveComponent D.a D.b (deriv D.w),
      n04PositiveEndpoint i (!side) = (if side then C.right m else C.left m) := by
  have hD : RadialProfileGeometry D := (Classical.choose_spec hN.1.1).1
  have hC : controlGeometryConditions D S C := hN.2.2.2.1
  have hf : ContDiff ℝ ∞ (deriv D.w) :=
    (contDiff_infty_iff_deriv.mp hD.2.2.1.1).2
  let c : ℝ := if side then C.right m else C.left m
  let A : ℝ := deriv (deriv D.w) c
  have hc : c ∈ radialCore D := by
    have hb := hC.1 m
    cases side
    · exact ⟨hb.1, hb.2.1.trans hb.2.2⟩
    · exact ⟨hb.1.trans hb.2.1, hb.2.2⟩
  have hz : deriv D.w c = 0 := by
    cases side
    · exact (hC.2.1 m).1
    · exact (hC.2.1 m).2.1
  have hA : A ≠ 0 := hD.2.2.2.2.2.2 c hc hz
  have horient : if side then 0 < A else A < 0 := by
    have ho := n04b_component_root_orientations hN m
    cases side
    · exact ho.1
    · exact ho.2
  obtain ⟨δ, hδ, hsign⟩ := n04_simple_zero_sign_near
    (hf.differentiable (by simp) c).hasDerivAt hz hA
  have hpositive (y : ℝ) (hy : |y - c| < δ)
      (hout : if side then c < y else y < c) : 0 < deriv D.w y := by
    have hyne : y ≠ c := by
      cases side
      · exact ne_of_lt hout
      · exact (ne_of_lt hout).symm
    have hprod : 0 < A * (y - c) := by
      cases side
      · exact mul_pos_of_neg_of_neg horient (sub_neg.mpr hout)
      · exact mul_pos horient (sub_pos.mpr hout)
    rcases hsign y hy hyne with hp | hn
    · exact hp.1
    · exact (not_lt_of_ge hprod.le hn.2).elim
  let η : ℝ := min δ (min (c - D.a) (D.b - c)) / 2
  have hη : 0 < η := half_pos
    (lt_min hδ (lt_min (sub_pos.mpr hc.1) (sub_pos.mpr hc.2)))
  have hηδ : η < δ := by
    have h := min_le_left δ (min (c - D.a) (D.b - c))
    dsimp only [η]
    linarith
  have hηa : η < c - D.a := by
    have h := (min_le_right δ (min (c - D.a) (D.b - c))).trans
      (min_le_left (c - D.a) (D.b - c))
    dsimp only [η]
    linarith
  have hηb : η < D.b - c := by
    have h := (min_le_right δ (min (c - D.a) (D.b - c))).trans
      (min_le_right (c - D.a) (D.b - c))
    dsimp only [η]
    linarith
  let x : ℝ := if side then c + η else c - η
  have hxcore : x ∈ radialCore D := by
    cases side <;> dsimp only [x, Bool.false_eq_true, ite_false, ite_true] <;>
      constructor <;> linarith [hc.1, hc.2]
  have hxdist : |x - c| < δ := by
    apply abs_lt.mpr
    cases side <;> dsimp only [x, Bool.false_eq_true, ite_false, ite_true] <;>
      constructor <;> linarith
  have hxout : if side then c < x else x < c := by
    cases side <;> dsimp only [x, Bool.false_eq_true, ite_false, ite_true] <;> linarith
  obtain ⟨i, hi, _⟩ := (n04PositiveComponent_existsUnique_interval_iff hf.continuous x).mpr
    ⟨hxcore, hpositive x hxdist hxout⟩
  refine ⟨i, ?_⟩
  have hendpoint := n04PositiveEndpoint_ambient_or_zero hf.continuous i (!side)
  cases side
  · change n04PositiveRight i = c
    change x < c at hxout
    have hle : n04PositiveRight i ≤ c := by
      by_contra h
      have hp := n04PositiveComponent_interval_pos hf.continuous i
        (show c ∈ Ioo (n04PositiveLeft i) (n04PositiveRight i) from
          ⟨hi.1.trans hxout, lt_of_not_ge h⟩)
      exact hp.ne' hz
    have hge : c ≤ n04PositiveRight i := by
      by_contra h
      have hrc : n04PositiveRight i < c := lt_of_not_ge h
      have hd : |n04PositiveRight i - c| < δ :=
        abs_lt.mpr ⟨by linarith [(abs_lt.mp hxdist).1, hi.2], by linarith⟩
      have hp := hpositive (n04PositiveRight i) hd hrc
      rcases hendpoint with he | he
      · change n04PositiveRight i = D.b at he
        linarith [hc.2]
      · exact hp.ne' he.2
    exact le_antisymm hle hge
  · change n04PositiveLeft i = c
    change c < x at hxout
    have hge : c ≤ n04PositiveLeft i := by
      by_contra h
      have hp := n04PositiveComponent_interval_pos hf.continuous i
        (show c ∈ Ioo (n04PositiveLeft i) (n04PositiveRight i) from
          ⟨lt_of_not_ge h, hxout.trans hi.2⟩)
      exact hp.ne' hz
    have hle : n04PositiveLeft i ≤ c := by
      by_contra h
      have hcl : c < n04PositiveLeft i := lt_of_not_ge h
      have hd : |n04PositiveLeft i - c| < δ :=
        abs_lt.mpr ⟨by linarith, by linarith [(abs_lt.mp hxdist).2, hi.1]⟩
      have hp := hpositive (n04PositiveLeft i) hd hcl
      rcases hendpoint with he | he
      · change n04PositiveLeft i = D.a at he
        linarith [hc.1]
      · exact hp.ne' he.2
    exact le_antisymm hle hge

end ContinuousFlexibility.Analysis
