import ContinuousFlexibility.Analysis.PositiveComponentEndpoints
import ContinuousFlexibility.Statements.Nonlinear
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# The actual negative neighbor of an interior positive endpoint

The derivative at a simple zero fixes the sign on its two sides. The
negative-component cover then supplies a genuine adjacent component;
its zero endpoint must be the original positive endpoint. Both ends
are handled by the same Boolean statement. Ambient endpoints remain
the separate identity case.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

theorem n04_simple_zero_sign_near {f : ℝ → ℝ} {c A : ℝ}
    (hf : HasDerivAt f A c) (hz : f c = 0) (hA : A ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x, |x - c| < δ → x ≠ c →
      (0 < f x ∧ 0 < A * (x - c)) ∨ (f x < 0 ∧ A * (x - c) < 0) := by
  have ht : Tendsto (fun x => slope f c x / A) (𝓝[≠] c) (𝓝 1) := by
    simpa only [div_self hA] using hf.tendsto_slope.div_const A
  have hnear : ∀ᶠ x in 𝓝 c, x ≠ c → 0 < slope f c x / A := by
    simpa only [mem_compl_iff, mem_singleton_iff, mem_Ioi] using
      (eventually_nhdsWithin_iff.mp (ht (Ioi_mem_nhds (zero_lt_one : (0 : ℝ) < 1))))
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨δ, hδ, ?_⟩
  intro x hx hxc
  have hp := hball (by simpa only [Metric.mem_ball, Real.dist_eq] using hx) hxc
  apply div_pos_iff.mp
  simpa only [slope_def_field, hz, sub_zero, div_div, mul_comm] using hp

private theorem n04_positive_interval_negative_side {f : ℝ → ℝ} {l r A : ℝ}
    (hlr : l < r) (side : Bool)
    (hf : HasDerivAt f A (if side then r else l))
    (hz : f (if side then r else l) = 0) (hA : A ≠ 0)
    (hpositive : ∀ x ∈ Ioo l r, 0 < f x) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x, |x - (if side then r else l)| < δ →
      (if side then r < x else x < l) → f x < 0 := by
  obtain ⟨δ, hδ, hsign⟩ := n04_simple_zero_sign_near hf hz hA
  let ε : ℝ := min δ (r - l) / 2
  have hε : 0 < ε := half_pos (lt_min hδ (sub_pos.mpr hlr))
  have hεδ : ε < δ := by
    have h := min_le_left δ (r - l)
    dsimp only [ε]
    linarith
  have hεgap : ε < r - l := by
    have h := min_le_right δ (r - l)
    dsimp only [ε]
    linarith
  let y : ℝ := if side then r - ε else l + ε
  have hy : y ∈ Ioo l r := by
    cases side <;> simp only [y, Bool.false_eq_true, ↓reduceIte] <;>
      constructor <;> linarith
  have hyδ : |y - (if side then r else l)| < δ := by
    apply abs_lt.mpr
    cases side <;> simp only [y, Bool.false_eq_true, ↓reduceIte] <;>
      constructor <;> linarith
  have hyne : y ≠ (if side then r else l) := by
    cases side <;> simp only [y, Bool.false_eq_true, ↓reduceIte] <;> linarith
  have hprod : 0 < A * (y - (if side then r else l)) := by
    rcases hsign y hyδ hyne with hp | hn
    · exact hp.2
    · exact (not_lt_of_ge (hpositive y hy).le hn.1).elim
  have horient : if side then A < 0 else 0 < A := by
    cases side
    · change 0 < A
      simp only [y, Bool.false_eq_true, ↓reduceIte] at hprod
      by_contra hnon
      have hm := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hnon) hε.le
      nlinarith
    · change A < 0
      simp only [y, ↓reduceIte] at hprod
      by_contra hnon
      have hm := mul_nonneg (le_of_not_gt hnon) hε.le
      nlinarith
  refine ⟨δ, hδ, ?_⟩
  intro x hx hout
  have hxc : x ≠ (if side then r else l) := by
    cases side <;> simp only [Bool.false_eq_true, ↓reduceIte] at hout ⊢ <;> linarith
  have hnegative : A * (x - (if side then r else l)) < 0 := by
    cases side
    · exact mul_neg_of_pos_of_neg horient (sub_neg.mpr hout)
    · exact mul_neg_of_neg_of_pos horient (sub_pos.mpr hout)
  rcases hsign x hx hxc with hp | hn
  · exact (not_lt_of_ge hp.2.le hnegative).elim
  · exact hn.1

theorem n04PositiveEndpoint_exists_negative_neighbor
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    (hD : RadialProfileGeometry D) (hC : controlGeometryConditions D S C)
    (i : N04PositiveComponent D.a D.b (deriv D.w)) (side : Bool)
    (hinterior : n04PositiveEndpoint i side ≠ (if side then D.b else D.a)) :
    ∃ m : ℕ, n04PositiveEndpoint i side = (if side then C.left m else C.right m) := by
  have hf : ContDiff ℝ ∞ (deriv D.w) :=
    (contDiff_infty_iff_deriv.mp hD.2.2.1.1).2
  rcases n04PositiveEndpoint_ambient_or_simple_root hD i side with hamb | ⟨hc, hz, hsimple⟩
  · exact (hinterior hamb).elim
  obtain ⟨δ, hδ, hneg⟩ := n04_positive_interval_negative_side
    (n04PositiveComponent_bounds hf.continuous i).2.1 side
    (hf.differentiable (by simp) _).hasDerivAt hz hsimple
    (fun x hx => n04PositiveComponent_interval_pos hf.continuous i hx)
  let c : ℝ := n04PositiveEndpoint i side
  have hnegc : ∀ x, |x - c| < δ → (if side then c < x else x < c) →
      deriv D.w x < 0 := by
    cases side <;>
      simpa only [c, n04PositiveEndpoint, Bool.false_eq_true, ↓reduceIte] using hneg
  let ε : ℝ := min δ (min (c - D.a) (D.b - c)) / 2
  have hε : 0 < ε := half_pos (lt_min hδ
    (lt_min (sub_pos.mpr hc.1) (sub_pos.mpr hc.2)))
  have hεδ : ε < δ := by
    have h := min_le_left δ (min (c - D.a) (D.b - c))
    dsimp only [ε]
    linarith
  have hεa : ε < c - D.a := by
    have h := (min_le_right δ (min (c - D.a) (D.b - c))).trans
      (min_le_left (c - D.a) (D.b - c))
    dsimp only [ε] at hε ⊢
    linarith
  have hεb : ε < D.b - c := by
    have h := (min_le_right δ (min (c - D.a) (D.b - c))).trans
      (min_le_right (c - D.a) (D.b - c))
    dsimp only [ε] at hε ⊢
    linarith
  let x : ℝ := if side then c + ε else c - ε
  have hx : x ∈ Ioo D.a D.b := by
    cases side <;> simp only [x, Bool.false_eq_true, ↓reduceIte] <;>
      constructor <;> linarith [hc.1, hc.2]
  have hxδ : |x - c| < δ := by
    apply abs_lt.mpr
    cases side <;> simp only [x, Bool.false_eq_true, ↓reduceIte] <;>
      constructor <;> linarith
  have hxlower : -δ < x - c := (abs_lt.mp hxδ).1
  have hxupper : x - c < δ := (abs_lt.mp hxδ).2
  have hout : if side then c < x else x < c := by
    cases side <;> simp only [x, Bool.false_eq_true, ↓reduceIte] <;> linarith
  have hxneg : deriv D.w x < 0 := hnegc x hxδ hout
  obtain ⟨m, hm⟩ := hC.2.2.2.2.1 x hx hxneg
  refine ⟨m, ?_⟩
  cases side
  · change c = C.right m
    change x < c at hout
    have hR : C.right m ≤ c := by
      by_contra h
      have hbad := hC.2.2.2.1 m c ⟨hm.1.trans hout, lt_of_not_ge h⟩
      exact (ne_of_lt hbad) hz
    have hcR : c ≤ C.right m := by
      by_contra h
      have hRc : C.right m < c := lt_of_not_ge h
      have hd : |C.right m - c| < δ := abs_lt.mpr ⟨by linarith [hm.2], by linarith⟩
      have hbad := hnegc (C.right m) hd hRc
      exact (ne_of_lt hbad) (hC.2.1 m).2.1
    exact le_antisymm hcR hR
  · change c = C.left m
    change c < x at hout
    have hL : c ≤ C.left m := by
      by_contra h
      have hbad := hC.2.2.2.1 m c ⟨lt_of_not_ge h, hout.trans hm.2⟩
      exact (ne_of_lt hbad) hz
    have hLc : C.left m ≤ c := by
      by_contra h
      have hcL : c < C.left m := lt_of_not_ge h
      have hd : |C.left m - c| < δ := abs_lt.mpr ⟨by linarith, by linarith [hm.1]⟩
      have hbad := hnegc (C.left m) hd hcL
      exact (ne_of_lt hbad) (hC.2.1 m).1
    exact le_antisymm hL hLc

end ContinuousFlexibility.Analysis
