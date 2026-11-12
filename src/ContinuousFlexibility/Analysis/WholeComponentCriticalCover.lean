import ContinuousFlexibility.Analysis.WholeComponentFieldSelection
import ContinuousFlexibility.Analysis.PositiveComponentAdjacency

/-!
# Whole components cover every physical radius

A simple critical point has negative values on one of its two sides.
The actual negative-component cover supplies the adjacent component;
the absence of other nearby zeros forces the original critical point
to be one of that component's true endpoints. Thus closed negative
components and open positive components cover the whole annulus.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

variable {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}

theorem n04_criticalRadius_mem_negativeClosed
    (hD : RadialProfileGeometry D) (hC : controlGeometryConditions D S C)
    {c : ℝ} (hc : c ∈ radialCore D) (hz : deriv D.w c = 0) :
    ∃ m : ℕ, c ∈ Icc (C.left m) (C.right m) := by
  have hf : ContDiff ℝ ∞ (deriv D.w) :=
    (contDiff_infty_iff_deriv.mp hD.2.2.1.1).2
  let A : ℝ := deriv (deriv D.w) c
  have hA : A ≠ 0 := hD.2.2.2.2.2.2 c hc hz
  obtain ⟨δ, hδ, hsign⟩ := n04_simple_zero_sign_near
    (hf.differentiable (by simp) c).hasDerivAt hz hA
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
    dsimp only [η] at hη ⊢
    linarith
  have hηb : η < D.b - c := by
    have h := (min_le_right δ (min (c - D.a) (D.b - c))).trans
      (min_le_right (c - D.a) (D.b - c))
    dsimp only [η] at hη ⊢
    linarith
  let x : ℝ := if 0 < A then c - η else c + η
  have hxcore : x ∈ radialCore D := by
    dsimp only [x]
    split_ifs <;> constructor <;> linarith [hc.1, hc.2]
  have hxdist : |x - c| < δ := by
    apply abs_lt.mpr
    dsimp only [x]
    split_ifs <;> constructor <;> linarith
  have hxne : x ≠ c := by
    dsimp only [x]
    split_ifs <;> linarith
  have hxprod : A * (x - c) < 0 := by
    dsimp only [x]
    split_ifs with hpos
    · exact mul_neg_of_pos_of_neg hpos (by linarith)
    · exact mul_neg_of_neg_of_pos (lt_of_le_of_ne (le_of_not_gt hpos) hA)
        (by linarith)
  have hxneg : deriv D.w x < 0 := by
    rcases hsign x hxdist hxne with hp | hn
    · exact (not_lt_of_ge hp.2.le hxprod).elim
    · exact hn.1
  have hne (y : ℝ) (hy : |y - c| < δ) (hyc : y ≠ c) : deriv D.w y ≠ 0 := by
    rcases hsign y hy hyc with hp | hn
    · exact hp.1.ne'
    · exact hn.1.ne
  obtain ⟨m, hm⟩ := hC.2.2.2.2.1 x hxcore hxneg
  refine ⟨m, ?_, ?_⟩
  · by_contra h
    have hcl : c < C.left m := lt_of_not_ge h
    have hd : |C.left m - c| < δ :=
      abs_lt.mpr ⟨by linarith, by linarith [(abs_lt.mp hxdist).2, hm.1]⟩
    exact hne (C.left m) hd hcl.ne' (hC.2.1 m).1
  · by_contra h
    have hrc : C.right m < c := lt_of_not_ge h
    have hd : |C.right m - c| < δ :=
      abs_lt.mpr ⟨by linarith [(abs_lt.mp hxdist).1, hm.2], by linarith⟩
    exact hne (C.right m) hd hrc.ne (hC.2.1 m).2.1

theorem n04_wholeComponent_cover
    (hD : RadialProfileGeometry D) (hC : controlGeometryConditions D S C)
    {r : ℝ} (hr : r ∈ radialCore D) :
    (∃ m : ℕ, r ∈ Icc (C.left m) (C.right m)) ∨
      ∃ i : N04PositiveComponent D.a D.b (deriv D.w),
        r ∈ Ioo (n04PositiveLeft i) (n04PositiveRight i) := by
  rcases lt_trichotomy (deriv D.w r) 0 with hn | hz | hp
  · obtain ⟨m, hm⟩ := hC.2.2.2.2.1 r hr hn
    exact Or.inl ⟨m, hm.1.le, hm.2.le⟩
  · exact Or.inl (n04_criticalRadius_mem_negativeClosed hD hC hr hz)
  · have hf : Continuous (deriv D.w) := hD.2.2.1.1.continuous_deriv (by simp)
    obtain ⟨i, hi, _⟩ := (n04PositiveComponent_existsUnique_interval_iff hf r).mpr ⟨hr, hp⟩
    exact Or.inr ⟨i, hi⟩

end ContinuousFlexibility.Analysis
