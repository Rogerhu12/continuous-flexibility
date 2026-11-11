import ContinuousFlexibility.Radial.R07RadialUniqueness
import ContinuousFlexibility.Radial.R07DeepTailBridge
import ContinuousFlexibility.Radial.MorseChainLocalGluing

/-!
# Continuing a natural tail to an earlier matching radius

For a fixed frequency, the deep-tail theorem may be applied arbitrarily far
out. The smooth physical solution is then continued through a finite radial
interval. A cut inside an overlap of the two actual solutions gives a smooth
global representative and preserves its nonzero tail witness.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter Real
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

/-- Equality on a genuine overlap determines the Cauchy data at the earlier
end of the old tail, even though its arbitrary inward extension need not
agree on a full neighborhood there. -/
theorem radialNaturalTail_overlap_cauchy {D : ReferenceData}
    (hD : RadialProfileGeometry D) {right : Bool} {j : ℕ} {e f g : ℝ}
    (he : e ∈ radialCore D) (hf : f ∈ radialCore D)
    (hef : if right then e < f else f < e)
    (hg : g ∈ radialTailInterval D right f)
    {u v : ℝ → ℝ} (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (hU : RadialNaturalTail D right j e u) (hV : RadialNaturalTail D right j f v)
    (hmatch : u =ᶠ[𝓝 g] v) : u f = v f ∧ deriv u f = deriv v f := by
  have hgCore : g ∈ radialCore D := by
    cases right
    · exact ⟨hg.1, hg.2.trans hf.2⟩
    · exact ⟨hf.1.trans hg.1, hg.2⟩
  have hfg : f ≠ g := by
    cases right
    · exact ne_of_gt hg.2
    · exact ne_of_lt hg.1
  have hlen : min f g < max f g := min_lt_max.mpr hfg
  have hleft : D.a < min f g := lt_min hf.1 hgCore.1
  have hright : max f g < D.b := max_lt hf.2 hgCore.2
  have hfI : f ∈ Icc (min f g) (max f g) := ⟨min_le_left _ _, le_max_left _ _⟩
  have hgI : g ∈ Icc (min f g) (max f g) := ⟨min_le_right _ _, le_max_right _ _⟩
  have huEq : ∀ x ∈ Icc (min f g) (max f g), radialJacobi ((j : ℝ) ^ 2) D.w u x = 0 := by
    intro x hx
    apply hU.2.1.2 x
    cases right
    · rw [min_eq_right hg.2.le, max_eq_left hg.2.le] at hx
      exact ⟨hgCore.1.trans_le hx.1, hx.2.trans_lt hef⟩
    · rw [min_eq_left hg.1.le, max_eq_right hg.1.le] at hx
      exact ⟨hef.trans_le hx.1, hx.2.trans_lt hgCore.2⟩
  have hvEq : ∀ x ∈ Icc (min f g) (max f g), radialJacobi ((j : ℝ) ^ 2) D.w v x = 0 := by
    apply radialJacobi_zero_on_Icc hD.2.2.1.1 hv (hD.1.trans hleft) hlen
    intro x hx
    apply hV.2.1.2 x
    cases right
    · rw [min_eq_right hg.2.le, max_eq_left hg.2.le] at hx
      exact ⟨hgCore.1.trans hx.1, hx.2⟩
    · rw [min_eq_left hg.1.le, max_eq_right hg.1.le] at hx
      exact ⟨hx.1, hx.2.trans hgCore.2⟩
  have hEq := radialHomogeneous_eqOn_Icc hD hleft hlen.le hright hgI hu hv huEq hvEq
    hmatch.eq_of_nhds hmatch.deriv_eq
  have hder := derivWithin_congr hEq (hEq hfI)
  rw [(hu.differentiable (by simp) f).derivWithin (uniqueDiffOn_Icc hlen f hfI),
    (hv.differentiable (by simp) f).derivWithin (uniqueDiffOn_Icc hlen f hfI)] at hder
  exact ⟨hEq hfI, hder⟩

theorem exists_radialNaturalTail_continuation_with_cauchy {D : ReferenceData}
    (hD : RadialProfileGeometry D) {right : Bool} {j : ℕ} {e f : ℝ}
    (he : e ∈ radialCore D) (hf : f ∈ radialCore D)
    (hef : if right then e < f else f < e)
    {v : ℝ → ℝ} (hv : ContDiff ℝ ∞ v) (hN : RadialNaturalTail D right j f v) :
    ∃ u : ℝ → ℝ, ContDiff ℝ ∞ u ∧ RadialNaturalTail D right j e u ∧
      u f = v f ∧ deriv u f = deriv v f := by
  obtain ⟨r, hr, hvr⟩ := hN.2.2.2
  let g : ℝ := (f + r) / 2
  have hg : g ∈ radialTailInterval D right f := by
    cases right
    · change D.a < g ∧ g < f
      change D.a < r ∧ r < f at hr
      dsimp only [g]
      constructor <;> linarith only [hr.1, hr.2, hf.1]
    · change f < g ∧ g < D.b
      change f < r ∧ r < D.b at hr
      dsimp only [g]
      constructor <;> linarith only [hr.1, hr.2, hf.2]
  have hgr : if right then g < r else r < g := by
    cases right
    · change r < (f + r) / 2
      change D.a < r ∧ r < f at hr
      linarith only [hr.2]
    · change (f + r) / 2 < r
      change f < r ∧ r < D.b at hr
      linarith only [hr.1]
  have hopen : IsOpen (radialTailInterval D right f) := by cases right <;> exact isOpen_Ioo
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen g hg
  let a := g - ε / 2
  let b := g + ε / 2
  have hag : a < g := by dsimp only [a]; linarith only [hε]
  have hgb : g < b := by dsimp only [b]; linarith only [hε]
  have hab : a ≤ b := hag.le.trans hgb.le
  have hsub : Icc a b ⊆ radialTailInterval D right f := by
    intro x hx
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    dsimp only [a, b] at hx
    constructor <;> linarith only [hx.1, hx.2, hε]
  have htailCore : radialTailInterval D right f ⊆ radialCore D := by
    intro x hx
    cases right
    · exact ⟨hx.1, hx.2.trans hf.2⟩
    · exact ⟨hf.1.trans hx.1, hx.2⟩
  have ha : a ∈ radialCore D := htailCore (hsub (left_mem_Icc.mpr hab))
  have hb : b ∈ radialCore D := htailCore (hsub (right_mem_Icc.mpr hab))
  let l := min e a
  let h := max e b
  have hl : D.a < l := lt_min he.1 ha.1
  have hh : h < D.b := max_lt he.2 hb.2
  obtain ⟨z, hz, hzeq, hzv⟩ := exists_radialSolution_matching_germ hD hl hh
    (min_le_right e a) hag hgb (le_max_right e b) hv
    (fun x hx => hN.2.1.2 x (hsub hx))
  let u : ℝ → ℝ := if right then morseGlueCut g z v else morseGlueCut g v z
  have hu : ContDiff ℝ ∞ u := by
    cases right
    · exact contDiff_morseGlueCut hv hz hzv.symm
    · exact contDiff_morseGlueCut hz hv hzv
  have houter (x : ℝ) (hx : if right then g ≤ x else x ≤ g) : u =ᶠ[𝓝 x] v := by
    cases right
    · exact morseGlueCut_eventually_left hzv.symm hx
    · exact morseGlueCut_eventually_right hzv hx
  have hinner (x : ℝ) (hx : if right then x ≤ g else g ≤ x) : u =ᶠ[𝓝 x] z := by
    cases right
    · exact morseGlueCut_eventually_right hzv.symm hx
    · exact morseGlueCut_eventually_left hzv hx
  have heq : ∀ x ∈ radialTailInterval D right e, radialJacobi ((j : ℝ) ^ 2) D.w u x = 0 := by
    intro x hx
    by_cases hout : if right then g ≤ x else x ≤ g
    · have hxe : x ∈ radialTailInterval D right f := by
        cases right
        · exact ⟨hx.1, hout.trans_lt hg.2⟩
        · exact ⟨hg.1.trans_le hout, hx.2⟩
      have he := houter x hout
      unfold radialJacobi
      have hd : (fun t => D.w t * deriv u t) =ᶠ[𝓝 x] fun t => D.w t * deriv v t := by
        filter_upwards [he.deriv] with t ht
        rw [ht]
      rw [hd.deriv_eq, he.eq_of_nhds]
      exact hN.2.1.2 x hxe
    · have hin : if right then x ≤ g else g ≤ x := by
        cases right <;> exact (le_of_not_ge hout)
      have hxI : x ∈ Icc l h := by
        cases right
        · exact ⟨(min_le_right e a).trans (hag.le.trans hin), hx.2.le.trans (le_max_left e b)⟩
        · exact ⟨(min_le_left e a).trans hx.1.le, hin.trans (hgb.le.trans (le_max_right e b))⟩
      have he := hinner x hin
      unfold radialJacobi
      have hd : (fun t => D.w t * deriv u t) =ᶠ[𝓝 x] fun t => D.w t * deriv z t := by
        filter_upwards [he.deriv] with t ht
        rw [ht]
      rw [hd.deriv_eq, he.eq_of_nhds]
      exact hzeq x hxI
  have hrE : r ∈ radialTailInterval D right e := by
    cases right
    · exact ⟨hr.1, hr.2.trans hef⟩
    · exact ⟨hef.trans hr.1, hr.2⟩
  have huR : u r = v r := (houter r (by cases right <;> exact hgr.le)).eq_of_nhds
  have hNu : RadialNaturalTail D right j e u := by
    refine ⟨hu.contDiffAt, ⟨hu.contDiffOn, heq⟩, ?_, r, hrE, ?_⟩
    · exact (r07_memLp_radialHilbertMeasure hD.1 hD.2.2.1.1.continuous hu.continuous).restrict _
    · simpa only [huR] using hvr
  have hgerm : u =ᶠ[𝓝 g] v := houter g (by cases right <;> exact le_rfl)
  exact ⟨u, hu, hNu, radialNaturalTail_overlap_cauchy hD he hf hef hg hu hv hNu hN hgerm⟩

theorem exists_radialNaturalTail_continuation {D : ReferenceData}
    (hD : RadialProfileGeometry D) {right : Bool} {j : ℕ} {e f : ℝ}
    (he : e ∈ radialCore D) (hf : f ∈ radialCore D)
    (hef : if right then e < f else f < e)
    {v : ℝ → ℝ} (hv : ContDiff ℝ ∞ v) (hN : RadialNaturalTail D right j f v) :
    ∃ u : ℝ → ℝ, ContDiff ℝ ∞ u ∧ RadialNaturalTail D right j e u := by
  obtain ⟨u, hu, hNu, _, _⟩ := exists_radialNaturalTail_continuation_with_cauchy hD he hf hef hv hN
  exact ⟨u, hu, hNu⟩

end ContinuousFlexibility.Radial
