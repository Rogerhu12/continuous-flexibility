import ContinuousFlexibility.Analysis.CylinderSobolev

/-!
# Gluing at a genuine radial endpoint germ

An actual joint germ, not a collection of unrelated scalar slice germs,
allows two smooth cylinder fields to be glued at a fixed radial exit.
The glued field is exactly the second field beyond that exit and retains
a common radial derivative lower bound. Two applications preserve the
fixed reference field between disjoint left and right collars.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

def radialGermGlue (c : ℝ) (F G : PolarPoint → ℝ) (p : PolarPoint) : ℝ :=
  if p.1 < c then F p else G p

theorem radialGermGlue_eventuallyEq
    {c : ℝ} {F G : PolarPoint → ℝ}
    (hmatch : ∀ θ, F =ᶠ[𝓝 (c, θ)] G) (p : PolarPoint) :
    radialGermGlue c F G =ᶠ[𝓝 p] (if p.1 < c then F else G) := by
  by_cases hp : p.1 < c
  · rw [if_pos hp]
    filter_upwards [(isOpen_lt continuous_fst continuous_const).mem_nhds hp] with q hq
    simp only [radialGermGlue, if_pos hq]
  · rw [if_neg hp]
    by_cases he : p.1 = c
    · have hpair : p = (c, p.2) := Prod.ext he rfl
      have hm : F =ᶠ[𝓝 p] G := by rw [hpair]; exact hmatch p.2
      filter_upwards [hm] with q hq
      by_cases hqcut : q.1 < c
      · simp only [radialGermGlue, if_pos hqcut, hq]
      · simp only [radialGermGlue, if_neg hqcut]
    · have hgt : c < p.1 := lt_of_le_of_ne (le_of_not_gt hp) (Ne.symm he)
      filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds hgt] with q hq
      simp only [radialGermGlue, if_neg (not_lt_of_ge hq.le)]

theorem contDiff_radialGermGlue
    {c : ℝ} {F G : PolarPoint → ℝ}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    (hmatch : ∀ θ, F =ᶠ[𝓝 (c, θ)] G) :
    ContDiff ℝ ∞ (radialGermGlue c F G) := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  have he := radialGermGlue_eventuallyEq hmatch p
  by_cases hp : p.1 < c
  · rw [if_pos hp] at he
    exact hF.contDiffAt.congr_of_eventuallyEq he
  · rw [if_neg hp] at he
    exact hG.contDiffAt.congr_of_eventuallyEq he

theorem radialPartial_radialGermGlue
    {c : ℝ} {F G : PolarPoint → ℝ}
    (hmatch : ∀ θ, F =ᶠ[𝓝 (c, θ)] G) (p : PolarPoint) :
    radialPartial (radialGermGlue c F G) p =
      if p.1 < c then radialPartial F p else radialPartial G p := by
  have he := radialGermGlue_eventuallyEq hmatch p
  unfold radialPartial
  rw [he.fderiv_eq]
  split_ifs <;> rfl

theorem radialPartial_radialGermGlue_lower
    {c BF BG : ℝ} {F G : PolarPoint → ℝ}
    (hmatch : ∀ θ, F =ᶠ[𝓝 (c, θ)] G)
    (hF : ∀ p, BF ≤ radialPartial F p) (hG : ∀ p, BG ≤ radialPartial G p)
    (p : PolarPoint) :
    min BF BG ≤ radialPartial (radialGermGlue c F G) p := by
  rw [radialPartial_radialGermGlue hmatch p]
  split_ifs
  · exact (min_le_left BF BG).trans (hF p)
  · exact (min_le_right BF BG).trans (hG p)

theorem radialGermGlue_eq_left {c : ℝ} (F G : PolarPoint → ℝ) {p : PolarPoint}
    (hp : p.1 < c) : radialGermGlue c F G p = F p := by
  simp only [radialGermGlue, if_pos hp]

theorem radialGermGlue_eq_right {c : ℝ} (F G : PolarPoint → ℝ) {p : PolarPoint}
    (hp : c ≤ p.1) : radialGermGlue c F G p = G p := by
  simp only [radialGermGlue, if_neg (not_lt_of_ge hp)]

end ContinuousFlexibility.Analysis

