import ContinuousFlexibility.Analysis.N01cEndpointDivision

/-!
# Joint parameter smoothness of the same endpoint quotient

Finite affine parameter planes keep the original radial divided function.
Its fixed-interval integral formula proves joint smoothness across both
roots, with no parameter-dependent choice of an extension.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Radial differentiation preserves joint smoothness of the genuine
finite-dimensional parameter family. -/
theorem contDiffAt_radialParameter_deriv
    {F : E × ℝ → ℝ} {x : E} {r : ℝ}
    (hF : ContDiffAt ℝ ∞ F (x, r)) :
    ContDiffAt ℝ ∞ (fun p : E × ℝ => deriv (fun t => F (p.1, t)) p.2) (x, r) := by
  have hs : ContDiffAt ℝ ∞ (fun p : ℝ × E => F (p.2, p.1)) (r, x) :=
    hF.comp (r, x) (contDiffAt_snd.prodMk contDiffAt_fst)
  have hd := (contDiffAt_parameter_fderiv hs).comp (x, r)
    (contDiffAt_snd.prodMk contDiffAt_fst)
  simpa only [fderiv_apply_one_eq_deriv] using
    hd.clm_apply (contDiffAt_const (c := (1 : ℝ)))

variable [FiniteDimensional ℝ E]

/-- The same `dslope`, with a fixed endpoint, is smooth jointly in the
finite parameters and the radial coordinate. -/
theorem contDiffOn_dslope_parameter
    {U : Set E} {R : Set ℝ} {F : E × ℝ → ℝ}
    (hU : IsOpen U) (hR : IsOpen R) (hconv : Convex ℝ R)
    (hF : ContDiffOn ℝ ∞ F (U ×ˢ R)) {a : ℝ} (ha : a ∈ R) :
    ContDiffOn ℝ ∞ (fun p : E × ℝ => dslope (fun r => F (p.1, r)) a p.2)
      (U ×ˢ R) := by
  let G : (E × ℝ) × ℝ → ℝ := fun p =>
    deriv (fun r => F (p.1.1, r)) (a + p.2 * (p.1.2 - a))
  have hparam : ∀ p ∈ U ×ˢ R, ∀ t ∈ Icc (0 : ℝ) 1,
      ContDiffAt ℝ ∞ G (p, t) := by
    intro p hp t ht
    have hr := rootDivision_affine_mem hconv ha hp.2 ht
    have hd := contDiffAt_radialParameter_deriv
      (hF.contDiffAt ((hU.prod hR).mem_nhds ⟨hp.1, hr⟩))
    exact hd.comp (p, t)
      (contDiffAt_fst.fst.prodMk (contDiffAt_const.add
        (contDiffAt_snd.mul (contDiffAt_fst.snd.sub contDiffAt_const))))
  have hi : ContDiffOn ℝ ∞ (fun p : E × ℝ => ∫ t in (0 : ℝ)..1, G (p, t))
      (U ×ˢ R) := by
    intro p hp
    exact (contDiffAt_intervalIntegral_parameter (hU.prod hR)
      (by norm_num) hparam hp).contDiffWithinAt
  apply hi.congr
  intro p hp
  have hx : ContDiffOn ℝ ∞ (fun r => F (p.1, r)) R :=
    hF.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun r hr => ⟨hp.1, hr⟩)
  exact dslope_eq_intervalIntegral_deriv hR hconv hx ha hp.2

/-- Both endpoint divisions preserve joint smoothness of the original
finite-parameter family, using one quotient on the entire interval. -/
theorem contDiffOn_twoRootDivided_parameter
    {U : Set E} {R : Set ℝ} {F : E × ℝ → ℝ}
    (hU : IsOpen U) (hR : IsOpen R) (hconv : Convex ℝ R)
    (hF : ContDiffOn ℝ ∞ F (U ×ˢ R)) {l h : ℝ} (hl : l ∈ R) (hh : h ∈ R) :
    ContDiffOn ℝ ∞
      (fun p : E × ℝ => twoRootDivided (fun r => F (p.1, r)) l h p.2)
      (U ×ˢ R) :=
  (contDiffOn_dslope_parameter hU hR hconv
    (contDiffOn_dslope_parameter hU hR hconv hF hl) hh).neg

end ContinuousFlexibility.Analysis
