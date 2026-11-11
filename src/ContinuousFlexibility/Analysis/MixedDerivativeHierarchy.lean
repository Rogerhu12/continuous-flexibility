import ContinuousFlexibility.Analysis.MixedDerivativeLocality

/-!
# The two actual first derivatives of the mixed derivative hierarchy

The statements are local on the original open cylinder. They do not
require an extension of a smooth field outside that cylinder.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Statements

open Set Filter
open scoped ContDiff Topology

theorem hasDerivAt_radial_slice_of_differentiableAt
    {f : PolarPoint → ℝ} {p : PolarPoint} (hf : DifferentiableAt ℝ f p) :
    HasDerivAt (fun r => f (r, p.2)) (radialPartial f p) p.1 := by
  have h := hf.hasFDerivAt.comp_hasDerivAt p.1
    ((hasDerivAt_id' p.1).prodMk (hasDerivAt_const p.1 p.2))
  simpa only [Function.comp_def, radialPartial] using h

theorem hasDerivAt_angular_slice_of_differentiableAt
    {f : PolarPoint → ℝ} {p : PolarPoint} (hf : DifferentiableAt ℝ f p) :
    HasDerivAt (fun θ => f (p.1, θ)) (angularPartial f p) p.2 := by
  have h := hf.hasFDerivAt.comp_hasDerivAt p.2
    ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id' p.2))
  simpa only [Function.comp_def, angularPartial] using h

theorem radialPartial_mixedDerivative_of_contDiffOn
    {V : Set PolarPoint} {f : PolarPoint → ℝ}
    (hV : IsOpen V) (hf : ContDiffOn ℝ ∞ f V)
    (a b : ℕ) {p : PolarPoint} (hp : p ∈ V) :
    radialPartial (mixedDerivative a b f) p = mixedDerivative (a + 1) b f p := by
  have hs := ((contDiffOn_mixedDerivative hV hf a b).contDiffAt
    (hV.mem_nhds hp)).differentiableAt (by simp)
  rw [← (hasDerivAt_radial_slice_of_differentiableAt hs).deriv]
  simp only [mixedDerivative, iteratedDeriv_succ]

theorem angularPartial_mixedDerivative_of_contDiffOn
    {V : Set PolarPoint} {f : PolarPoint → ℝ}
    (hV : IsOpen V) (hf : ContDiffOn ℝ ∞ f V)
    (a b : ℕ) {p : PolarPoint} (hp : p ∈ V) :
    angularPartial (mixedDerivative a b f) p = mixedDerivative a (b + 1) f p := by
  induction a generalizing p with
  | zero =>
      have hs := ((contDiffOn_mixedDerivative hV hf 0 b).contDiffAt
        (hV.mem_nhds hp)).differentiableAt (by simp)
      rw [← (hasDerivAt_angular_slice_of_differentiableAt hs).deriv]
      simp only [mixedDerivative, iteratedDeriv_zero, iteratedDeriv_succ]
  | succ a ih =>
      let g : PolarPoint → ℝ := mixedDerivative a b f
      have hs : ContDiffOn ℝ ∞ g V := contDiffOn_mixedDerivative hV hf a b
      have hrad : mixedDerivative (a + 1) b f =ᶠ[𝓝 p] radialPartial g := by
        filter_upwards [hV.mem_nhds hp] with q hq
        exact (radialPartial_mixedDerivative_of_contDiffOn hV hf a b hq).symm
      have hang : angularPartial g =ᶠ[𝓝 p] mixedDerivative a (b + 1) f := by
        filter_upwards [hV.mem_nhds hp] with q hq
        exact ih hq
      calc
        angularPartial (mixedDerivative (a + 1) b f) p =
            angularPartial (radialPartial g) p :=
          congrArg (fun L : PolarPoint →L[ℝ] ℝ => L (0, 1)) hrad.fderiv_eq
        _ = radialPartial (angularPartial g) p :=
          (radial_angular_commute ((hs.contDiffAt (hV.mem_nhds hp)).of_le (by simp))).symm
        _ = radialPartial (mixedDerivative a (b + 1) f) p :=
          congrArg (fun L : PolarPoint →L[ℝ] ℝ => L (1, 0)) hang.fderiv_eq
        _ = mixedDerivative (a + 1) (b + 1) f p :=
          radialPartial_mixedDerivative_of_contDiffOn hV hf a (b + 1) hp

theorem mixedDerivative_hasDerivAt_radial
    {V : Set PolarPoint} {f : PolarPoint → ℝ}
    (hV : IsOpen V) (hf : ContDiffOn ℝ ∞ f V)
    (a b : ℕ) {p : PolarPoint} (hp : p ∈ V) :
    HasDerivAt (fun r => mixedDerivative a b f (r, p.2))
      (mixedDerivative (a + 1) b f p) p.1 := by
  have h := hasDerivAt_radial_slice_of_differentiableAt
    (((contDiffOn_mixedDerivative hV hf a b).contDiffAt
      (hV.mem_nhds hp)).differentiableAt (by simp))
  exact h.congr_deriv (radialPartial_mixedDerivative_of_contDiffOn hV hf a b hp)

theorem mixedDerivative_hasDerivAt_angular
    {V : Set PolarPoint} {f : PolarPoint → ℝ}
    (hV : IsOpen V) (hf : ContDiffOn ℝ ∞ f V)
    (a b : ℕ) {p : PolarPoint} (hp : p ∈ V) :
    HasDerivAt (fun θ => mixedDerivative a b f (p.1, θ))
      (mixedDerivative a (b + 1) f p) p.2 := by
  have h := hasDerivAt_angular_slice_of_differentiableAt
    (((contDiffOn_mixedDerivative hV hf a b).contDiffAt
      (hV.mem_nhds hp)).differentiableAt (by simp))
  exact h.congr_deriv (angularPartial_mixedDerivative_of_contDiffOn hV hf a b hp)

end ContinuousFlexibility.Statements
