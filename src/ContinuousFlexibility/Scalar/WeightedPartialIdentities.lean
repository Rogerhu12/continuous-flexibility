module

public import ContinuousFlexibility.Analysis.CylinderMixedJets

/-!
# Ordinary mixed jets and the scalar height derivatives

These identities retain the actual Fréchet partials used by scalar geometry.
They let the quantitative mixed-jet estimates control the radial derivative,
the normalized angular derivative and its angular derivative.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open scoped ContDiff

theorem radialPartial_eq_mixedDerivative_on
    {U : Set PolarPoint} {f : PolarPoint → ℝ}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) {p : PolarPoint} (hp : p ∈ U) :
    radialPartial f p = mixedDerivative 1 0 f p := by
  simpa only [mixedDerivative, iteratedDeriv_zero, zero_add] using
    mixedDerivative_radialPartial hU hf 0 0 hp

theorem angularPartial_eq_mixedDerivative_on
    {U : Set PolarPoint} {f : PolarPoint → ℝ}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) {p : PolarPoint} (hp : p ∈ U) :
    angularPartial f p = mixedDerivative 0 1 f p := by
  simpa only [mixedDerivative, iteratedDeriv_zero, zero_add] using
    mixedDerivative_angularPartial hU hf 0 0 hp

theorem heightAngular_eq_mixedDerivative_on
    {U : Set PolarPoint} {f : PolarPoint → ℝ}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) {p : PolarPoint} (hp : p ∈ U) :
    heightAngular f p = mixedDerivative 0 1 f p / p.1 := by
  rw [heightAngular, angularPartial_eq_mixedDerivative_on hU hf hp]

theorem angularPartial_heightAngular_eq_mixedDerivative_on
    {U : Set PolarPoint} {f : PolarPoint → ℝ}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) {p : PolarPoint}
    (hp : p ∈ U) (hr : p.1 ≠ 0) :
    angularPartial (heightAngular f) p = mixedDerivative 0 2 f p / p.1 := by
  have hang : ContDiffOn ℝ ∞ (angularPartial f) U :=
    (hf.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const
  have hsecond : angularPartial (angularPartial f) p = mixedDerivative 0 2 f p :=
    (angularPartial_eq_mixedDerivative_on hU hang hp).trans
      (mixedDerivative_angularPartial hU hf 0 1 hp)
  have hd : DifferentiableAt ℝ (angularPartial f) p :=
    (hang.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  change angularPartial (fun y => angularPartial f y / y.1) p = _
  rw [angularPartial_div hd differentiableAt_fst hr, angularPartial_fst, hsecond]
  field_simp <;> ring

end ContinuousFlexibility.Statements
