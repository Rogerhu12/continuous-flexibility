module

public import ContinuousFlexibility.Radial.ReferenceSmoothGreen

/-!
# The actual remainder and forcing of a reference graph element

The left-tail field, the true border column, and their physical differential
expressions are retained as functions. Their periodicity is proved from the
original formulas, and integrable pairings can be subtracted without using
the convention that a nonintegrable Bochner integral is zero.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open ContinuousFlexibility.Radial
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

def n06ReferenceTestOperator (D : ReferenceData) (φ : PolarPoint → ℝ) :
    PolarPoint → ℝ := fun p => radialPDE D.w (fun r θ => φ (r, θ)) p.1 p.2

def n06ReferenceLeftField (χ : ℝ → ℝ) : PolarPoint → ℝ :=
  fun p => χ p.1

def n06ReferenceNuField (D : ReferenceData) : PolarPoint → ℝ :=
  fun p => referenceColumn D p.1 * cosineMode 2 p.2

def n06ReferenceRemainder (χ : ℝ → ℝ) (η : PolarPoint → ℝ) (aL : ℝ) :
    PolarPoint → ℝ := fun p => η p - aL * n06ReferenceLeftField χ p

def n06ReferenceRemainderForcing (D : ReferenceData) (χ : ℝ → ℝ) (g : PolarPoint → ℝ)
    (μ aL : ℝ) : PolarPoint → ℝ := fun p =>
  g p - μ * n06ReferenceNuField D p -
    aL * n06ReferenceTestOperator D (n06ReferenceLeftField χ) p

theorem n06_referenceLeftField_contDiff {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) : ContDiff ℝ ∞ (n06ReferenceLeftField χ) :=
  hχ.comp contDiff_fst

theorem n06_referenceLeftField_periodic (χ : ℝ → ℝ) (t : ℝ) :
    Function.Periodic (n06ReferenceLeftField χ) (0, t) := by
  intro p
  simp only [n06ReferenceLeftField, Prod.fst_add, add_zero]

theorem n06_referenceNuField_continuous {D : ReferenceData}
    (hgeom : RadialProfileGeometry D) (hb : RadialTrueBorder D) :
    Continuous (n06ReferenceNuField D) := by
  have hc : Continuous (cosineMode 2) :=
    (show Differentiable ℝ (cosineMode 2) from
      fun θ => (hasDerivAt_cosineMode 2 θ).differentiableAt).continuous
  exact ((r11b_continuous_referenceColumn hgeom hb).comp continuous_fst).mul
    (hc.comp continuous_snd)

theorem n06_referenceNuField_periodic (D : ReferenceData) :
    Function.Periodic (n06ReferenceNuField D) (0, Real.pi) := by
  intro p
  have hc := cosineMode_even_frequency_periodic 1 p.2
  simpa only [n06ReferenceNuField, Prod.fst_add, Prod.snd_add, add_zero,
    Nat.mul_one, hc]

theorem n06_referenceTestOperator_periodic {D : ReferenceData}
    (hw : ContDiff ℝ ∞ D.w) {φ : PolarPoint → ℝ}
    (hφ : ContDiff ℝ ∞ φ) {t : ℝ} (hp : Function.Periodic φ (0, t)) :
    Function.Periodic (n06ReferenceTestOperator D φ) (0, t) := by
  have hR := r11b_periodic_directionalPartial hφ hp (1, 0)
  have hA := r11b_periodic_directionalPartial hφ hp (0, 1)
  have hRR := r11b_periodic_directionalPartial
    (r11b_contDiff_directionalPartial hφ (1, 0)) hR (1, 0)
  have hAA := r11b_periodic_directionalPartial
    (r11b_contDiff_directionalPartial hφ (0, 1)) hA (0, 1)
  change Function.Periodic (radialPartial φ) (0, t) at hR
  change Function.Periodic (radialPartial (radialPartial φ)) (0, t) at hRR
  change Function.Periodic (angularPartial (angularPartial φ)) (0, t) at hAA
  have heq : n06ReferenceTestOperator D φ = fun p =>
      deriv D.w p.1 * radialPartial φ p + D.w p.1 * radialPartial (radialPartial φ) p +
        deriv D.w p.1 / p.1 * angularPartial (angularPartial φ) p := by
    funext p
    exact radialPDE_eq_polar_jets (hw.differentiable (by simp) p.1) hφ
  rw [heq]
  intro p
  simp only [Prod.fst_add, add_zero, hR p, hRR p, hAA p]

theorem n06_referenceRemainder_periodic {χ : ℝ → ℝ}
    {η : PolarPoint → ℝ} (hη : Function.Periodic η (0, Real.pi)) (aL : ℝ) :
    Function.Periodic (n06ReferenceRemainder χ η aL) (0, Real.pi) := by
  intro p
  simp only [n06ReferenceRemainder, hη p, n06_referenceLeftField_periodic χ Real.pi p]

theorem n06_referenceRemainderForcing_periodic {D : ReferenceData} {χ : ℝ → ℝ}
    (hw : ContDiff ℝ ∞ D.w) (hcutoff : ContDiff ℝ ∞ χ)
    {g : PolarPoint → ℝ} (hg : Function.Periodic g (0, Real.pi)) (μ aL : ℝ) :
    Function.Periodic (n06ReferenceRemainderForcing D χ g μ aL) (0, Real.pi) := by
  have hχ := n06_referenceTestOperator_periodic hw (n06_referenceLeftField_contDiff hcutoff)
    (n06_referenceLeftField_periodic χ Real.pi)
  intro p
  simp only [n06ReferenceRemainderForcing, hg p, n06_referenceNuField_periodic D p, hχ p]

theorem n06_integrable_sub_mul {μ : Measure PolarPoint}
    {f g φ : PolarPoint → ℝ}
    (hf : Integrable (fun p => f p * φ p) μ)
    (hg : Integrable (fun p => g p * φ p) μ) (c : ℝ) :
    Integrable (fun p => (f p - c * g p) * φ p) μ := by
  apply (hf.sub (hg.const_mul c)).congr
  filter_upwards with p
  dsimp only [Pi.sub_apply]
  ring

theorem n06_integral_sub_mul {μ : Measure PolarPoint}
    {f g φ : PolarPoint → ℝ}
    (hf : Integrable (fun p => f p * φ p) μ)
    (hg : Integrable (fun p => g p * φ p) μ) (c : ℝ) :
    (∫ p, (f p - c * g p) * φ p ∂μ) =
      (∫ p, f p * φ p ∂μ) - c * ∫ p, g p * φ p ∂μ := by
  calc
    _ = ∫ p, f p * φ p - c * (g p * φ p) ∂μ := by
      apply integral_congr_ae
      filter_upwards with p
      ring
    _ = _ := by rw [integral_sub hf (hg.const_mul c), integral_const_mul]

end ContinuousFlexibility.Statements
