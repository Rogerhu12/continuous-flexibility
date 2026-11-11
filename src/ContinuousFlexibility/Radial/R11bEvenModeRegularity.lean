import ContinuousFlexibility.Radial.R11bFourierCoefficients
import ContinuousFlexibility.Radial.R11bWeakModes
import ContinuousFlexibility.Radial.R11bZeroMode
import ContinuousFlexibility.Radial.R11bGlobalL2
import ContinuousFlexibility.Radial.R11bRadialTests
import ContinuousFlexibility.Analysis.IntervalWeakPotentialRegularity

/-!
# Actual C¹ representatives of every even angular coefficient

The mean occupies index zero, the physical border occupies index one, and
all positive frequencies are 2*n. Moving only the actual border to the
forcing gives the scalar potential equation and its integrated flux.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory
open scoped ContDiff
open ContinuousFlexibility.Statements ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

def r11bEvenModeForcing (D : ReferenceData) (U : RadialUnknown)
    (F : RadialSource) (n : ℕ) (r : ℝ) : ℝ :=
  evenFourierCoefficient F.1 n r -
    (if n = 1 then U.2 else 0) * referenceColumn D r

theorem r11b_evenModeForcing_memLp {D : ReferenceData}
    (hgeom : RadialProfileGeometry D) (hborder : RadialTrueBorder D)
    (U : RadialUnknown) {F : RadialSource}
    (hf : MemLp F.1 2 (radialPhysicalMeasure D)) (n : ℕ) :
    MemLp (r11bEvenModeForcing D U F n) 2 (volume.restrict (radialCore D)) := by
  have hcoef := evenFourierCoefficient_memLp (r11b_memLp_radial_angularMean hf) n
  have hcol : MemLp (referenceColumn D) 2 (volume.restrict (radialCore D)) :=
    interval_memLp_of_continuous (r11b_continuous_referenceColumn hgeom hborder)
  apply MemLp.ae_eq _ (hcoef.sub (hcol.const_mul (if n = 1 then U.2 else 0)))
  exact Filter.Eventually.of_forall fun _ => rfl

theorem r11b_evenCoefficient_weak_equation {D : ReferenceData}
    (hgeom : RadialProfileGeometry D) (hborder : RadialTrueBorder D)
    {γ M₀ M₁ : ℝ} {U : RadialUnknown} {F : RadialSource}
    (hUF : ReferenceGraph D γ M₀ M₁ U F)
    (hf : MemLp F.1 2 (radialPhysicalMeasure D)) (n : ℕ)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ radialCore D) :
    (∫ r in D.a..D.b, evenFourierCoefficient U.1 n r *
      (deriv (fun t => D.w t * deriv φ t) r -
        (((2 * n : ℕ) : ℝ) ^ 2 * deriv D.w r / r) * φ r)) =
      ∫ r in D.a..D.b, r11bEvenModeForcing D U F n r * φ r := by
  by_cases hn : n = 0
  · subst n
    simpa [r11bEvenModeForcing, evenFourierCoefficient_zero_physical] using
      r11b_referenceGraph_mean_equation hUF hφ hφc hφs
  · have hj : 0 < 2 * n := by omega
    have hj2 : 2 * n = 2 ↔ n = 1 := by omega
    have h := r11b_referenceGraph_mode_equation hgeom hUF (2 * n) hj hφ hφc hφs
    have hcoef := evenFourierCoefficient_memLp (r11b_memLp_radial_angularMean hf) n
    have hfi : IntervalIntegrable
        (fun r => referenceMode F.1 (2 * n) r * φ r) volume D.a D.b := by
      simpa only [evenFourierCoefficient_eq_referenceMode F.1 hn] using
        intervalIntegrable_mul_continuous hgeom.2.1.le hcoef hφ.continuous
    have hcol : MemLp (referenceColumn D) 2 (volume.restrict (radialCore D)) :=
      interval_memLp_of_continuous (r11b_continuous_referenceColumn hgeom hborder)
    have hgi := intervalIntegrable_mul_continuous hgeom.2.1.le hcol hφ.continuous
    have hrhs :
        (∫ r in D.a..D.b, r11bEvenModeForcing D U F n r * φ r) =
          (∫ r in D.a..D.b, referenceMode F.1 (2 * n) r * φ r) -
            (if n = 1 then U.2 else 0) *
              (∫ r in D.a..D.b, referenceColumn D r * φ r) := by
      unfold r11bEvenModeForcing
      rw [evenFourierCoefficient_eq_referenceMode F.1 hn]
      simp_rw [sub_mul, mul_assoc]
      rw [intervalIntegral.integral_sub hfi
        (hgi.const_mul (if n = 1 then U.2 else 0)), intervalIntegral.integral_const_mul]
    rw [hrhs, evenFourierCoefficient_eq_referenceMode U.1 hn]
    change (∫ r in D.a..D.b,
      referenceMode U.1 (2 * n) r * radialJacobi (((2 * n : ℕ) : ℝ) ^ 2) D.w φ r) = _
    simp only [hj2] at h
    linarith

theorem r11b_evenCoefficient_contDiffOn_one_representative {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    {γ M₀ M₁ : ℝ} (hγ : 0 < γ) {U : RadialUnknown} {F : RadialSource}
    (hUF : ReferenceGraph D γ M₀ M₁ U F) (n : ℕ) (r₀ : ℝ)
    (hr₀ : r₀ ∈ radialCore D) :
    ∃ c : ℝ → ℝ, ∃ q : ℝ,
      evenFourierCoefficient U.1 n =ᵐ[volume.restrict (radialCore D)] c ∧
      ContDiffOn ℝ 1 c (radialCore D) ∧
      ∀ r ∈ radialCore D, D.w r * deriv c r =
        intervalLocalPrimitive
          (fun t => r11bEvenModeForcing D U F n t +
            c t * (((2 * n : ℕ) : ℝ) ^ 2 * deriv D.w t / t)) r₀ r + q := by
  have hgeom : RadialProfileGeometry D := hD.choose_spec.1
  have huLp := r11b_output_memLp hD hborder hγ hUF.1
  have hfLp := r11b_source_memLp hD hγ hUF.2.1
  have hu := evenFourierCoefficient_memLp (r11b_memLp_radial_angularMean huLp) n
  have hf := r11b_evenModeForcing_memLp hgeom hborder U hfLp n
  have hV : Continuous (fun r => ((2 * n : ℕ) : ℝ) ^ 2 * deriv D.w r / r) := by
    simp_rw [mul_div_assoc]
    exact continuous_const.mul (r11b_continuous_flat_deriv_div hgeom.1 hgeom.2.2.1)
  exact exists_contDiffOn_one_rep_of_weak_potential_Ioo hgeom.2.1 hu hf
    hgeom.2.2.1.1 (fun r hr => (hgeom.2.2.2.2.1 r hr).ne') hV r₀ hr₀
    (fun _ hφ hφc hφs =>
      r11b_evenCoefficient_weak_equation hgeom hborder hUF hfLp n hφ hφc hφs)

end ContinuousFlexibility.Radial
