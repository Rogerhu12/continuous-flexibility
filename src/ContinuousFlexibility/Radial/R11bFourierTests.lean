module

public import ContinuousFlexibility.Radial.R11bRadialTests
public import ContinuousFlexibility.Radial.FourierSineOrthogonality

/-!
# Separated Fourier tests for the actual weak equations

These identities concern ordinary integrals and actual partial derivatives.
No summability or Fourier reconstruction is used here. A compact radial test
times any smooth periodic angular factor is an admissible two-dimensional
test, with its radial and angular derivatives computed explicitly.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped ContDiff Topology
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

theorem r11b_radialAngularMean_eq_angularAverage (f : ℝ → ℝ) :
    radialAngularMean f = angularAverage f := by
  simp only [radialAngularMean, angularAverage, one_div]

theorem r11b_radialAngularMean_const_mul (f : ℝ → ℝ) (c : ℝ) :
    radialAngularMean (fun θ => c * f θ) = c * radialAngularMean f := by
  unfold radialAngularMean
  rw [intervalIntegral.integral_const_mul]
  ring

theorem r11b_radialAngularMean_mul_const (f : ℝ → ℝ) (c : ℝ) :
    radialAngularMean (fun θ => f θ * c) = radialAngularMean f * c := by
  unfold radialAngularMean
  rw [intervalIntegral.integral_mul_const]
  ring

theorem r11b_radialAngularMean_lift_pairing (f e : ℝ → ℝ) (c : ℝ) :
    radialAngularMean (fun θ => f θ * (c * e θ)) =
      radialAngularMean (fun θ => f θ * e θ) * c := by
  have heq : (fun θ => f θ * (c * e θ)) = (fun θ => (f θ * e θ) * c) := by
    funext θ
    ring
  rw [heq, r11b_radialAngularMean_mul_const]

theorem r11b_contDiff_cosineMode (j : ℕ) : ContDiff ℝ ∞ (cosineMode j) :=
  contDiff_const.mul (Real.contDiff_cos.comp (contDiff_const.mul contDiff_id))

theorem r11b_contDiff_sineMode (j : ℕ) : ContDiff ℝ ∞ (sineMode j) :=
  contDiff_const.mul (Real.contDiff_sin.comp (contDiff_const.mul contDiff_id))

theorem r11b_cosineMode_periodic (j : ℕ) :
    Function.Periodic (cosineMode j) (2 * Real.pi) := by
  intro θ
  unfold cosineMode
  rw [mul_add, Real.cos_add_nat_mul_two_pi]

theorem r11b_sineMode_periodic (j : ℕ) :
    Function.Periodic (sineMode j) (2 * Real.pi) := by
  intro θ
  unfold sineMode
  rw [mul_add, Real.sin_add_nat_mul_two_pi]

theorem r11b_hasDerivAt_sineMode (j : ℕ) (θ : ℝ) :
    HasDerivAt (sineMode j) ((j : ℝ) * cosineMode j θ) θ := by
  have h := (((hasDerivAt_id θ).const_mul (j : ℝ)).sin).const_mul (Real.sqrt 2)
  unfold sineMode cosineMode
  convert h using 1
  · rfl
  · simp only [id_eq, mul_one]
    ring

theorem r11b_radialTest_separated {D : ReferenceData} {φ e : ℝ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ radialCore D) (he : ContDiff ℝ ∞ e)
    (hper : Function.Periodic e (2 * Real.pi)) :
    RadialTest D (fun x : PolarPoint => φ x.1 * e x.2) := by
  refine ⟨(hφ.comp contDiff_fst).mul (he.comp contDiff_snd), ?_, ?_⟩
  · intro x
    change φ (x.1 + 0) * e (x.2 + 2 * Real.pi) = φ x.1 * e x.2
    rw [add_zero, hper]
  · refine ⟨tsupport φ, hφc, hφs, ?_⟩
    intro r hr θ
    change φ r * e θ = 0
    rw [image_eq_zero_of_notMem_tsupport hr, zero_mul]

theorem r11b_radialTest_cosine {D : ReferenceData} {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ radialCore D) (j : ℕ) :
    RadialTest D (fun x : PolarPoint => φ x.1 * cosineMode j x.2) :=
  r11b_radialTest_separated hφ hφc hφs
    (r11b_contDiff_cosineMode j) (r11b_cosineMode_periodic j)

theorem r11b_radialTest_sine {D : ReferenceData} {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ radialCore D) (j : ℕ) :
    RadialTest D (fun x : PolarPoint => φ x.1 * sineMode j x.2) :=
  r11b_radialTest_separated hφ hφc hφs
    (r11b_contDiff_sineMode j) (r11b_sineMode_periodic j)

theorem r11b_angularPartial_separated {φ e : ℝ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (he : ContDiff ℝ ∞ e) (r θ : ℝ) :
    angularPartial (fun x : PolarPoint => φ x.1 * e x.2) (r, θ) =
      φ r * deriv e θ := by
  have hs : ContDiff ℝ ∞ (fun x : PolarPoint => φ x.1 * e x.2) :=
    (hφ.comp contDiff_fst).mul (he.comp contDiff_snd)
  exact (hasDerivAt_angularSlice (x := (r, θ))
    (hs.differentiable (by simp) (r, θ))).unique
      ((he.differentiable (by simp) θ).hasDerivAt.const_mul (φ r))

theorem r11b_radialPartial_separated {φ e : ℝ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (he : ContDiff ℝ ∞ e) (r θ : ℝ) :
    radialPartial (fun x : PolarPoint => φ x.1 * e x.2) (r, θ) =
      deriv φ r * e θ := by
  have hs : ContDiff ℝ ∞ (fun x : PolarPoint => φ x.1 * e x.2) :=
    (hφ.comp contDiff_fst).mul (he.comp contDiff_snd)
  exact (hasDerivAt_radialSlice (x := (r, θ))
    (hs.differentiable (by simp) (r, θ))).unique
      ((hφ.differentiable (by simp) r).hasDerivAt.mul_const (e θ))

theorem r11b_angularPartial_sine_test {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (j : ℕ) (r θ : ℝ) :
    angularPartial (fun x : PolarPoint => φ x.1 * sineMode j x.2) (r, θ) =
      (j : ℝ) * (φ r * cosineMode j θ) := by
  rw [r11b_angularPartial_separated hφ (r11b_contDiff_sineMode j),
    (r11b_hasDerivAt_sineMode j θ).deriv]
  ring

end ContinuousFlexibility.Radial
