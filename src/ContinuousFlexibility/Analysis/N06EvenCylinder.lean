module

public import ContinuousFlexibility.Analysis.N06FiniteCylinder
public import ContinuousFlexibility.Radial.ReferenceCosineAlgebra
public import ContinuousFlexibility.Radial.ReferenceCosineParseval

/-!
# The graph estimate in the actual even π-periodic Fourier sector

The existing normalized mean/cosine basis is paired with the negative sine
family. A constant at index zero completes that partner family; its
frequency is zero, so it contributes nothing to actual derivatives.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open scoped BigOperators ContDiff
open ContinuousFlexibility.Radial ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

/-- The derivative partner of the existing normalized mean/cosine basis. -/
def n06AngularPartner : ℕ → ℝ → ℝ
  | 0 => fun _ => 1
  | n + 1 => fun θ => -sineMode (2 * (n + 1)) θ

theorem n06_contDiff_angularPartner (n : ℕ) :
    ContDiff ℝ ∞ (n06AngularPartner n) := by
  cases n with
  | zero => exact contDiff_const
  | succ n =>
    change ContDiff ℝ ∞ (fun θ : ℝ =>
      -(Real.sqrt 2 * Real.sin (((2 * (n + 1) : ℕ) : ℝ) * θ)))
    exact (contDiff_const.mul ((contDiff_const.mul contDiff_id).sin)).neg

theorem n06_angularPartner_pairing (i j : ℕ) :
    angularPairing (n06AngularPartner i) (n06AngularPartner j) =
      if i = j then 1 else 0 := by
  cases i with
  | zero =>
    cases j with
    | zero =>
      change angularAverage (fun _ : ℝ => (1 : ℝ) * 1) = 1
      simp only [mul_one, angularAverage, intervalIntegral.integral_const,
        sub_zero, smul_eq_mul]
      field_simp [Real.pi_ne_zero]
    | succ j =>
      change angularAverage (fun θ => 1 * (-sineMode (2 * (j + 1)) θ)) = 0
      simp only [one_mul, angularAverage, intervalIntegral.integral_neg,
        integral_sineMode, neg_zero, mul_zero]
  | succ i =>
    cases j with
    | zero =>
      change angularAverage (fun θ => (-sineMode (2 * (i + 1)) θ) * 1) = 0
      simp only [mul_one, angularAverage, intervalIntegral.integral_neg,
        integral_sineMode, neg_zero, mul_zero]
    | succ j =>
      have h := angularPairing_sineMode (2 * (i + 1)) (2 * (j + 1))
        (by omega) (by omega)
      by_cases hij : i = j
      · subst j
        simpa only [n06AngularPartner, angularPairing, neg_mul_neg, ite_true] using h
      · have hfreq : 2 * (i + 1) ≠ 2 * (j + 1) := by omega
        have hsucc : i + 1 ≠ j + 1 := by omega
        simpa only [n06AngularPartner, angularPairing, neg_mul_neg,
          if_neg hfreq, if_neg hsucc] using h

theorem n06_referenceAngularBasis_hasDerivAt (n : ℕ) (θ : ℝ) :
    HasDerivAt (referenceAngularBasis n)
      (((2 * n : ℕ) : ℝ) * n06AngularPartner n θ) θ := by
  cases n with
  | zero =>
    simpa only [referenceAngularBasis, n06AngularPartner, Nat.mul_zero,
      Nat.cast_zero, zero_mul] using (hasDerivAt_const θ (1 : ℝ))
  | succ n =>
    change HasDerivAt (cosineMode (2 * (n + 1)))
      (((2 * (n + 1) : ℕ) : ℝ) * (-sineMode (2 * (n + 1)) θ)) θ
    exact (hasDerivAt_cosineMode (2 * (n + 1)) θ).congr_deriv (by
      rw [cosineModeFirst_eq_neg_mul_sineMode]
      ring)

theorem n06_angularPartner_hasDerivAt (n : ℕ) (θ : ℝ) :
    HasDerivAt (n06AngularPartner n)
      (-((2 * n : ℕ) : ℝ) * referenceAngularBasis n θ) θ := by
  cases n with
  | zero =>
    simpa only [referenceAngularBasis, n06AngularPartner, Nat.mul_zero,
      Nat.cast_zero, neg_zero, zero_mul] using (hasDerivAt_const θ (1 : ℝ))
  | succ n =>
    have h := ((((hasDerivAt_id' θ).const_mul (((2 * (n + 1) : ℕ) : ℝ))).sin).const_mul
      (Real.sqrt 2)).neg
    change HasDerivAt
      (fun t => -(Real.sqrt 2 * Real.sin (((2 * (n + 1) : ℕ) : ℝ) * t)))
      (-((2 * (n + 1) : ℕ) : ℝ) *
        (Real.sqrt 2 * Real.cos (((2 * (n + 1) : ℕ) : ℝ) * θ))) θ
    convert h using 1 <;> ring

/-- The finite-cylinder estimate instantiated with the repository's actual
even Fourier basis, including the mean at index zero. -/
theorem n06_even_cylinder_graph_bound
    (s : Finset ℕ) (u F : ℕ → ℝ → ℝ)
    {a c V q : ℝ → ℝ} {K : ℝ}
    (ha : ContDiff ℝ 1 a) (hu : ∀ i ∈ s, ContDiff ℝ ∞ (u i))
    (hc : Continuous c) (hV : Continuous V) (hq : ContDiff ℝ 2 q)
    (hF : ∀ i ∈ s, ∀ y, F i y =
      -deriv (fun t => a t * deriv (u i) t) y +
        ((2 * i : ℕ) : ℝ) ^ 2 * c y * u i y + V y * u i y)
    (hK : 1 ≤ K)
    (ha₁ : ∀ y ∈ Icc (0 : ℝ) 1, 1 / K ≤ a y)
    (ha₂ : ∀ y ∈ Icc (0 : ℝ) 1, a y ≤ K)
    (ha₃ : ∀ y ∈ Icc (0 : ℝ) 1, |deriv a y| ≤ K)
    (hc₁ : ∀ y ∈ Icc (0 : ℝ) 1, cylinderWeight y / K ≤ c y)
    (hV₁ : ∀ y ∈ Icc (0 : ℝ) 1, |V y| ≤ K)
    (hqa : ∀ y ∈ Icc (0 : ℝ) 1, c y = a y * q y)
    (hq₂ : ∀ y ∈ Icc (0 : ℝ) 1, |deriv (deriv q) y| ≤ K) :
    n06CylinderGraphSquare (r11bFiniteSynthesis s u referenceAngularBasis) ≤
      16384 * K ^ 10 *
        (n06CylinderSquare 0 (r11bFiniteSynthesis s F referenceAngularBasis) +
          n06CylinderSquare 0 (r11bFiniteSynthesis s u referenceAngularBasis)) := by
  have heorth (i j : ℕ) :
      angularPairing (referenceAngularBasis i) (referenceAngularBasis j) =
        if i = j then 1 else 0 := by
    simpa only [angularPairing, angularAverage, radialAngularMean, one_div] using
      referenceAngularBasis_pairing i j
  exact n06_finite_cylinder_graph_bound s u F referenceAngularBasis n06AngularPartner
    (fun i => ((2 * i : ℕ) : ℝ)) ha hu hc hV hq hF
    (fun i _ => contDiff_referenceAngularBasis i)
    (fun i _ => n06_contDiff_angularPartner i)
    (fun i _ => memLp_referenceAngular_interval_of_continuous
      (contDiff_referenceAngularBasis i).continuous)
    (fun i _ => memLp_referenceAngular_interval_of_continuous
      (n06_contDiff_angularPartner i).continuous)
    (fun i _ j _ => heorth i j)
    (fun i _ j _ => n06_angularPartner_pairing i j)
    (fun i _ θ => n06_referenceAngularBasis_hasDerivAt i θ)
    (fun i _ θ => n06_angularPartner_hasDerivAt i θ)
    hK ha₁ ha₂ ha₃ hc₁ hV₁ hqa hq₂

/-- On π-periodic fields the normalized cylinder square is the actual
half-period square integral divided by π. -/
theorem n06CylinderSquare_eq_halfPeriod (k : ℕ) (U : PolarPoint → ℝ)
    (hU : Continuous U)
    (hp : ∀ y, Function.Periodic (fun θ => U (y, θ)) Real.pi) :
    n06CylinderSquare k U =
      Real.pi⁻¹ * (∫ y in (0 : ℝ)..1,
        cylinderWeight y ^ k * (∫ θ in (0 : ℝ)..Real.pi, U (y, θ) ^ 2)) := by
  unfold n06CylinderSquare
  have hs (y : ℝ) :
      angularAverage (fun θ => U (y, θ) ^ 2) =
        Real.pi⁻¹ * (∫ θ in (0 : ℝ)..Real.pi, U (y, θ) ^ 2) := by
    have hcont : Continuous (fun θ => U (y, θ) ^ 2) :=
      (hU.comp (continuous_const.prodMk continuous_id)).pow 2
    have hper : Function.Periodic (fun θ => U (y, θ) ^ 2) Real.pi :=
      fun θ => congrArg (fun x : ℝ => x ^ 2) (hp y θ)
    simpa only [radialAngularMean, angularAverage, one_div] using
      radialAngularMean_eq_halfPeriod hper (hcont.intervalIntegrable _ _)
  simp_rw [hs]
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro y _
  ring

end ContinuousFlexibility.Analysis
