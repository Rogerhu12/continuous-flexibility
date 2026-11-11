import ContinuousFlexibility.Analysis.N04bRotationVariationBound
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# The actual first variation of the physical translation number

A uniform angular remainder o(q), together with the explicit bounded
Fourier corrector, implies a derivative of the translation number. The
constant Fourier coefficient is that derivative. The initial translation
and the uniform remainder are inputs about the actual family of maps;
no derivative of the translation number is assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Filter
open scoped Topology

theorem n04bPhysicalTranslationNumber_of_translation
    (f : CircleDeg1Lift) (T : ℝ)
    (hF : ∀ θ : ℝ, n04bPhysicalLift f θ = θ + T) :
    n04bPhysicalTranslationNumber f = T := by
  have hf (x : ℝ) : f x = x + T / Real.pi := by
    have hx := hF (Real.pi * x)
    rw [n04bPhysicalLift_pi] at hx
    calc
      f x = (Real.pi * x + T) / Real.pi :=
        (eq_div_iff Real.pi_ne_zero).mpr (by simpa only [mul_comm] using hx)
      _ = _ := by field_simp [Real.pi_ne_zero]; ring
  have ht : f.translationNumber = T / Real.pi :=
    le_antisymm
      (f.translationNumber_le_of_le_add (fun x => (hf x).le))
      (f.le_translationNumber_of_add_le (fun x => (hf x).ge))
  rw [n04bPhysicalTranslationNumber, ht]
  field_simp [Real.pi_ne_zero]

theorem n04b_physicalTranslationNumber_slope_bound
    (f : CircleDeg1Lift) {T : ℝ} (hT : Real.sin T ≠ 0) (a b c q η : ℝ)
    (hq : q ≠ 0)
    (hrem : ∀ θ : ℝ,
      |n04bPhysicalLift f θ - θ - T -
        q * (c + n04bSecondHarmonic a b θ)| ≤ |q| * η) :
    |(n04bPhysicalTranslationNumber f - T) / q - c| ≤
      η + |q| * n04bFourierLipschitz T a b * (|c| + |a| + |b| + η) := by
  have he : (n04bPhysicalTranslationNumber f - T) / q - c =
      (n04bPhysicalTranslationNumber f - T - q * c) / q := by
    field_simp [hq]
    <;> ring
  rw [he, abs_div]
  apply (div_le_iff₀ (abs_pos.mpr hq)).mpr
  calc
    _ ≤ n04bFourierRemainderBound T a b c q η :=
      n04b_physicalTranslationNumber_fourier_bound f hT a b c q η hrem
    _ = _ := by
      dsimp only [n04bFourierRemainderBound]
      rw [← sq_abs q]
      ring

/-- Uniform first-order expansion of the actual family implies the
physical translation-number derivative. The remainder is uniform in
angle on a punctured parameter neighborhood. -/
theorem n04b_hasDerivAt_physicalTranslationNumber
    (f : ℝ → CircleDeg1Lift) {T : ℝ} (hT : Real.sin T ≠ 0)
    (a b c : ℝ) (η : ℝ → ℝ)
    (hzero : n04bPhysicalTranslationNumber (f 0) = T)
    (hη : Tendsto η (𝓝[≠] (0 : ℝ)) (𝓝 0))
    (hrem : ∀ᶠ q in 𝓝[≠] (0 : ℝ), ∀ θ : ℝ,
      |n04bPhysicalLift (f q) θ - θ - T -
        q * (c + n04bSecondHarmonic a b θ)| ≤ |q| * η q) :
    HasDerivAt (fun q : ℝ => n04bPhysicalTranslationNumber (f q)) c 0 := by
  let L : ℝ := n04bFourierLipschitz T a b
  let M : ℝ := |c| + |a| + |b|
  have ha : Tendsto (fun q : ℝ => |q|) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    simpa only [abs_zero] using
      (continuous_abs.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have hq0 : ∀ᶠ q : ℝ in 𝓝[≠] (0 : ℝ), q ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with q hq
    simpa using hq
  have hM : Tendsto (fun _ : ℝ => M) (𝓝[≠] (0 : ℝ)) (𝓝 M) :=
    tendsto_const_nhds
  have herr : Tendsto (fun q : ℝ => η q + |q| * L * (M + η q))
      (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    simpa only [zero_mul, zero_add, mul_zero, add_zero] using
      hη.add ((ha.mul_const L).mul (hM.add hη))
  have hslope : Tendsto
      (fun q : ℝ => (n04bPhysicalTranslationNumber (f q) - T) / q)
      (𝓝[≠] (0 : ℝ)) (𝓝 c) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have he : ∀ᶠ q in 𝓝[≠] (0 : ℝ), η q + |q| * L * (M + η q) < ε :=
      herr.eventually (Iio_mem_nhds hε)
    filter_upwards [hrem, hq0, he] with q hrem hq0 he
    rw [Real.dist_eq]
    exact (n04b_physicalTranslationNumber_slope_bound (f q) hT a b c q (η q)
      hq0 hrem).trans_lt he
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  simpa only [zero_add, hzero, smul_eq_mul, div_eq_mul_inv, mul_comm] using hslope

/-- The same result directly for actual monotone π-periodic physical
maps. Irrationality supplies the finite-mode nonresonance. -/
theorem n04b_hasDerivAt_piLiftTranslationNumber
    (F : ℝ → ℝ → ℝ)
    (hmono : ∀ q : ℝ, Monotone (F q))
    (hperiod : ∀ q θ : ℝ, F q (θ + Real.pi) = F q θ + Real.pi)
    {T : ℝ} (hT : Irrational (T / Real.pi))
    (a b c : ℝ) (η : ℝ → ℝ)
    (hzero : ∀ θ : ℝ, F 0 θ = θ + T)
    (hη : Tendsto η (𝓝[≠] (0 : ℝ)) (𝓝 0))
    (hrem : ∀ᶠ q in 𝓝[≠] (0 : ℝ), ∀ θ : ℝ,
      |F q θ - θ - T - q * (c + n04bSecondHarmonic a b θ)| ≤ |q| * η q) :
    HasDerivAt
      (fun q : ℝ => n04bPhysicalTranslationNumber (n04bPiLift (F q) (hmono q) (hperiod q)))
      c 0 := by
  apply n04b_hasDerivAt_physicalTranslationNumber
    (fun q => n04bPiLift (F q) (hmono q) (hperiod q))
    (n04b_sin_ne_zero_of_irrational hT) a b c η
  · apply n04bPhysicalTranslationNumber_of_translation
    intro θ
    rw [n04bPhysicalLift_normalize]
    exact hzero θ
  · exact hη
  · filter_upwards [hrem] with q hq
    intro θ
    simpa only [n04bPhysicalLift_normalize] using hq θ

end ContinuousFlexibility.Analysis
