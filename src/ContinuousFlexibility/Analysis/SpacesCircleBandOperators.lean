module

public import ContinuousFlexibility.Analysis.SpacesCircleFourierCut

/-!
# Joint circle band operators and reconstruction

These are actual operators on the angular `L²` spaces. The full countable
band decomposition reconstructs the function and every smooth derivative.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ENNReal ContDiff

/-- The angular derivative of a joint material-weight/frequency band. -/
def circleBandJet (M : ℝ) (hM : 1 ≤ M) (k b : ℕ) : AngleL2 →L[ℝ] AngleL2 :=
  circleFourierJetCut (circleFrequencyBand M k) (circleFrequencyBand_neg hM k) b

theorem circleBandJet_transform_apply (M : ℝ) (hM : 1 ≤ M) (k b : ℕ)
    (f : AngleL2) (n : ℤ) :
    circleFourierTransform (circleBandJet M hM k b f) n =
      if n ∈ circleFrequencyBand M k then
        (2 * Complex.I * (n : ℂ)) ^ b * circleFourierTransform f n else 0 :=
  circleFourierTransform_jetCut_apply _ (circleFrequencyBand_neg hM k) b f n

theorem circleBandJet_ae (M : ℝ) (hM : 1 ≤ M) (k b : ℕ) (f : AngleL2) :
    (circleBandJet M hM k b f : ℝ → ℝ) =ᵐ[angleMeasure]
      iteratedDeriv b (circleFourierCutFunction (circleFrequencyBand M k) f) :=
  circleFourierJetCutFun_ae _ b f

/-- The fixed-order synthesis bound has exponential growth in the band
index, with a constant depending only on the derivative order. -/
theorem circleBandJet_synthesis_bound (M : ℝ) (hM : 1 ≤ M) (k b c s : ℕ)
    (hbc : b + c ≤ s) (f : AngleL2) :
    ‖M ^ c • circleBandJet M hM k b f‖ ≤
      (Real.exp (s : ℝ) * Real.exp ((s : ℝ) * (k : ℝ))) * ‖f‖ := by
  apply circleFourierJetCut_weighted_norm_le _ (circleFrequencyBand_neg hM k) b f (M ^ c)
    (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))
  intro n hn
  rw [abs_of_nonneg (pow_nonneg (zero_le_one.trans hM) c)]
  exact circleFrequencyBand_synthesis_bound hM hn b c s hbc

theorem circleBandJet_zero_norm_le (M : ℝ) (hM : 1 ≤ M) (k : ℕ) (f : AngleL2) :
    ‖circleBandJet M hM k 0 f‖ ≤ ‖f‖ := by
  simpa only [pow_zero, one_smul, Nat.cast_zero, zero_mul, Real.exp_zero, one_mul] using
    circleBandJet_synthesis_bound M hM k 0 0 0 (by omega) f

/-- Applying a band again does not change any of its projected derivatives. -/
theorem circleBandJet_comp_zero (M : ℝ) (hM : 1 ≤ M) (k b : ℕ) (f : AngleL2) :
    circleBandJet M hM k b (circleBandJet M hM k 0 f) = circleBandJet M hM k b f := by
  apply circleFourierTransform.injective
  apply lp.ext
  funext n
  rw [circleBandJet_transform_apply, circleBandJet_transform_apply,
    circleBandJet_transform_apply]
  by_cases hn : n ∈ circleFrequencyBand M k
  · simp only [ite_eq_left hn, pow_zero, one_mul]
  · simp only [ite_eq_right hn]

/-- The complete spectral-band sum reconstructs every angular `L²` class. -/
theorem circleBandJet_hasSum_zero (M : ℝ) (hM : 1 ≤ M) (f : AngleL2) :
    HasSum (fun k : ℕ => circleBandJet M hM k 0 f) f := by
  have he (k : ℕ) : circleFourierTransform (circleBandJet M hM k 0 f) =
      Analysis.lpSpectralBand (Analysis.spectralLogBand (circleFrequencySize M)) k
        (circleFourierTransform f) := by
    apply lp.ext
    funext n
    rw [circleBandJet_transform_apply, Analysis.lpSpectralBand_apply]
    simp only [pow_zero, one_mul, circleFrequencyBand_mem hM]
  apply (circleFourierTransform.isometry.isEmbedding.isInducing.hasSum_iff
    (fun k : ℕ => circleBandJet M hM k 0 f) f).mp
  change HasSum (fun k : ℕ => circleFourierTransform (circleBandJet M hM k 0 f))
    (circleFourierTransform f)
  simpa only [he] using Analysis.hasSum_lpSpectralBand
    (Analysis.spectralLogBand (circleFrequencySize M)) (circleFourierTransform f)

/-- The normalized Fourier transform respects the actual derivative classes. -/
theorem circleFourierTransform_derivative {f d : AngleL2} {g : ℝ → ℝ}
    (hg : ContDiff ℝ ∞ g) (hp : Function.Periodic g Real.pi)
    (hfg : (f : ℝ → ℝ) =ᵐ[angleMeasure] g) (b : ℕ)
    (hdg : (d : ℝ → ℝ) =ᵐ[angleMeasure] iteratedDeriv b g) (n : ℤ) :
    circleFourierTransform d n =
      (2 * Complex.I * (n : ℂ)) ^ b * circleFourierTransform f n := by
  have hc : circleFourierCoeff d n =
      (2 * Complex.I * (n : ℂ)) ^ b * circleFourierCoeff f n :=
    (congrFun (circleFourierCoeff_congr_ae hdg) n).trans
      ((circleFourierCoeff_iteratedDeriv hg hp b n).trans
        (congrArg ((2 * Complex.I * (n : ℂ)) ^ b * ·)
          (congrFun (circleFourierCoeff_congr_ae hfg) n).symm))
  rw [circleFourierTransform_apply, circleFourierTransform_apply, hc]
  simp only [Complex.real_smul]
  ring

theorem circleBandJet_eq_band_derivative (M : ℝ) (hM : 1 ≤ M) (k : ℕ)
    {f d : AngleL2} {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hp : Function.Periodic g Real.pi)
    (hfg : (f : ℝ → ℝ) =ᵐ[angleMeasure] g) (b : ℕ)
    (hdg : (d : ℝ → ℝ) =ᵐ[angleMeasure] iteratedDeriv b g) :
    circleBandJet M hM k b f = circleBandJet M hM k 0 d := by
  apply circleFourierTransform.injective
  apply lp.ext
  funext n
  rw [circleBandJet_transform_apply, circleBandJet_transform_apply,
    circleFourierTransform_derivative hg hp hfg b hdg n]
  simp only [pow_zero, one_mul]

theorem circleBandJet_hasSum_derivative (M : ℝ) (hM : 1 ≤ M)
    {f d : AngleL2} {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hp : Function.Periodic g Real.pi)
    (hfg : (f : ℝ → ℝ) =ᵐ[angleMeasure] g) (b : ℕ)
    (hdg : (d : ℝ → ℝ) =ᵐ[angleMeasure] iteratedDeriv b g) :
    HasSum (fun k : ℕ => circleBandJet M hM k b f) d :=
  (circleBandJet_hasSum_zero M hM d).congr_fun
    (fun k => circleBandJet_eq_band_derivative M hM k hg hp hfg b hdg)

end ContinuousFlexibility.Statements
