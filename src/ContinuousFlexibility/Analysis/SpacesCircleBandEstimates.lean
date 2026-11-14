module

public import ContinuousFlexibility.Analysis.SpacesCircleBandOperators

/-!
# Fixed-loss circle-band analysis estimates

The two pure jets of order `s` control every band: the discrete weight
`M^s f` controls rows with large material weight, and the angular derivative
controls rows with large Fourier frequency. No derivative order depends on
the band index.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ENNReal ContDiff

theorem circleBandJet_analysis_bound (M : ℝ) (hM : 1 ≤ M) (k s : ℕ)
    (f d : AngleL2)
    (hder : ∀ n : ℤ, circleFourierTransform d n =
      (2 * Complex.I * (n : ℂ)) ^ s * circleFourierTransform f n) :
    ‖Real.exp ((s : ℝ) * (k : ℝ)) • circleBandJet M hM k 0 f‖ ≤
      ‖M ^ s • f‖ + ‖d‖ := by
  let v : lp (fun _ : ℤ => ℝ) 2 :=
    lp.toNorm (circleFourierTransform (M ^ s • f)) + lp.toNorm (circleFourierTransform d)
  have hv (n : ℤ) : ‖v n‖ =
      ‖circleFourierTransform (M ^ s • f) n‖ + ‖circleFourierTransform d n‖ := by
    change ‖‖circleFourierTransform (M ^ s • f) n‖ + ‖circleFourierTransform d n‖‖ = _
    rw [Real.norm_eq_abs, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
  have hnorm :
      ‖circleFourierTransform (Real.exp ((s : ℝ) * (k : ℝ)) • circleBandJet M hM k 0 f)‖ ≤
        ‖v‖ := by
    apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    intro n
    rw [circleFourierTransform.map_smul]
    change ‖Real.exp ((s : ℝ) * (k : ℝ)) •
      circleFourierTransform (circleBandJet M hM k 0 f) n‖ ≤ ‖v n‖
    rw [circleBandJet_transform_apply]
    by_cases hn : n ∈ circleFrequencyBand M k
    · rw [ite_eq_left hn, pow_zero, one_mul, norm_smul, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _), hv n]
      calc
        Real.exp ((s : ℝ) * (k : ℝ)) * ‖circleFourierTransform f n‖ ≤
            (M ^ s + (2 * |(n : ℝ)|) ^ s) * ‖circleFourierTransform f n‖ :=
          mul_le_mul_of_nonneg_right (circleFrequencyBand_analysis_bound hM hn s)
            (norm_nonneg _)
        _ = _ := by
          rw [circleFourierTransform.map_smul (M ^ s) f, hder n]
          simp only [lp.coeFn_smul, Pi.smul_apply, norm_smul, Real.norm_eq_abs,
            abs_of_nonneg (zero_le_one.trans hM), norm_mul, norm_pow,
            Complex.norm_two, Complex.norm_I, Complex.norm_intCast, mul_one]
          ring
    · simp only [ite_eq_right hn, smul_zero, norm_zero, norm_nonneg]
  calc
    ‖Real.exp ((s : ℝ) * (k : ℝ)) • circleBandJet M hM k 0 f‖ =
        ‖circleFourierTransform (Real.exp ((s : ℝ) * (k : ℝ)) • circleBandJet M hM k 0 f)‖ :=
      (circleFourierTransform.norm_map _).symm
    _ ≤ ‖v‖ := hnorm
    _ ≤ ‖lp.toNorm (circleFourierTransform (M ^ s • f))‖ +
        ‖lp.toNorm (circleFourierTransform d)‖ := norm_add_le _ _
    _ = ‖M ^ s • f‖ + ‖d‖ := by
      rw [lp.norm_toNorm, lp.norm_toNorm, circleFourierTransform.norm_map,
        circleFourierTransform.norm_map]

theorem circleBandJet_analysis_bound_of_smooth (M : ℝ) (hM : 1 ≤ M) (k s : ℕ)
    {f d : AngleL2} {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hp : Function.Periodic g Real.pi)
    (hfg : (f : ℝ → ℝ) =ᵐ[angleMeasure] g)
    (hdg : (d : ℝ → ℝ) =ᵐ[angleMeasure] iteratedDeriv s g) :
    ‖Real.exp ((s : ℝ) * (k : ℝ)) • circleBandJet M hM k 0 f‖ ≤
      ‖M ^ s • f‖ + ‖d‖ :=
  circleBandJet_analysis_bound M hM k s f d
    (circleFourierTransform_derivative hg hp hfg s hdg)

end ContinuousFlexibility.Statements
