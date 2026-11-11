import ContinuousFlexibility.Analysis.CircleReturnL2
import ContinuousFlexibility.Analysis.CircleReturnSmoothInverse

/-!
# The canonical return inverse on the full smooth circle space

The inverse is defined on every smooth pi-periodic input.  Its coefficients
are the actual integral coefficients, so addition and scalar multiplication
hold on this full domain.  The inverse identities specialize to the smooth
odd domain and the smooth even zero-mean target.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory Statements
open scoped ContDiff

theorem circleFourierCoeff_add {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g)
    (n : ℤ) :
    circleFourierCoeff (f + g) n = circleFourierCoeff f n + circleFourierCoeff g n := by
  have hphase : Continuous (fun x : ℝ => fourier (-n) (x : AddCircle (2 * Real.pi))) := by
    simp_rw [circleFourier_phase]
    fun_prop
  simp only [circleFourierCoeff_eq_integral, Pi.add_apply, smul_add]
  rw [intervalIntegral.integral_add
    ((hphase.smul hf).intervalIntegrable _ _) ((hphase.smul hg).intervalIntegrable _ _),
    smul_add]

theorem circleFourierCoeff_const_mul (f : ℝ → ℂ) (c : ℂ) (n : ℤ) :
    circleFourierCoeff (fun x => c * f x) n = c * circleFourierCoeff f n :=
  fourierCoeffOn.const_mul f c n (by positivity : (0 : ℝ) < 2 * Real.pi)

theorem circleCosineCoeff_add {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (j : ℕ) :
    circleCosineCoeff (f + g) j = circleCosineCoeff f j + circleCosineCoeff g j := by
  have hfc := Complex.continuous_ofReal.comp hf
  have hgc := Complex.continuous_ofReal.comp hg
  simp only [circleCosineCoeff, Pi.add_apply, Complex.ofReal_add,
    circleFourierCoeff_add hfc hgc, Complex.add_re]
  ring

theorem circleCosineCoeff_smul (f : ℝ → ℝ) (c : ℝ) (j : ℕ) :
    circleCosineCoeff (c • f) j = c * circleCosineCoeff f j := by
  simp only [circleCosineCoeff, Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul,
    circleFourierCoeff_const_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  ring

theorem circlePiCosineCoeff_add {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (j : ℕ) :
    circlePiCosineCoeff (f + g) j = circlePiCosineCoeff f j + circlePiCosineCoeff g j := by
  by_cases hj : Even j <;> simp [circlePiCosineCoeff, hj, circleCosineCoeff_add hf hg]

theorem circlePiCosineCoeff_smul (f : ℝ → ℝ) (c : ℝ) (j : ℕ) :
    circlePiCosineCoeff (c • f) j = c * circlePiCosineCoeff f j := by
  by_cases hj : Even j <;> simp [circlePiCosineCoeff, hj, circleCosineCoeff_smul]

private theorem circle_periodic_two_pi_linear {E : Type*} {f : ℝ → E}
    (hp : Function.Periodic f Real.pi) : Function.Periodic f (2 * Real.pi) := by
  intro x
  calc
    f (x + 2 * Real.pi) = f ((x + Real.pi) + Real.pi) := by congr 1; ring
    _ = f (x + Real.pi) := hp (x + Real.pi)
    _ = f x := hp x

/-- Rapid moments hold on the full smooth periodic domain, including
functions with a nonzero mean or without a parity assumption. -/
theorem summable_circlePiCosineCoeff_moment {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f Real.pi) (s : ℕ) :
    Summable (fun j : ℕ => |circlePiCosineCoeff f j| * (j : ℝ) ^ s) := by
  apply Summable.of_nonneg_of_le
    (g := fun j : ℕ => |circlePiCosineCoeff f j| * (j : ℝ) ^ s)
    (f := fun j : ℕ => |circleCosineCoeff f j| * (j : ℝ) ^ s)
    (fun j => mul_nonneg (abs_nonneg _) (pow_nonneg (Nat.cast_nonneg j) s)) ?_
    (summable_circleCosineCoeff_moment hf (circle_periodic_two_pi_linear hp) s)
  intro j
  by_cases hj : Even j
  · simp only [circlePiCosineCoeff, hj, ite_true, le_refl]
  · simp only [circlePiCosineCoeff, hj, ite_false, abs_zero, zero_mul]
    positivity

theorem circlePiCosineCoeff_support (f : ℝ → ℝ) (j : ℕ)
    (hj : circlePiCosineCoeff f j ≠ 0) : Even j := by
  by_contra hodd
  exact hj (if_neg hodd)

theorem contDiff_circleReturnSolution {f : ℝ → ℝ} {T γ : ℝ}
    (hγ : 0 < γ)
    (hT : ∀ j : ℕ, 1 ≤ j → γ / j ≤ |Real.sin (j * T)|)
    (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f Real.pi) :
    ContDiff ℝ ∞ (circleReturnSolution f T) :=
  contDiff_circleReturnInverseSeries hγ hT (summable_circlePiCosineCoeff_moment hf hp)

theorem periodic_circleReturnSolution (f : ℝ → ℝ) (T : ℝ) :
    Function.Periodic (circleReturnSolution f T) Real.pi :=
  circleReturnInverseSeries_periodic_pi (circlePiCosineCoeff_support f) T

theorem odd_circleReturnSolution (f : ℝ → ℝ) (T θ : ℝ) :
    circleReturnSolution f T (-θ) = -circleReturnSolution f T θ :=
  circleReturnInverseSeries_odd (circlePiCosineCoeff f) T θ

theorem summable_circleReturnSolution_terms {f : ℝ → ℝ} {T γ : ℝ}
    (hγ : 0 < γ)
    (hT : ∀ j : ℕ, 1 ≤ j → γ / j ≤ |Real.sin (j * T)|)
    (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f Real.pi) (θ : ℝ) :
    Summable (fun j : ℕ => circlePiCosineCoeff f j / Real.sin (j * T) * Real.sin (j * θ)) := by
  apply summable_circleSineTerms
  simpa only [pow_zero, mul_one, zero_add] using
    summable_circleReturn_divided_moment hγ hT 0 (summable_circlePiCosineCoeff_moment hf hp 1)

/-- Additivity of the actual inverse on all smooth pi-periodic inputs. -/
theorem circleReturnSolution_add {f g : ℝ → ℝ} {T γ : ℝ}
    (hγ : 0 < γ)
    (hT : ∀ j : ℕ, 1 ≤ j → γ / j ≤ |Real.sin (j * T)|)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hfp : Function.Periodic f Real.pi) (hgp : Function.Periodic g Real.pi) :
    circleReturnSolution (f + g) T = circleReturnSolution f T + circleReturnSolution g T := by
  funext θ
  change (∑' j : ℕ, circlePiCosineCoeff (f + g) j / Real.sin (j * T) * Real.sin (j * θ)) =
    (∑' j : ℕ, circlePiCosineCoeff f j / Real.sin (j * T) * Real.sin (j * θ)) +
    (∑' j : ℕ, circlePiCosineCoeff g j / Real.sin (j * T) * Real.sin (j * θ))
  rw [← (summable_circleReturnSolution_terms hγ hT hf hfp θ).tsum_add
    (summable_circleReturnSolution_terms hγ hT hg hgp θ)]
  apply tsum_congr
  intro j
  rw [circlePiCosineCoeff_add hf.continuous hg.continuous, add_div, add_mul]

/-- Scalar compatibility holds for the canonical formula itself. -/
theorem circleReturnSolution_smul (f : ℝ → ℝ) (T c : ℝ) :
    circleReturnSolution (c • f) T = c • circleReturnSolution f T := by
  funext θ
  change (∑' j : ℕ, circlePiCosineCoeff (c • f) j / Real.sin (j * T) * Real.sin (j * θ)) =
    c * ∑' j : ℕ, circlePiCosineCoeff f j / Real.sin (j * T) * Real.sin (j * θ)
  simp_rw [circlePiCosineCoeff_smul, mul_div_assoc, mul_assoc]
  rw [tsum_mul_left]

theorem circleReturnSolution_zero (T : ℝ) : circleReturnSolution 0 T = 0 := by
  simpa using circleReturnSolution_smul (0 : ℝ → ℝ) T 0

/-- The full-domain inverse has the same fixed derivative-loss bound.
The zero Fourier mode of the input is automatically killed by the inverse
formula, so no mean-zero assumption is needed here. -/
theorem tsum_circlePiCosineCoeff_moment_le_angleL2_all {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f Real.pi) (s : ℕ) :
    (∑' j : ℕ, |circlePiCosineCoeff f j| * (j : ℝ) ^ (s + 1)) ≤
      circleFourierMomentConstant *
        (eLpNorm (iteratedDeriv (s + 3) f) 2 angleMeasure).toReal := by
  apply le_trans _ (tsum_circleCosineCoeff_moment_le_angleL2 hf hp s)
  apply tsum_le_tsum _ (summable_circlePiCosineCoeff_moment hf hp (s + 1))
    (summable_circleCosineCoeff_moment hf (circle_periodic_two_pi_linear hp) (s + 1))
  intro j
  by_cases hj : Even j
  · simp only [circlePiCosineCoeff, hj, ite_true, le_refl]
  · simp only [circlePiCosineCoeff, hj, ite_false, abs_zero, zero_mul]
    positivity

theorem abs_iteratedDeriv_circleReturnSolution_le_all {f : ℝ → ℝ} {T γ : ℝ}
    (hγ : 0 < γ)
    (hT : ∀ j : ℕ, 1 ≤ j → γ / j ≤ |Real.sin (j * T)|)
    (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f Real.pi) (s : ℕ) (θ : ℝ) :
    |iteratedDeriv s (circleReturnSolution f T) θ| ≤
      γ⁻¹ * (circleFourierMomentConstant *
        (eLpNorm (iteratedDeriv (s + 3) f) 2 angleMeasure).toReal) := by
  have hc := summable_circlePiCosineCoeff_moment hf hp
  have ha (k : ℕ) := summable_circleReturn_divided_moment hγ hT k (hc (k + 1))
  have hsum : (∑' j : ℕ,
      |circlePiCosineCoeff f j / Real.sin (j * T)| * (j : ℝ) ^ s) ≤
      γ⁻¹ * ∑' j : ℕ, |circlePiCosineCoeff f j| * (j : ℝ) ^ (s + 1) := by
    rw [← tsum_mul_left]
    exact tsum_le_tsum (circleReturn_divided_moment_le (circlePiCosineCoeff f) hγ hT s)
      (ha s) ((hc (s + 1)).mul_left γ⁻¹)
  exact (abs_iteratedDeriv_circleSineSeries_le ha s θ).trans
    (hsum.trans (mul_le_mul_of_nonneg_left
      (tsum_circlePiCosineCoeff_moment_le_angleL2_all hf hp s) (inv_nonneg.mpr hγ.le)))

theorem eLpNorm_iteratedDeriv_circleReturnSolution_le_all {f : ℝ → ℝ} {T γ : ℝ}
    (hγ : 0 < γ)
    (hT : ∀ j : ℕ, 1 ≤ j → γ / j ≤ |Real.sin (j * T)|)
    (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f Real.pi) (s : ℕ) :
    eLpNorm (iteratedDeriv s (circleReturnSolution f T)) 2 angleMeasure ≤
      ENNReal.ofReal (circleReturnL2Constant * γ⁻¹) *
        eLpNorm (iteratedDeriv (s + 3) f) 2 angleMeasure := by
  have hd := (contDiff_circleReturnSolution hγ hT hf hp).continuous_iteratedDeriv s (by simp)
  have hbound := abs_iteratedDeriv_circleReturnSolution_le_all hγ hT hf hp s
  have hnonneg : 0 ≤ γ⁻¹ * (circleFourierMomentConstant *
      (eLpNorm (iteratedDeriv (s + 3) f) 2 angleMeasure).toReal) :=
    mul_nonneg (inv_nonneg.mpr hγ.le)
      (mul_nonneg circleFourierMomentConstant_nonneg ENNReal.toReal_nonneg)
  refine (eLpNorm_angle_le_uniform hd hnonneg hbound).trans_eq ?_
  have halgebra : circleAngleOneNorm *
      (γ⁻¹ * (circleFourierMomentConstant *
        (eLpNorm (iteratedDeriv (s + 3) f) 2 angleMeasure).toReal)) =
      (circleReturnL2Constant * γ⁻¹) *
        (eLpNorm (iteratedDeriv (s + 3) f) 2 angleMeasure).toReal := by
    unfold circleReturnL2Constant
    ring
  rw [halgebra, ENNReal.ofReal_mul
    (mul_nonneg circleReturnL2Constant_nonneg (inv_nonneg.mpr hγ.le)),
    ENNReal.ofReal_toReal (memLp_angleMeasure_iteratedDeriv_of_contDiff hf (s + 3)).eLpNorm_ne_top]

/-- The canonical inverse is a right inverse on the actual target class. -/
theorem circleReturnSolution_right_inverse {f : ℝ → ℝ} {T γ : ℝ}
    (hγ : 0 < γ)
    (hT : ∀ j : ℕ, 1 ≤ j → γ / j ≤ |Real.sin (j * T)|)
    (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f Real.pi)
    (he : Function.Even f) (hm : ∫ x in (0 : ℝ)..Real.pi, f x = 0) :
    circleReturnShift T (circleReturnSolution f T) = f :=
  (circleReturnSolution_spec hγ hT hf hp he hm).2.2.2

/-- The canonical inverse is also a left inverse on smooth odd functions,
by uniqueness for the irrational rotation difference. -/
theorem circleReturnSolution_left_inverse {v : ℝ → ℝ} {T γ : ℝ}
    (hγ : 0 < γ)
    (hT : ∀ j : ℕ, 1 ≤ j → γ / j ≤ |Real.sin (j * T)|)
    (hv : ContDiff ℝ ∞ v) (hp : Function.Periodic v Real.pi)
    (ho : ∀ θ, v (-θ) = -v θ) :
    circleReturnSolution (circleReturnShift T v) T = v := by
  obtain ⟨hfs, hfp, hfe, hfm⟩ := circleReturnShift_output_properties hv hp ho T
  have hsol := circleReturnSolution_spec hγ hT hfs hfp hfe hfm
  apply circleReturnShift_injective_on_odd hsol.1.continuous hv.continuous
    hsol.2.1 hp hsol.2.2.1 ho (irrational_travel_of_smallDivisor hγ hT)
  intro θ
  exact congrFun hsol.2.2.2 θ

end ContinuousFlexibility.Analysis
