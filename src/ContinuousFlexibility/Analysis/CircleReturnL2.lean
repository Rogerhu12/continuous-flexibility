import ContinuousFlexibility.Analysis.CircleReturnFourier
import ContinuousFlexibility.Analysis.CircleReturnSeries
import ContinuousFlexibility.Analysis.CircleJetClosedGraph

/-!
# Quantitative estimates for the actual circle Fourier coefficients

The constants in this file are norms of fixed tests and one convergent
numerical series.  They are independent of the circle, its travel angle,
the input function, and the derivative order.  Integration by parts followed
by the actual angular L² pairing gives a fixed loss of three derivatives.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory Statements
open scoped ContDiff RealInnerProductSpace

private theorem circle_one_memLp : MemLp (fun _ : ℝ => (1 : ℝ)) 2 angleMeasure :=
  memLp_angleMeasure_of_continuous continuous_const

/-- The norm of the constant-one test on the actual angular interval. -/
def circleAngleOneNorm : ℝ := ‖circle_one_memLp.toLp (fun _ : ℝ => (1 : ℝ))‖

theorem circleAngleOneNorm_nonneg : 0 ≤ circleAngleOneNorm := norm_nonneg _

/-- The L¹ norm is controlled by the actual angular L² norm.  Using the
fixed L² test avoids any convention about normalized angular measure. -/
theorem integral_circle_norm_le_angleL2 {g : ℝ → ℂ} (hg : Continuous g) :
    (∫ x, ‖g x‖ ∂angleMeasure) ≤
      circleAngleOneNorm * (eLpNorm g 2 angleMeasure).toReal := by
  have hn := memLp_angleMeasure_of_continuous hg.norm
  have heq : angleL2TestPairing (fun _ : ℝ => (1 : ℝ)) circle_one_memLp
      (hn.toLp (fun x => ‖g x‖)) = ∫ x, ‖g x‖ ∂angleMeasure := by
    rw [angleL2TestPairing_apply]
    apply integral_congr_ae
    filter_upwards [MemLp.coeFn_toLp hn] with x hx
    rw [hx, mul_one]
  have hbound := norm_inner_le_norm (𝕜 := ℝ)
    (circle_one_memLp.toLp (fun _ : ℝ => (1 : ℝ))) (hn.toLp (fun x => ‖g x‖))
  change ‖angleL2TestPairing (fun _ : ℝ => (1 : ℝ)) circle_one_memLp
      (hn.toLp (fun x => ‖g x‖))‖ ≤
      circleAngleOneNorm * ‖hn.toLp (fun x => ‖g x‖)‖ at hbound
  rw [heq, Lp.norm_toLp (fun x => ‖g x‖) hn,
    eLpNorm_norm g hg.aestronglyMeasurable] at hbound
  exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hbound)

/-- Normalization constant for an integral coefficient of a pi-periodic
function, measured in the repository's unnormalized angular L² norm. -/
def circleFourierL2Constant : ℝ := Real.pi⁻¹ * circleAngleOneNorm

theorem circleFourierL2Constant_nonneg : 0 ≤ circleFourierL2Constant :=
  mul_nonneg (inv_nonneg.mpr Real.pi_pos.le) circleAngleOneNorm_nonneg

theorem norm_circleFourierCoeff_le_integral_norm (g : ℝ → ℂ) (n : ℤ) :
    ‖circleFourierCoeff g n‖ ≤
      (1 / (2 * Real.pi)) * ∫ x in (0 : ℝ)..2 * Real.pi, ‖g x‖ := by
  rw [circleFourierCoeff_eq_integral, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * Real.pi))]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    _ ≤ ∫ x in (0 : ℝ)..2 * Real.pi,
        ‖fourier (-n) (x : AddCircle (2 * Real.pi)) • g x‖ :=
      intervalIntegral.norm_integral_le_integral_norm (by positivity)
    _ = _ := by simp only [norm_smul, fourier_apply, Circle.norm_coe, one_mul]

/-- Every integral Fourier coefficient is bounded by the same actual L²
norm.  Period pi converts the full Fourier integration interval to the
single angular interval used by the physical spaces. -/
theorem norm_circleFourierCoeff_le_angleL2 {g : ℝ → ℂ}
    (hg : Continuous g) (hp : Function.Periodic g Real.pi) (n : ℤ) :
    ‖circleFourierCoeff g n‖ ≤
      circleFourierL2Constant * (eLpNorm g 2 angleMeasure).toReal := by
  have hpn : Function.Periodic (fun x => ‖g x‖) Real.pi :=
    fun x => congrArg norm (hp x)
  calc
    _ ≤ (1 / (2 * Real.pi)) * ∫ x in (0 : ℝ)..2 * Real.pi, ‖g x‖ :=
      norm_circleFourierCoeff_le_integral_norm g n
    _ = Real.pi⁻¹ * ∫ x, ‖g x‖ ∂angleMeasure := by
      rw [circle_integral_two_pi hg.norm hpn,
        intervalIntegral.integral_of_le Real.pi_pos.le]
      change (1 / (2 * Real.pi)) * (2 * ∫ x, ‖g x‖ ∂angleMeasure) = _
      field_simp [Real.pi_ne_zero] <;> ring
    _ ≤ Real.pi⁻¹ *
        (circleAngleOneNorm * (eLpNorm g 2 angleMeasure).toReal) :=
      mul_le_mul_of_nonneg_left (integral_circle_norm_le_angleL2 hg)
        (inv_nonneg.mpr Real.pi_pos.le)
    _ = _ := by rw [circleFourierL2Constant, mul_assoc]

/-- Complexification commutes with every ordinary derivative of an
actual smooth real function. -/
theorem circle_iteratedDeriv_ofReal {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (k : ℕ) :
    iteratedDeriv k (fun x => (f x : ℂ)) =
      fun x => Complex.ofReal (iteratedDeriv k f x) := by
  induction k with
  | zero => simp only [iteratedDeriv_zero]
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    have hd := (hf.differentiable_iteratedDeriv k
      (ENat.natCast_lt_of_coe_top_le_withTop le_rfl k) x).hasDerivAt
    have h := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt x hd
    simpa only [Function.comp_def, iteratedDeriv_succ] using h.deriv

private theorem circle_periodic_two_pi {E : Type*} {f : ℝ → E}
    (hp : Function.Periodic f Real.pi) : Function.Periodic f (2 * Real.pi) := by
  intro x
  calc
    f (x + 2 * Real.pi) = f ((x + Real.pi) + Real.pi) := by congr 1; ring
    _ = f (x + Real.pi) := hp (x + Real.pi)
    _ = f x := hp x

/-- Integration by parts turns every positive-frequency derivative
moment into a single actual L² derivative norm. -/
theorem circleFourierCoeff_moment_le_angleL2 {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f Real.pi)
    (k : ℕ) {n : ℤ} (hn : n ≠ 0) :
    ‖circleFourierCoeff (fun x => (f x : ℂ)) n‖ * ‖(n : ℂ)‖ ^ k ≤
      circleFourierL2Constant * (eLpNorm (iteratedDeriv k f) 2 angleMeasure).toReal := by
  have hc : ContDiff ℝ ∞ (fun x => (f x : ℂ)) := Complex.ofRealCLM.contDiff.comp hf
  have hpc : Function.Periodic (fun x => (f x : ℂ)) Real.pi :=
    fun x => congrArg Complex.ofReal (hp x)
  have hd : Continuous (iteratedDeriv k f) := hf.continuous_iteratedDeriv k (by simp)
  have hdc : Continuous (fun x => Complex.ofReal (iteratedDeriv k f x)) :=
    Complex.continuous_ofReal.comp hd
  have hdp : Function.Periodic (fun x => Complex.ofReal (iteratedDeriv k f x)) Real.pi := by
    rw [← circle_iteratedDeriv_ofReal hf k]
    exact circlePeriodic_iteratedDeriv hpc k
  have hnorm : eLpNorm (fun x => Complex.ofReal (iteratedDeriv k f x)) 2 angleMeasure =
      eLpNorm (iteratedDeriv k f) 2 angleMeasure :=
    eLpNorm_congr_norm_ae hdc.aestronglyMeasurable hd.aestronglyMeasurable
      (Eventually.of_forall fun x => Complex.norm_real _)
  rw [← norm_circleFourierCoeff_iteratedDeriv hc (circle_periodic_two_pi hpc) k hn,
    circle_iteratedDeriv_ofReal hf k]
  simpa only [hnorm] using norm_circleFourierCoeff_le_angleL2 hdc hdp n

/-- Pairing the positive and negative frequencies costs exactly the
factor two in the coefficient bound. -/
theorem circleCosineCoeff_moment_le_angleL2 {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f Real.pi)
    (k : ℕ) {j : ℕ} (hj : j ≠ 0) :
    |circleCosineCoeff f j| * (j : ℝ) ^ k ≤
      2 * circleFourierL2Constant * (eLpNorm (iteratedDeriv k f) 2 angleMeasure).toReal := by
  have hjz : (j : ℤ) ≠ 0 := by exact_mod_cast hj
  have hpos := circleFourierCoeff_moment_le_angleL2 hf hp k hjz
  have hneg := circleFourierCoeff_moment_le_angleL2 hf hp k (neg_ne_zero.mpr hjz)
  simp only [Int.cast_natCast, Int.cast_neg, norm_neg, Complex.norm_natCast] at hpos hneg
  have habs : |circleCosineCoeff f j| ≤
      ‖circleFourierCoeff (fun x => (f x : ℂ)) (j : ℤ)‖ +
      ‖circleFourierCoeff (fun x => (f x : ℂ)) (-(j : ℤ))‖ := by
    exact (abs_add_le _ _).trans
      (add_le_add (Complex.abs_re_le_norm _) (Complex.abs_re_le_norm _))
  calc
    _ ≤ (‖circleFourierCoeff (fun x => (f x : ℂ)) (j : ℤ)‖ +
        ‖circleFourierCoeff (fun x => (f x : ℂ)) (-(j : ℤ))‖) * (j : ℝ) ^ k :=
      mul_le_mul_of_nonneg_right habs (pow_nonneg (Nat.cast_nonneg j) k)
    _ = ‖circleFourierCoeff (fun x => (f x : ℂ)) (j : ℤ)‖ * (j : ℝ) ^ k +
        ‖circleFourierCoeff (fun x => (f x : ℂ)) (-(j : ℤ))‖ * (j : ℝ) ^ k := by ring
    _ ≤ _ := (add_le_add hpos hneg).trans_eq (by ring)

/-- A fixed numerical constant; no value of the convergent reciprocal
square series is required by the inverse estimate. -/
def circleFourierMomentConstant : ℝ :=
  2 * circleFourierL2Constant * ∑' j : ℕ, 1 / (j : ℝ) ^ 2

theorem circleFourierMomentConstant_nonneg : 0 ≤ circleFourierMomentConstant := by
  unfold circleFourierMomentConstant
  exact mul_nonneg (mul_nonneg (by norm_num) circleFourierL2Constant_nonneg)
    (tsum_nonneg fun j => by positivity)

/-- One coefficient moment for the inverse is controlled by three
additional actual angular derivatives, with a constant independent of s. -/
theorem tsum_circleCosineCoeff_moment_le_angleL2 {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f Real.pi) (s : ℕ) :
    (∑' j : ℕ, |circleCosineCoeff f j| * (j : ℝ) ^ (s + 1)) ≤
      circleFourierMomentConstant *
        (eLpNorm (iteratedDeriv (s + 3) f) 2 angleMeasure).toReal := by
  let B := 2 * circleFourierL2Constant *
    (eLpNorm (iteratedDeriv (s + 3) f) 2 angleMeasure).toReal
  have hsum : Summable (fun j : ℕ => 1 / (j : ℝ) ^ 2) :=
    (Real.summable_one_div_nat_pow (p := 2)).mpr (by omega)
  have hmajor : Summable (fun j : ℕ => B * (1 / (j : ℝ) ^ 2)) := hsum.mul_left B
  have hbound (j : ℕ) : |circleCosineCoeff f j| * (j : ℝ) ^ (s + 1) ≤
      B * (1 / (j : ℝ) ^ 2) := by
    by_cases hj : j = 0
    · subst j
      simp
    · have hjp : (0 : ℝ) < j := by exact_mod_cast Nat.pos_of_ne_zero hj
      rw [mul_one_div]
      apply (le_div_iff₀ (pow_pos hjp 2)).mpr
      rw [mul_assoc, ← pow_add]
      have hexp : s + 1 + 2 = s + 3 := by omega
      rw [hexp]
      exact circleCosineCoeff_moment_le_angleL2 hf hp (s + 3) hj
  calc
    _ ≤ ∑' j : ℕ, B * (1 / (j : ℝ) ^ 2) :=
      Summable.tsum_le_tsum hbound
        (summable_circleCosineCoeff_moment hf (circle_periodic_two_pi hp) (s + 1)) hmajor
    _ = _ := by
      rw [tsum_mul_left]
      dsimp [B, circleFourierMomentConstant]
      ring

/-- Uniform derivative bounds for a convergent smooth sine series. -/
theorem abs_iteratedDeriv_circleSineSeries_le {a : ℕ → ℝ}
    (ha : ∀ k : ℕ, Summable (fun j : ℕ => |a j| * (j : ℝ) ^ k)) (s : ℕ) (θ : ℝ) :
    |iteratedDeriv s (fun x : ℝ => ∑' j : ℕ, a j * Real.sin (j * x)) θ| ≤
      ∑' j : ℕ, |a j| * (j : ℝ) ^ s := by
  have hterm : ∀ j : ℕ, ContDiff ℝ (⊤ : ℕ∞)
      (fun x : ℝ => a j * Real.sin ((j : ℝ) * x)) := by
    intro j
    simpa only [Function.comp_def, Pi.mul_apply, id_eq] using
      (contDiff_const.mul (Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)) :
        ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => a j * (Real.sin ∘ (fun y : ℝ => (j : ℝ) * id y)) x))
  rw [← Real.norm_eq_abs, ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  rw [iteratedFDeriv_tsum_apply (N := ⊤)
    (f := fun (j : ℕ) (x : ℝ) => a j * Real.sin ((j : ℝ) * x)) (k := s)
    (v := fun k j => |a j| * (j : ℝ) ^ k)
    hterm
    (fun k _ => ha k)
    (fun k j x _ => circleSineTerm_iteratedFDeriv_bound (a j) j k x)
    (by simp) θ]
  exact tsum_of_norm_bounded (ha s).hasSum
    (fun j => circleSineTerm_iteratedFDeriv_bound (a j) j s θ)

/-- The actual inverse chosen from the integral coefficients of f. -/
def circleReturnSolution (f : ℝ → ℝ) (T : ℝ) : ℝ → ℝ :=
  circleReturnInverseSeries (circlePiCosineCoeff f) T

theorem circleReturnSolution_spec {f : ℝ → ℝ} {T γ : ℝ}
    (hγ : 0 < γ)
    (hT : ∀ j : ℕ, 1 ≤ j → γ / j ≤ |Real.sin (j * T)|)
    (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f Real.pi)
    (he : Function.Even f) (hm : ∫ x in (0 : ℝ)..Real.pi, f x = 0) :
    ContDiff ℝ ∞ (circleReturnSolution f T) ∧
      Function.Periodic (circleReturnSolution f T) Real.pi ∧
      (∀ θ, circleReturnSolution f T (-θ) = -circleReturnSolution f T θ) ∧
      circleReturnShift T (circleReturnSolution f T) = f := by
  obtain ⟨hc0, hc, hceven, hseries⟩ := circlePiCosineCoeff_spec hf hp he hm
  refine ⟨contDiff_circleReturnInverseSeries hγ hT hc,
    circleReturnInverseSeries_periodic_pi hceven T,
    circleReturnInverseSeries_odd (circlePiCosineCoeff f) T, ?_⟩
  funext θ
  exact (circleReturnShift_inverseSeries hγ hT
    (by simpa only [pow_one] using hc 1) hc0 θ).trans (hseries θ).symm

/-- Half-period projection can only decrease the absolute coefficient
moment, so it preserves the same quantitative bound. -/
theorem tsum_circlePiCosineCoeff_moment_le_angleL2 {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f Real.pi)
    (he : Function.Even f) (hm : ∫ x in (0 : ℝ)..Real.pi, f x = 0) (s : ℕ) :
    (∑' j : ℕ, |circlePiCosineCoeff f j| * (j : ℝ) ^ (s + 1)) ≤
      circleFourierMomentConstant *
        (eLpNorm (iteratedDeriv (s + 3) f) 2 angleMeasure).toReal := by
  apply le_trans _ (tsum_circleCosineCoeff_moment_le_angleL2 hf hp s)
  apply Summable.tsum_le_tsum _ ((circlePiCosineCoeff_spec hf hp he hm).2.1 (s + 1))
    (summable_circleCosineCoeff_moment hf (circle_periodic_two_pi hp) (s + 1))
  intro j
  by_cases hj : Even j
  · simp only [circlePiCosineCoeff, hj, ite_true, le_refl]
  · simp only [circlePiCosineCoeff, hj, ite_false, abs_zero, zero_mul]
    positivity

/-- The inverse's genuine s-th derivative is bounded uniformly in angle
by the L² norm of the (s+3)-rd derivative of its actual input. -/
theorem abs_iteratedDeriv_circleReturnSolution_le {f : ℝ → ℝ} {T γ : ℝ}
    (hγ : 0 < γ)
    (hT : ∀ j : ℕ, 1 ≤ j → γ / j ≤ |Real.sin (j * T)|)
    (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f Real.pi)
    (he : Function.Even f) (hm : ∫ x in (0 : ℝ)..Real.pi, f x = 0)
    (s : ℕ) (θ : ℝ) :
    |iteratedDeriv s (circleReturnSolution f T) θ| ≤
      γ⁻¹ * (circleFourierMomentConstant *
        (eLpNorm (iteratedDeriv (s + 3) f) 2 angleMeasure).toReal) := by
  have hc := (circlePiCosineCoeff_spec hf hp he hm).2.1
  have ha (k : ℕ) := summable_circleReturn_divided_moment hγ hT k (hc (k + 1))
  have hsum : (∑' j : ℕ,
      |circlePiCosineCoeff f j / Real.sin (j * T)| * (j : ℝ) ^ s) ≤
      γ⁻¹ * ∑' j : ℕ, |circlePiCosineCoeff f j| * (j : ℝ) ^ (s + 1) := by
    rw [← tsum_mul_left]
    exact Summable.tsum_le_tsum (circleReturn_divided_moment_le (circlePiCosineCoeff f) hγ hT s)
      (ha s) ((hc (s + 1)).mul_left γ⁻¹)
  exact (abs_iteratedDeriv_circleSineSeries_le ha s θ).trans
    (hsum.trans (mul_le_mul_of_nonneg_left
      (tsum_circlePiCosineCoeff_moment_le_angleL2 hf hp he hm s) (inv_nonneg.mpr hγ.le)))

theorem ofReal_circleAngleOneNorm :
    ENNReal.ofReal circleAngleOneNorm = eLpNorm (fun _ : ℝ => (1 : ℝ)) 2 angleMeasure := by
  rw [circleAngleOneNorm, Lp.norm_toLp, ENNReal.ofReal_toReal circle_one_memLp.eLpNorm_ne_top]

/-- A pointwise uniform bound gives the actual angular L² bound. -/
theorem eLpNorm_angle_le_uniform {g : ℝ → ℝ} {B : ℝ}
    (hg : Continuous g) (hB : 0 ≤ B) (hb : ∀ θ, |g θ| ≤ B) :
    eLpNorm g 2 angleMeasure ≤ ENNReal.ofReal (circleAngleOneNorm * B) := by
  calc
    _ ≤ eLpNorm (fun _ : ℝ => B) 2 angleMeasure :=
      eLpNorm_mono_real hg.aestronglyMeasurable (fun θ => by simpa only [Real.norm_eq_abs] using hb θ)
    _ = ENNReal.ofReal B * eLpNorm (fun _ : ℝ => (1 : ℝ)) 2 angleMeasure := by
      rw [show (fun _ : ℝ => B) = B • (fun _ : ℝ => (1 : ℝ)) by funext x; simp,
        eLpNorm_const_smul, ← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg hB]
    _ = _ := by
      rw [← ofReal_circleAngleOneNorm, ← ENNReal.ofReal_mul hB, mul_comm B]

/-- One fixed real constant for all derivative orders of the return
inverse; the only travel-dependent factor is the reciprocal margin. -/
def circleReturnL2Constant : ℝ := circleAngleOneNorm * circleFourierMomentConstant

theorem circleReturnL2Constant_nonneg : 0 ≤ circleReturnL2Constant :=
  mul_nonneg circleAngleOneNorm_nonneg circleFourierMomentConstant_nonneg

/-- The actual function-level L² inverse estimate with fixed loss three.
This is the per-circle estimate used before summing with physical weights. -/
theorem eLpNorm_iteratedDeriv_circleReturnSolution_le {f : ℝ → ℝ} {T γ : ℝ}
    (hγ : 0 < γ)
    (hT : ∀ j : ℕ, 1 ≤ j → γ / j ≤ |Real.sin (j * T)|)
    (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f Real.pi)
    (he : Function.Even f) (hm : ∫ x in (0 : ℝ)..Real.pi, f x = 0) (s : ℕ) :
    eLpNorm (iteratedDeriv s (circleReturnSolution f T)) 2 angleMeasure ≤
      ENNReal.ofReal (circleReturnL2Constant * γ⁻¹) *
        eLpNorm (iteratedDeriv (s + 3) f) 2 angleMeasure := by
  have hvs := (circleReturnSolution_spec hγ hT hf hp he hm).1
  have hd := hvs.continuous_iteratedDeriv s (by simp)
  have hbound := abs_iteratedDeriv_circleReturnSolution_le hγ hT hf hp he hm s
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

end ContinuousFlexibility.Analysis
