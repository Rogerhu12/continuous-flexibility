import ContinuousFlexibility.Radial.OscillatorKernel
import ContinuousFlexibility.Radial.HermitePolynomial
import Mathlib.Algebra.Polynomial.Roots

/-!
# Actual Hermite--Gaussian oscillator eigenfunctions

The functions are built from mathlib's Hermite polynomials and the actual
Gaussian. Their derivative equations and `L²` conditions are proved below.
No complete basis or closed-domain spectral representation is postulated.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory Polynomial
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

def polynomialGaussian (j : ℝ) (p : ℝ[X]) (x : ℝ) : ℝ :=
  p.eval x * oscillatorGround j x

def gaussianDerivativePolynomial (j : ℝ) (p : ℝ[X]) : ℝ[X] :=
  p.derivative - C j * X * p

theorem contDiff_polynomialGaussian (j : ℝ) (p : ℝ[X]) :
    ContDiff ℝ ∞ (polynomialGaussian j p) := by
  have hp : ContDiff ℝ ∞ (fun x : ℝ => p.eval x) := by
    simpa only [Polynomial.coe_aeval_eq_eval] using p.contDiff_aeval (𝕜 := ℝ) ∞
  exact hp.mul (contDiff_oscillatorGround j)

theorem hasDerivAt_polynomialGaussian (j : ℝ) (p : ℝ[X]) (x : ℝ) :
    HasDerivAt (polynomialGaussian j p)
      (polynomialGaussian j (gaussianDerivativePolynomial j p) x) x := by
  convert (p.hasDerivAt x).mul (hasDerivAt_oscillatorGround j x) using 1
  · rfl
  · simp only [polynomialGaussian, gaussianDerivativePolynomial, eval_sub, eval_mul, eval_C, eval_X]
    ring

theorem deriv_polynomialGaussian (j : ℝ) (p : ℝ[X]) :
    deriv (polynomialGaussian j p) = polynomialGaussian j (gaussianDerivativePolynomial j p) :=
  funext (fun x => (hasDerivAt_polynomialGaussian j p x).deriv)

/-- Actual differential action on a polynomial times the Gaussian. -/
theorem oscillatorExpression_polynomialGaussian (j : ℝ) (p : ℝ[X]) (x : ℝ) :
    oscillatorExpression j (polynomialGaussian j p) x =
      (-p.derivative.derivative.eval x + 2 * j * x * p.derivative.eval x + j * p.eval x) *
        oscillatorGround j x := by
  unfold oscillatorExpression
  rw [deriv_polynomialGaussian, deriv_polynomialGaussian]
  simp only [polynomialGaussian, gaussianDerivativePolynomial, derivative_sub, derivative_mul,
    derivative_C, derivative_X, eval_sub, eval_add, eval_mul, eval_C, eval_X,
    eval_zero, eval_one]
  ring

/-- Genuine Lebesgue integrability for any polynomial times a decaying
Gaussian. This follows by finite polynomial induction from Gaussian moments. -/
theorem integrable_polynomialGaussian {j : ℝ} (hj : 0 < j) (p : ℝ[X]) :
    Integrable (polynomialGaussian j p) volume := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    convert hp.add hq using 1
    funext x
    simp only [polynomialGaussian, eval_add, Pi.add_apply]
    ring
  | monomial n a =>
    have hi := integrable_rpow_mul_exp_neg_mul_sq (b := j / 2) (by positivity)
      (s := (n : ℝ)) (by have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n; linarith)
    convert hi.const_mul a using 1
    funext x
    simp only [polynomialGaussian, eval_monomial, Real.rpow_natCast, oscillatorGround]
    have hG : exp (-(j * x ^ 2 / 2)) = exp (-(j / 2) * x ^ 2) := by congr 1; ring
    rw [hG]
    ring

theorem memLp_polynomialGaussian {j : ℝ} (hj : 0 < j) (p : ℝ[X]) :
    MemLp (polynomialGaussian j p) 2 volume := by
  apply (oscillator_memLp_two_iff_integrable_sq
    (contDiff_polynomialGaussian j p).continuous.aestronglyMeasurable).mpr
  convert integrable_polynomialGaussian (by positivity : 0 < 2 * j) (p ^ 2) using 1
  funext x
  simp only [polynomialGaussian, mul_pow, eval_pow, oscillatorGround_sq]
  unfold oscillatorGround
  congr 1
  congr 1
  ring

theorem polynomialGaussian_energyDomain {j : ℝ} (hj : 0 < j) (p : ℝ[X]) :
    OscillatorEnergyDomain (polynomialGaussian j p) := by
  refine ⟨(contDiff_polynomialGaussian j p).of_le (by simp), memLp_polynomialGaussian hj p, ?_, ?_⟩
  · rw [deriv_polynomialGaussian]
    exact memLp_polynomialGaussian hj _
  · convert memLp_polynomialGaussian hj (X * p) using 1
    funext x
    simp only [polynomialGaussian, eval_mul, eval_X]
    ring

def oscillatorHermitePolynomial (j : ℝ) (n : ℕ) : ℝ[X] :=
  (hermitePolynomial n).comp (C (sqrt (2 * j)) * X)

def oscillatorHermiteMode (j : ℝ) (n : ℕ) : ℝ → ℝ :=
  polynomialGaussian j (oscillatorHermitePolynomial j n)

theorem oscillatorHermiteMode_eq (j : ℝ) (n : ℕ) (x : ℝ) :
    oscillatorHermiteMode j n x =
      (hermitePolynomial n).eval (sqrt (2 * j) * x) * exp (-(j * x ^ 2 / 2)) := by
  simp only [oscillatorHermiteMode, oscillatorHermitePolynomial, polynomialGaussian,
    eval_comp, eval_mul, eval_C, eval_X, oscillatorGround]

theorem oscillatorHermiteMode_energyDomain {j : ℝ} (hj : 0 < j) (n : ℕ) :
    OscillatorEnergyDomain (oscillatorHermiteMode j n) :=
  polynomialGaussian_energyDomain hj _

theorem oscillatorHermiteMode_equation {j : ℝ} (hj : 0 < j) (n : ℕ) (x : ℝ) :
    oscillatorExpression j (oscillatorHermiteMode j n) x =
      j * (2 * (n : ℝ) + 1) * oscillatorHermiteMode j n x := by
  unfold oscillatorHermiteMode
  rw [oscillatorExpression_polynomialGaussian]
  simp only [oscillatorHermitePolynomial, derivative_comp, derivative_mul,
    derivative_C, derivative_X, zero_mul, zero_add, mul_one,
    eval_comp, eval_mul, eval_C, eval_X]
  rw [hermitePolynomial_differentialEquation_eval n (sqrt (2 * j) * x)]
  unfold polynomialGaussian
  simp only [eval_comp, eval_mul, eval_C, eval_X]
  have hs : sqrt (2 * j) ^ 2 = 2 * j := sq_sqrt (by positivity)
  have hs3 : sqrt (2 * j) ^ 3 = 2 * j * sqrt (2 * j) := by rw [pow_succ, hs]
  ring_nf at hs hs3 ⊢
  rw [hs, hs3]
  ring

/-- The mixed second-derivative pairing is integrable on the actual line.
The eigen-equation replaces `ψ''` by its potential and energy terms. -/
theorem integrable_mul_second_of_oscillator_eigen
    {j E : ℝ} {φ ψ : ℝ → ℝ} (hφ : OscillatorEnergyDomain φ)
    (hψ : OscillatorEnergyDomain ψ)
    (heq : ∀ x, oscillatorExpression j ψ x = E * ψ x) :
    Integrable (fun x => φ x * deriv (deriv ψ) x) volume := by
  have hm := hφ.2.2.2.integrable_mul hψ.2.2.2
  have hn := hφ.2.1.integrable_mul hψ.2.1
  convert (hm.const_mul (j ^ 2)).sub (hn.const_mul E) using 1
  funext x
  have he := heq x
  unfold oscillatorExpression at he
  simp only [Pi.sub_apply, Pi.mul_apply]
  linear_combination -(φ x) * he

/-- Genuine `L²` orthogonality of distinct eigenvalues, proved using
whole-line integration by parts. The hypotheses imply integrability of
every pairing and remove endpoint terms; no formal symmetry is postulated. -/
theorem oscillator_eigen_orthogonal
    {j E F : ℝ} {φ ψ : ℝ → ℝ}
    (hφ : OscillatorEnergyDomain φ) (hψ : OscillatorEnergyDomain ψ)
    (hE : ∀ x, oscillatorExpression j φ x = E * φ x)
    (hF : ∀ x, oscillatorExpression j ψ x = F * ψ x) (hEF : E ≠ F) :
    (∫ x : ℝ, φ x * ψ x) = 0 := by
  have hφψ := integrable_mul_second_of_oscillator_eigen hφ hψ hF
  have hψφ := integrable_mul_second_of_oscillator_eigen hψ hφ hE
  have hI := integral_mul_deriv_eq_deriv_mul_of_integrable
    (fun x _ => (hφ.1.differentiable (by norm_num) x).hasDerivAt)
    (fun x _ => (hψ.1.differentiable_deriv_two x).hasDerivAt)
    hφψ (hφ.2.2.1.integrable_mul hψ.2.2.1) (hφ.2.1.integrable_mul hψ.2.2.1)
  have hJ := integral_mul_deriv_eq_deriv_mul_of_integrable
    (fun x _ => (hψ.1.differentiable (by norm_num) x).hasDerivAt)
    (fun x _ => (hφ.1.differentiable_deriv_two x).hasDerivAt)
    hψφ (hψ.2.2.1.integrable_mul hφ.2.2.1) (hψ.2.1.integrable_mul hφ.2.2.1)
  have hs : (∫ x : ℝ, φ x * deriv (deriv ψ) x) = ∫ x : ℝ, ψ x * deriv (deriv φ) x := by
    rw [hI, hJ]
    congr 1
    apply integral_congr_ae
    filter_upwards with x
    ring
  have hz : (∫ x : ℝ, φ x * deriv (deriv ψ) x - ψ x * deriv (deriv φ) x) = 0 := by
    rw [integral_sub hφψ hψφ, hs, sub_self]
  have hp : ∀ x, φ x * deriv (deriv ψ) x - ψ x * deriv (deriv φ) x =
      (E - F) * (φ x * ψ x) := by
    intro x
    have he := hE x
    have hf := hF x
    unfold oscillatorExpression at he hf
    linear_combination (ψ x) * he - (φ x) * hf
  have hc : (E - F) * (∫ x : ℝ, φ x * ψ x) = 0 := by
    rw [← integral_const_mul]
    calc
      _ = ∫ x : ℝ, φ x * deriv (deriv ψ) x - ψ x * deriv (deriv φ) x := by
        apply integral_congr_ae
        exact Eventually.of_forall (fun x => (hp x).symm)
      _ = 0 := hz
  exact (mul_eq_zero.mp hc).resolve_left (sub_ne_zero.mpr hEF)

theorem oscillatorHermiteMode_orthogonal
    {j : ℝ} (hj : 0 < j) {m n : ℕ} (hmn : m ≠ n) :
    (∫ x : ℝ, oscillatorHermiteMode j m x * oscillatorHermiteMode j n x) = 0 := by
  apply oscillator_eigen_orthogonal (oscillatorHermiteMode_energyDomain hj m)
    (oscillatorHermiteMode_energyDomain hj n)
    (oscillatorHermiteMode_equation hj m) (oscillatorHermiteMode_equation hj n)
  intro heq
  have hh := mul_left_cancel₀ hj.ne' heq
  apply hmn
  exact Nat.cast_injective (by linarith : (m : ℝ) = n)

theorem oscillatorHermiteMode_nonzero {j : ℝ} (hj : 0 < j) (n : ℕ) :
    ∃ x : ℝ, oscillatorHermiteMode j n x ≠ 0 := by
  classical
  by_contra h
  have hz : ∀ x, oscillatorHermiteMode j n x = 0 := by
    intro x
    by_contra hx
    exact h ⟨x, hx⟩
  have hs : sqrt (2 * j) ≠ 0 := (sqrt_pos.mpr (by positivity : 0 < 2 * j)).ne'
  have hp : hermitePolynomial n = 0 := by
    apply Polynomial.funext
    intro y
    have hy := hz (y / sqrt (2 * j))
    rw [oscillatorHermiteMode_eq] at hy
    have harg : sqrt (2 * j) * (y / sqrt (2 * j)) = y := by field_simp
    rw [harg] at hy
    have he := (mul_eq_zero.mp hy).resolve_right (exp_pos _).ne'
    simpa only [eval_zero] using he
  exact hermitePolynomial_ne_zero n hp

theorem oscillatorHermiteMode_sqIntegral_pos {j : ℝ} (hj : 0 < j) (n : ℕ) :
    0 < ∫ x : ℝ, oscillatorHermiteMode j n x ^ 2 := by
  obtain ⟨x, hx⟩ := oscillatorHermiteMode_nonzero hj n
  have hE := oscillatorHermiteMode_energyDomain hj n
  apply integral_pos_of_integrable_nonneg_nonzero (hE.1.continuous.pow 2)
    ((oscillator_memLp_two_iff_integrable_sq hE.1.continuous.aestronglyMeasurable).mp hE.2.1)
    (fun y => sq_nonneg _) (pow_ne_zero 2 hx)

/-- The normalization is the square root of the proved positive, finite
actual `L²` integral. No norm formula or orthogonality is a definition. -/
def oscillatorHermiteNorm (j : ℝ) (n : ℕ) : ℝ :=
  sqrt (∫ x : ℝ, oscillatorHermiteMode j n x ^ 2)

def normalizedOscillatorHermite (j : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  oscillatorHermiteMode j n x / oscillatorHermiteNorm j n

theorem oscillatorHermiteNorm_pos {j : ℝ} (hj : 0 < j) (n : ℕ) :
    0 < oscillatorHermiteNorm j n :=
  sqrt_pos.mpr (oscillatorHermiteMode_sqIntegral_pos hj n)

theorem oscillatorHermiteNorm_sq {j : ℝ} (hj : 0 < j) (n : ℕ) :
    oscillatorHermiteNorm j n ^ 2 = ∫ x : ℝ, oscillatorHermiteMode j n x ^ 2 :=
  sq_sqrt (oscillatorHermiteMode_sqIntegral_pos hj n).le

theorem normalizedOscillatorHermite_energyDomain {j : ℝ} (hj : 0 < j) (n : ℕ) :
    OscillatorEnergyDomain (normalizedOscillatorHermite j n) := by
  convert oscillatorEnergyDomain_const_mul (oscillatorHermiteMode_energyDomain hj n)
    (oscillatorHermiteNorm j n)⁻¹ using 1
  funext x
  simp only [normalizedOscillatorHermite, div_eq_mul_inv]
  ring

theorem normalizedOscillatorHermite_equation {j : ℝ} (hj : 0 < j) (n : ℕ) (x : ℝ) :
    oscillatorExpression j (normalizedOscillatorHermite j n) x =
      j * (2 * (n : ℝ) + 1) * normalizedOscillatorHermite j n x := by
  have hf : normalizedOscillatorHermite j n =
      fun y => (oscillatorHermiteNorm j n)⁻¹ * oscillatorHermiteMode j n y := by
    funext y
    simp only [normalizedOscillatorHermite, div_eq_mul_inv]
    ring
  rw [hf, oscillatorExpression_const_mul (oscillatorHermiteMode_energyDomain hj n).1,
    oscillatorHermiteMode_equation hj n x]
  ring

/-- Normalized Hermite--Gaussian functions have the genuine whole-line
`L²` pairing `δ_mn`. This is an orthonormal family, not yet a complete basis. -/
theorem integral_normalizedOscillatorHermite_mul
    {j : ℝ} (hj : 0 < j) (m n : ℕ) :
    (∫ x : ℝ, normalizedOscillatorHermite j m x * normalizedOscillatorHermite j n x) =
      if m = n then 1 else 0 := by
  have hchange : (∫ x : ℝ,
      normalizedOscillatorHermite j m x * normalizedOscillatorHermite j n x) =
      (∫ x : ℝ, oscillatorHermiteMode j m x * oscillatorHermiteMode j n x) /
        (oscillatorHermiteNorm j m * oscillatorHermiteNorm j n) := by
    calc
      _ = ∫ x : ℝ, (oscillatorHermiteMode j m x * oscillatorHermiteMode j n x) /
          (oscillatorHermiteNorm j m * oscillatorHermiteNorm j n) := by
        apply integral_congr_ae
        filter_upwards with x
        simp only [normalizedOscillatorHermite, div_mul_div_comm]
      _ = _ := integral_div _ _
  rw [hchange]
  by_cases hmn : m = n
  · subst n
    rw [ite_eq_left rfl]
    have hsame : (∫ x : ℝ, oscillatorHermiteMode j m x * oscillatorHermiteMode j m x) =
        ∫ x : ℝ, oscillatorHermiteMode j m x ^ 2 := by
      congr 1
      funext x
      ring
    rw [hsame, ← pow_two, oscillatorHermiteNorm_sq hj m]
    exact div_self (oscillatorHermiteMode_sqIntegral_pos hj m).ne'
  · rw [ite_eq_right hmn, oscillatorHermiteMode_orthogonal hj hmn, zero_div]

/-- The constructed normalized modes realize the actual central spectral
levels. Completeness and a closed operator realization are not inferred
from the existence of these eigenfunctions. -/
theorem central_normalizedHermite_equation
    {j : ℝ} (hj : 0 < j) (n : ℕ) (x : ℝ) :
    liouvilleSchrodinger (j ^ 2) centralRadius centralDensityRoot
      (normalizedOscillatorHermite j n) x =
      (j * (2 * (n : ℝ) + 1) + centralRadiusA ^ 2 - j ^ 2 * centralOscillatorA) *
        normalizedOscillatorHermite j n x := by
  rw [central_liouvilleSchrodinger]
  have he := normalizedOscillatorHermite_equation hj n x
  unfold oscillatorExpression at he
  linear_combination he

end ContinuousFlexibility.Radial
