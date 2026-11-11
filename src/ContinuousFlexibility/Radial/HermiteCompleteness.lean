import ContinuousFlexibility.Radial.OscillatorSpectrum
import ContinuousFlexibility.Radial.ExponentialMoments
import Mathlib.Algebra.Polynomial.Sequence

/-!
# Actual completeness of the Hermite--Gaussian family

Orthogonality to all normalized modes gives all Gaussian-weighted
polynomial moments. Exponential integrability follows from actual `L²`
and shifted Gaussian integrals. Moment uniqueness then gives almost
everywhere zero, including for genuine `Lp ℝ 2 volume` classes.
No complete-basis or closed spectral realization is a premise.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory Polynomial
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

def exponentialGaussian (j t x : ℝ) : ℝ := oscillatorGround j x * exp (t * x)

/-- Completing the square proves the actual tilted Gaussian belongs to
whole-line `L²`, for every real exponential tilt. -/
theorem memLp_exponentialGaussian {j : ℝ} (hj : 0 < j) (t : ℝ) :
    MemLp (exponentialGaussian j t) 2 volume := by
  have hc : Continuous (exponentialGaussian j t) :=
    (contDiff_oscillatorGround j).continuous.mul (continuous_const.mul continuous_id).rexp
  apply (oscillator_memLp_two_iff_integrable_sq hc.aestronglyMeasurable).mpr
  have hi := ((integrable_exp_neg_mul_sq hj).comp_sub_right (t / j)).const_mul (exp (t ^ 2 / j))
  convert hi using 1
  funext x
  unfold exponentialGaussian
  rw [mul_pow, oscillatorGround_sq]
  rw [show exp (t * x) ^ 2 = exp (t * x + t * x) by rw [pow_two, ← exp_add]]
  rw [← exp_add, ← exp_add]
  congr 1
  field_simp [hj.ne']
  ring

theorem hermitePolynomial_degree (n : ℕ) : (hermitePolynomial n).degree = n := by
  unfold hermitePolynomial
  rw [degree_map_eq_of_isUnit_leadingCoeff (Int.castRingHom ℝ)
    (by rw [Polynomial.leadingCoeff_hermite]; exact isUnit_one), Polynomial.degree_hermite]

theorem oscillatorHermitePolynomial_degree {j : ℝ} (hj : 0 < j) (n : ℕ) :
    (oscillatorHermitePolynomial j n).degree = n := by
  have hs : sqrt (2 * j) ≠ 0 := (sqrt_pos.mpr (by positivity : 0 < 2 * j)).ne'
  unfold oscillatorHermitePolynomial
  rw [degree_comp (by rw [degree_C_mul_X hs]; norm_num), hermitePolynomial_degree,
    degree_C_mul_X hs, mul_one]

def oscillatorHermiteSequence {j : ℝ} (hj : 0 < j) : Polynomial.Sequence ℝ where
  elems' := oscillatorHermitePolynomial j
  degree_eq' := oscillatorHermitePolynomial_degree hj

/-- This is algebraic spanning by the already constructed polynomials,
not an assumption of density in a function space. -/
theorem span_oscillatorHermitePolynomial {j : ℝ} (hj : 0 < j) :
    Submodule.span ℝ (Set.range (oscillatorHermitePolynomial j)) = ⊤ := by
  exact (oscillatorHermiteSequence hj).span (fun n => isUnit_iff_ne_zero.mpr
    (leadingCoeff_ne_zero.mpr ((oscillatorHermiteSequence hj).ne_zero n)))

/-- Every polynomial pairing is absolutely integrable by actual `L²`
Hölder, using the established polynomial--Gaussian `L²` membership. -/
theorem integrable_weightedGaussian_polynomial
    {j : ℝ} (hj : 0 < j) {f : ℝ → ℝ} (hf : MemLp f 2 volume) (p : ℝ[X]) :
    Integrable (fun x => f x * oscillatorGround j x * p.eval x) volume := by
  convert hf.integrable_mul (memLp_polynomialGaussian hj p) using 1
  funext x
  simp only [polynomialGaussian, Pi.mul_apply]
  ring

private def weightedPolynomialPairing
    {j : ℝ} (hj : 0 < j) {f : ℝ → ℝ} (hf : MemLp f 2 volume) : ℝ[X] →ₗ[ℝ] ℝ where
  toFun p := ∫ x : ℝ, f x * oscillatorGround j x * p.eval x
  map_add' p q := by
    rw [← integral_add (integrable_weightedGaussian_polynomial hj hf p)
      (integrable_weightedGaussian_polynomial hj hf q)]
    apply integral_congr_ae
    filter_upwards with x
    simp only [eval_add]
    ring
  map_smul' c p := by
    change (∫ x : ℝ, f x * oscillatorGround j x * (c • p).eval x) =
      c * ∫ x : ℝ, f x * oscillatorGround j x * p.eval x
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    simp only [eval_smul, smul_eq_mul]
    ring

theorem weightedGaussian_polynomial_integral_eq_zero
    {j : ℝ} (hj : 0 < j) {f : ℝ → ℝ} (hf : MemLp f 2 volume)
    (horth : ∀ n : ℕ, (∫ x : ℝ, f x * normalizedOscillatorHermite j n x) = 0)
    (p : ℝ[X]) : (∫ x : ℝ, f x * oscillatorGround j x * p.eval x) = 0 := by
  have hraw : ∀ n : ℕ, (∫ x : ℝ, f x * oscillatorHermiteMode j n x) = 0 := by
    intro n
    calc
      _ = (∫ x : ℝ, f x * normalizedOscillatorHermite j n x) * oscillatorHermiteNorm j n := by
        rw [← integral_mul_const]
        apply integral_congr_ae
        filter_upwards with x
        unfold normalizedOscillatorHermite
        field_simp [(oscillatorHermiteNorm_pos hj n).ne']
      _ = 0 := by rw [horth n, zero_mul]
  let L := weightedPolynomialPairing hj hf
  have hspan : Submodule.span ℝ (Set.range (oscillatorHermitePolynomial j)) ≤ L.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨n, rfl⟩
    change (∫ x : ℝ, f x * oscillatorGround j x * (oscillatorHermitePolynomial j n).eval x) = 0
    calc
      _ = ∫ x : ℝ, f x * oscillatorHermiteMode j n x := by
        apply integral_congr_ae
        filter_upwards with x
        unfold oscillatorHermiteMode polynomialGaussian
        ring
      _ = 0 := hraw n
  rw [span_oscillatorHermitePolynomial hj] at hspan
  have hp : p ∈ L.ker := hspan (Submodule.mem_top)
  exact hp

/-- Completeness for a measurable representative, with every convergence
condition derived from its actual whole-line `L²` membership. -/
theorem normalizedHermite_total_of_measurable
    {j : ℝ} (hj : 0 < j) {f : ℝ → ℝ} (hfm : Measurable f) (hf : MemLp f 2 volume)
    (horth : ∀ n : ℕ, (∫ x : ℝ, f x * normalizedOscillatorHermite j n x) = 0) :
    f =ᵐ[volume] 0 := by
  let F : ℝ → ℝ := fun x => f x * oscillatorGround j x
  have hF : Measurable F := hfm.mul (contDiff_oscillatorGround j).continuous.measurable
  have hFi : Integrable F volume := hf.integrable_mul (memLp_oscillatorGround hj)
  have hexp : ∀ t : ℝ, Integrable (fun x => F x * exp (t * x)) volume := by
    intro t
    convert hf.integrable_mul (memLp_exponentialGaussian hj t) using 1
    funext x
    unfold F exponentialGaussian
    simp only [Pi.mul_apply]
    ring
  have hpow : ∀ n : ℕ, Integrable (fun x : ℝ => F x * x ^ n) volume := by
    intro n
    simpa only [eval_pow, eval_X] using
      integrable_weightedGaussian_polynomial hj hf ((X : ℝ[X]) ^ n)
  have hmom : ∀ n : ℕ, (∫ x : ℝ, F x * x ^ n) = 0 := by
    intro n
    simpa only [eval_pow, eval_X] using
      weightedGaussian_polynomial_integral_eq_zero hj hf horth ((X : ℝ[X]) ^ n)
  have hz := ae_eq_zero_of_exponential_moments hF hFi hexp hpow hmom
  filter_upwards [hz] with x hx
  change f x = 0
  exact (mul_eq_zero.mp hx).resolve_right (oscillatorGround_pos j x).ne'

/-- Actual `L²` completeness, independent of the chosen measurable
representative. Orthogonality is expressed by genuine Lebesgue integrals. -/
theorem normalizedHermite_total
    {j : ℝ} (hj : 0 < j) {f : ℝ → ℝ} (hf : MemLp f 2 volume)
    (horth : ∀ n : ℕ, (∫ x : ℝ, f x * normalizedOscillatorHermite j n x) = 0) :
    f =ᵐ[volume] 0 := by
  let g := hf.aestronglyMeasurable.mk f
  have hfg : f =ᵐ[volume] g := hf.aestronglyMeasurable.ae_eq_mk
  have hg : MemLp g 2 volume := (memLp_congr_ae hfg).mp hf
  have hgm : Measurable g := hf.aestronglyMeasurable.measurable_mk
  have hgo : ∀ n : ℕ, (∫ x : ℝ, g x * normalizedOscillatorHermite j n x) = 0 := by
    intro n
    calc
      _ = ∫ x : ℝ, f x * normalizedOscillatorHermite j n x := by
        apply integral_congr_ae
        filter_upwards [hfg] with x hx
        rw [hx]
      _ = 0 := horth n
  exact hfg.trans (normalizedHermite_total_of_measurable hj hgm hg hgo)

/-- The totality conclusion for genuine `L²` equivalence classes, not only
for pointwise functions or an abstract sequence space. -/
theorem normalizedHermite_complete_Lp
    {j : ℝ} (hj : 0 < j) (u : Lp ℝ 2 (volume : Measure ℝ))
    (horth : ∀ n : ℕ, (∫ x : ℝ, u x * normalizedOscillatorHermite j n x) = 0) : u = 0 :=
  Lp.eq_zero_iff_ae_eq_zero.mpr (normalizedHermite_total hj (Lp.memLp u) horth)

end ContinuousFlexibility.Radial
