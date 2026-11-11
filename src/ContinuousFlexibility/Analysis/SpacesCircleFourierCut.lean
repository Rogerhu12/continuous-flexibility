import ContinuousFlexibility.Analysis.SpacesCircleFourierTransform
import ContinuousFlexibility.Analysis.SpacesCircleFrequencyBands

/-!
# Bounded angular Fourier jet projections

The operators are defined by genuine smooth real Fourier polynomials. Their
bounds follow from the exact Fourier isometry and the finite spectral symbol.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ENNReal BigOperators ContDiff

/-- The smooth real polynomial obtained by retaining a finite frequency set. -/
def circleFourierCutFunction (s : Finset ℤ) (f : AngleL2) (θ : ℝ) : ℝ :=
  (circleFourierPolynomial s (circleFourierCoeff f) θ).re

theorem circleFourierCutFunction_contDiff (s : Finset ℤ) (f : AngleL2) :
    ContDiff ℝ ∞ (circleFourierCutFunction s f) :=
  Complex.reCLM.contDiff.comp (circleFourierPolynomial_contDiff s (circleFourierCoeff f))

theorem circleFourierCutFunction_periodic (s : Finset ℤ) (f : AngleL2) :
    Function.Periodic (circleFourierCutFunction s f) Real.pi := by
  intro θ
  exact congrArg Complex.re (circleFourierPolynomial_periodic s (circleFourierCoeff f) θ)

theorem circleFourierCutFunction_coeff (s : Finset ℤ)
    (hs : ∀ n : ℤ, -n ∈ s ↔ n ∈ s) (f : AngleL2) (n : ℤ) :
    circleFourierCoeff (circleFourierCutFunction s f) n =
      if n ∈ s then circleFourierCoeff f n else 0 :=
  circleFourierPolynomial_re_coeff s (circleFourierCoeff f) hs (circleFourierCoeff_neg f) n

/-- The actual `L²` class of a derivative of the retained Fourier polynomial. -/
def circleFourierJetCutFun (s : Finset ℤ) (b : ℕ) (f : AngleL2) : AngleL2 :=
  (memLp_angleMeasure_iteratedDeriv_of_contDiff (circleFourierCutFunction_contDiff s f) b).toLp
    (iteratedDeriv b (circleFourierCutFunction s f))

theorem circleFourierJetCutFun_ae (s : Finset ℤ) (b : ℕ) (f : AngleL2) :
    (circleFourierJetCutFun s b f : ℝ → ℝ) =ᵐ[angleMeasure]
      iteratedDeriv b (circleFourierCutFunction s f) :=
  MemLp.coeFn_toLp (memLp_angleMeasure_iteratedDeriv_of_contDiff
    (circleFourierCutFunction_contDiff s f) b)

theorem circleFourierJetCutFun_coeff (s : Finset ℤ)
    (hs : ∀ n : ℤ, -n ∈ s ↔ n ∈ s) (b : ℕ) (f : AngleL2) (n : ℤ) :
    circleFourierCoeff (circleFourierJetCutFun s b f) n =
      if n ∈ s then (2 * Complex.I * (n : ℂ)) ^ b * circleFourierCoeff f n else 0 := by
  calc
    circleFourierCoeff (circleFourierJetCutFun s b f) n =
        circleFourierCoeff (iteratedDeriv b (circleFourierCutFunction s f)) n :=
      congrFun (circleFourierCoeff_congr_ae (circleFourierJetCutFun_ae s b f)) n
    _ = (2 * Complex.I * (n : ℂ)) ^ b *
        circleFourierCoeff (circleFourierCutFunction s f) n :=
      circleFourierCoeff_iteratedDeriv (circleFourierCutFunction_contDiff s f)
        (circleFourierCutFunction_periodic s f) b n
    _ = _ := by
      rw [circleFourierCutFunction_coeff s hs f n, mul_ite, mul_zero]

theorem circleFourierTransform_jetCut_apply (s : Finset ℤ)
    (hs : ∀ n : ℤ, -n ∈ s ↔ n ∈ s) (b : ℕ) (f : AngleL2) (n : ℤ) :
    circleFourierTransform (circleFourierJetCutFun s b f) n =
      if n ∈ s then (2 * Complex.I * (n : ℂ)) ^ b * circleFourierTransform f n else 0 := by
  rw [circleFourierTransform_apply, circleFourierJetCutFun_coeff s hs b f n]
  by_cases hn : n ∈ s
  · simp only [ite_eq_left hn, circleFourierTransform_apply, Complex.real_smul]
    ring
  · simp only [ite_eq_right hn, smul_zero]

/-- Any bound on the retained Fourier symbol gives exactly the same `L²`
operator bound. The scalar `a` includes discrete material weights. -/
theorem circleFourierJetCutFun_weighted_norm_le (s : Finset ℤ)
    (hs : ∀ n : ℤ, -n ∈ s ↔ n ∈ s) (b : ℕ) (f : AngleL2)
    (a : ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ n ∈ s, |a| * (2 * |(n : ℝ)|) ^ b ≤ C) :
    ‖a • circleFourierJetCutFun s b f‖ ≤ C * ‖f‖ := by
  have hnorm : ‖circleFourierTransform (a • circleFourierJetCutFun s b f)‖ ≤
      ‖C • circleFourierTransform f‖ := by
    apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    intro n
    rw [circleFourierTransform.map_smul]
    change ‖a • circleFourierTransform (circleFourierJetCutFun s b f) n‖ ≤
      ‖C • circleFourierTransform f n‖
    rw [circleFourierTransform_jetCut_apply s hs b f n]
    by_cases hn : n ∈ s
    · simp only [ite_eq_left hn, norm_smul, Real.norm_eq_abs, abs_of_nonneg hC,
        norm_mul, norm_pow, Complex.norm_two, Complex.norm_I, Complex.norm_intCast, mul_one]
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_right (hbound n hn) (norm_nonneg (circleFourierTransform f n))
    · simp only [ite_eq_right hn, smul_zero, norm_zero, norm_nonneg]
  simpa only [circleFourierTransform.norm_map, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg hC] using hnorm

private def circleFourierJetCutLinear (s : Finset ℤ)
    (hs : ∀ n : ℤ, -n ∈ s ↔ n ∈ s) (b : ℕ) : AngleL2 →ₗ[ℝ] AngleL2 where
  toFun := circleFourierJetCutFun s b
  map_add' := by
    intro f g
    apply circleFourierTransform.injective
    apply lp.ext
    funext n
    rw [circleFourierTransform.map_add (circleFourierJetCutFun s b f) (circleFourierJetCutFun s b g)]
    simp only [lp.coeFn_add, Pi.add_apply]
    rw [circleFourierTransform_jetCut_apply s hs b (f + g) n]
    rw [circleFourierTransform_jetCut_apply s hs b f n,
      circleFourierTransform_jetCut_apply s hs b g n, circleFourierTransform.map_add]
    by_cases hn : n ∈ s
    · simp only [ite_eq_left hn, lp.coeFn_add, Pi.add_apply, mul_add]
    · simp only [ite_eq_right hn, add_zero]
  map_smul' := by
    intro c f
    apply circleFourierTransform.injective
    apply lp.ext
    funext n
    simp only [RingHom.id_apply]
    rw [circleFourierTransform.map_smul c (circleFourierJetCutFun s b f)]
    simp only [lp.coeFn_smul, Pi.smul_apply]
    rw [circleFourierTransform_jetCut_apply s hs b (c • f) n]
    rw [circleFourierTransform_jetCut_apply s hs b f n, circleFourierTransform.map_smul]
    by_cases hn : n ∈ s
    · simp only [ite_eq_left hn, lp.coeFn_smul, Pi.smul_apply, Complex.real_smul]
      ring
    · simp only [ite_eq_right hn, smul_zero]

/-- The Fourier derivative projection as a bounded, real-linear operator. -/
def circleFourierJetCut (s : Finset ℤ)
    (hs : ∀ n : ℤ, -n ∈ s ↔ n ∈ s) (b : ℕ) : AngleL2 →L[ℝ] AngleL2 :=
  (circleFourierJetCutLinear s hs b).mkContinuous
    (∑ n ∈ s, (2 * |(n : ℝ)|) ^ b) (fun f => by
      change ‖circleFourierJetCutFun s b f‖ ≤ _
      have hC : 0 ≤ ∑ n ∈ s, (2 * |(n : ℝ)|) ^ b :=
        Finset.sum_nonneg (fun n _ => by positivity)
      have hbound (n : ℤ) (hn : n ∈ s) :
          |(1 : ℝ)| * (2 * |(n : ℝ)|) ^ b ≤ ∑ j ∈ s, (2 * |(j : ℝ)|) ^ b := by
        simp only [abs_one, one_mul]
        exact Finset.single_le_sum (f := fun j : ℤ => (2 * |(j : ℝ)|) ^ b)
          (fun j _ => by positivity) hn
      simpa only [one_smul] using
        circleFourierJetCutFun_weighted_norm_le s hs b f 1 hC hbound)

theorem circleFourierJetCut_apply (s : Finset ℤ)
    (hs : ∀ n : ℤ, -n ∈ s ↔ n ∈ s) (b : ℕ) (f : AngleL2) :
    circleFourierJetCut s hs b f = circleFourierJetCutFun s b f := rfl

theorem circleFourierJetCut_weighted_norm_le (s : Finset ℤ)
    (hs : ∀ n : ℤ, -n ∈ s ↔ n ∈ s) (b : ℕ) (f : AngleL2)
    (a : ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ n ∈ s, |a| * (2 * |(n : ℝ)|) ^ b ≤ C) :
    ‖a • circleFourierJetCut s hs b f‖ ≤ C * ‖f‖ :=
  circleFourierJetCutFun_weighted_norm_le s hs b f a hC hbound

end ContinuousFlexibility.Statements
