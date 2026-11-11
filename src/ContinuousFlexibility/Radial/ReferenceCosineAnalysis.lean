import ContinuousFlexibility.Radial.ReferenceCosineL2
import ContinuousFlexibility.Radial.ReferenceCirclePullback
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Actual angular analysis of even periodic L² fields

The coefficients below are actual normalized angular integrals. Scalar
Fourier Parseval and Fubini provide radial L² coefficients and the exact
sum of their squared norms, for an arbitrary sigma-finite radial measure.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory Filter
open scoped ENNReal InnerProductSpace

local instance : Fact (0 < Real.pi) := ⟨Real.pi_pos⟩

/-- The true normalized coefficient; index zero is the constant mode. -/
def referenceCosineCoeff (f : ℝ → ℝ) (n : ℕ) : ℝ :=
  ∫ θ, f θ * referenceCircleCosine n (θ : AddCircle Real.pi) ∂referenceAngularMeasure

@[simp]
theorem referenceCosineCoeff_zero (f : ℝ → ℝ) :
    referenceCosineCoeff f 0 = radialAngularMean f := by
  simp only [referenceCosineCoeff, referenceCircleCosine_zero, mul_one,
    integral_referenceAngularMeasure]

theorem referenceCosineCoeff_succ (f : ℝ → ℝ) (n : ℕ) :
    referenceCosineCoeff f (n + 1) =
      radialAngularMean (fun θ => f θ * Radial.cosineMode (2 * (n + 1)) θ) := by
  simp only [referenceCosineCoeff, referenceCircleCosine_succ_coe,
    integral_referenceAngularMeasure]

theorem memLp_pi_of_referenceAngularMeasure {f : ℝ → ℝ}
    (hf : MemLp f 2 referenceAngularMeasure) :
    MemLp f 2 (volume.restrict (Ioc (0 : ℝ) Real.pi)) := by
  have hc0 : ENNReal.ofReal ((2 * Real.pi)⁻¹) ≠ 0 := by positivity
  have hcTop : ENNReal.ofReal ((2 * Real.pi)⁻¹) ≠ ∞ := ENNReal.ofReal_ne_top
  have hh := hf.smul_measure
    (c := (ENNReal.ofReal ((2 * Real.pi)⁻¹))⁻¹) (by finiteness)
  rw [referenceAngularMeasure, smul_smul, ENNReal.inv_mul_cancel hc0 hcTop, one_smul] at hh
  apply MemLp.mono_measure (Measure.restrict_mono_set volume ?_) hh
  intro θ hθ
  exact ⟨hθ.1, hθ.2.trans (by linarith [Real.pi_pos])⟩

theorem referenceCosineCoeff_hasSum_sq {f : ℝ → ℝ}
    (hp : Function.Periodic f Real.pi) (he : ∀ θ, f (-θ) = f θ)
    (hf : MemLp f 2 referenceAngularMeasure) :
    HasSum (fun n : ℕ => (referenceCosineCoeff f n) ^ 2)
      (∫ θ, f θ ^ 2 ∂referenceAngularMeasure) := by
  have hfpi := memLp_pi_of_referenceAngularMeasure hf
  have hsTail : Summable (fun n : ℕ => (referenceCosineCoeff f (n + 1)) ^ 2) := by
    simpa only [referenceCosineCoeff_succ] using
      summable_sq_referenceCosineCoeff hp he hfpi
  have hs : Summable (fun n : ℕ => (referenceCosineCoeff f n) ^ 2) :=
    (summable_nat_add_iff 1).1 hsTail
  have heq : (∑' n : ℕ, (referenceCosineCoeff f n) ^ 2) =
      ∫ θ, f θ ^ 2 ∂referenceAngularMeasure := by
    rw [hs.tsum_eq_zero_add, referenceCosineCoeff_zero, integral_referenceAngularMeasure]
    simpa only [referenceCosineCoeff_succ] using
      (reference_cosine_parseval hp he hfpi).symm
  rw [← heq]
  exact hs.hasSum

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [SFinite μ]

/-- The actual radial function of angular coefficients. -/
def referenceCosineCoefficient (f : α × ℝ → ℝ) (n : ℕ) (r : α) : ℝ :=
  referenceCosineCoeff (fun θ => f (r, θ)) n

theorem referenceCosineCoefficient_aestronglyMeasurable
    {f : α × ℝ → ℝ} (hf : MemLp f 2 (μ.prod referenceAngularMeasure)) (n : ℕ) :
    AEStronglyMeasurable (referenceCosineCoefficient f n) μ := by
  have hm : AEStronglyMeasurable
      (fun x : α × ℝ => referenceCircleCosine n (x.2 : AddCircle Real.pi))
      (μ.prod referenceAngularMeasure) :=
    (((referenceCircleCosine n).continuous.comp
      (AddCircle.continuous_mk' Real.pi)).aestronglyMeasurable
        (μ := referenceAngularMeasure)).comp_snd
  exact (hf.aestronglyMeasurable.mul hm).integral_prod_right'

theorem referenceCosineCoefficient_ae_hasSum_sq {f : α × ℝ → ℝ}
    (hf : MemLp f 2 (μ.prod referenceAngularMeasure))
    (hp : ∀ r, Function.Periodic (fun θ => f (r, θ)) Real.pi)
    (he : ∀ r θ, f (r, -θ) = f (r, θ)) :
    ∀ᵐ r ∂μ, HasSum (fun n : ℕ => (referenceCosineCoefficient f n r) ^ 2)
      (∫ θ, f (r, θ) ^ 2 ∂referenceAngularMeasure) := by
  filter_upwards [memLp_two_prod_sections hf] with r hr
  exact referenceCosineCoeff_hasSum_sq (hp r) (he r) hr

theorem referenceCosineCoefficient_memLp {f : α × ℝ → ℝ}
    (hf : MemLp f 2 (μ.prod referenceAngularMeasure))
    (hp : ∀ r, Function.Periodic (fun θ => f (r, θ)) Real.pi)
    (he : ∀ r θ, f (r, -θ) = f (r, θ)) (n : ℕ) :
    MemLp (referenceCosineCoefficient f n) 2 μ := by
  have hm := referenceCosineCoefficient_aestronglyMeasurable hf n
  apply (memLp_two_iff_integrable_sq hm).2
  have hmsq : AEStronglyMeasurable (fun r => (referenceCosineCoefficient f n r) ^ 2) μ := by
    have hh := hm.mul hm
    change AEStronglyMeasurable (fun r =>
      referenceCosineCoefficient f n r * referenceCosineCoefficient f n r) μ at hh
    simpa only [pow_two] using hh
  apply hf.integrable_sq.integral_prod_left.mono' hmsq
  filter_upwards [referenceCosineCoefficient_ae_hasSum_sq hf hp he] with r hr
  have hb := le_hasSum hr n (fun j _ => sq_nonneg (referenceCosineCoefficient f j r))
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (referenceCosineCoefficient f n r : ℝ))] using hb

/-- Parseval integrated in the actual radial measure. -/
theorem referenceCosineCoefficient_hasSum_integral_sq {f : α × ℝ → ℝ}
    (hf : MemLp f 2 (μ.prod referenceAngularMeasure))
    (hp : ∀ r, Function.Periodic (fun θ => f (r, θ)) Real.pi)
    (he : ∀ r θ, f (r, -θ) = f (r, θ)) :
    HasSum (fun n : ℕ => ∫ r, (referenceCosineCoefficient f n r) ^ 2 ∂μ)
      (∫ x, f x ^ 2 ∂μ.prod referenceAngularMeasure) := by
  have hsum := referenceCosineCoefficient_ae_hasSum_sq hf hp he
  have hbound : Integrable (fun r => ∑' n : ℕ, (referenceCosineCoefficient f n r) ^ 2) μ := by
    apply hf.integrable_sq.integral_prod_left.congr
    filter_upwards [hsum] with r hr
    exact hr.tsum_eq.symm
  rw [integral_prod _ hf.integrable_sq]
  exact hasSum_integral_of_dominated_convergence
    (fun n r => (referenceCosineCoefficient f n r) ^ 2)
    (fun n => (referenceCosineCoefficient_memLp hf hp he n).integrable_sq.aestronglyMeasurable)
    (fun n => ae_of_all _ fun r =>
      (Real.norm_of_nonneg (sq_nonneg (referenceCosineCoefficient f n r : ℝ))).le)
    (hsum.mono fun _ hr => hr.summable) hbound hsum

/-- Actual radial L² coefficient vectors. -/
def referenceCosineAnalysisCoeff {f : α × ℝ → ℝ}
    (hf : MemLp f 2 (μ.prod referenceAngularMeasure))
    (hp : ∀ r, Function.Periodic (fun θ => f (r, θ)) Real.pi)
    (he : ∀ r θ, f (r, -θ) = f (r, θ)) (n : ℕ) : Lp ℝ 2 μ :=
  (referenceCosineCoefficient_memLp hf hp he n).toLp (referenceCosineCoefficient f n)

theorem referenceCosineAnalysisCoeff_ae {f : α × ℝ → ℝ}
    (hf : MemLp f 2 (μ.prod referenceAngularMeasure))
    (hp : ∀ r, Function.Periodic (fun θ => f (r, θ)) Real.pi)
    (he : ∀ r θ, f (r, -θ) = f (r, θ)) (n : ℕ) :
    referenceCosineAnalysisCoeff hf hp he n =ᵐ[μ] referenceCosineCoefficient f n :=
  (referenceCosineCoefficient_memLp hf hp he n).coeFn_toLp

theorem referenceL2_norm_sq {β : Type*} [MeasurableSpace β] {ν : Measure β}
    (v : Lp ℝ 2 ν) : ‖v‖ ^ 2 = ∫ x, v x ^ 2 ∂ν := by
  simpa only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs] using
    L2.inner_def (𝕜 := ℝ) v v

theorem referenceL2_toLp_norm_sq {β : Type*} [MeasurableSpace β] {ν : Measure β}
    {g : β → ℝ} (hg : MemLp g 2 ν) :
    ‖hg.toLp g‖ ^ 2 = ∫ x, g x ^ 2 ∂ν := by
  rw [referenceL2_norm_sq]
  exact integral_congr_ae (hg.coeFn_toLp.fun_comp (fun x : ℝ => x ^ 2))

theorem referenceCosineAnalysisCoeff_norm_sq {f : α × ℝ → ℝ}
    (hf : MemLp f 2 (μ.prod referenceAngularMeasure))
    (hp : ∀ r, Function.Periodic (fun θ => f (r, θ)) Real.pi)
    (he : ∀ r θ, f (r, -θ) = f (r, θ)) (n : ℕ) :
    ‖referenceCosineAnalysisCoeff hf hp he n‖ ^ 2 =
      ∫ r, (referenceCosineCoefficient f n r) ^ 2 ∂μ :=
  referenceL2_toLp_norm_sq (referenceCosineCoefficient_memLp hf hp he n)

theorem referenceCosineAnalysisCoeff_hasSum_norm_sq {f : α × ℝ → ℝ}
    (hf : MemLp f 2 (μ.prod referenceAngularMeasure))
    (hp : ∀ r, Function.Periodic (fun θ => f (r, θ)) Real.pi)
    (he : ∀ r θ, f (r, -θ) = f (r, θ)) :
    HasSum (fun n : ℕ => ‖referenceCosineAnalysisCoeff hf hp he n‖ ^ 2)
      (‖hf.toLp f‖ ^ 2) := by
  simp only [referenceCosineAnalysisCoeff_norm_sq, referenceL2_toLp_norm_sq]
  exact referenceCosineCoefficient_hasSum_integral_sq hf hp he

/-- The actual source coefficient sequence, in the Hilbert sum of radial L² spaces. -/
def referenceCosineAnalysis {f : α × ℝ → ℝ}
    (hf : MemLp f 2 (μ.prod referenceAngularMeasure))
    (hp : ∀ r, Function.Periodic (fun θ => f (r, θ)) Real.pi)
    (he : ∀ r θ, f (r, -θ) = f (r, θ)) :
    lp (fun _ : ℕ => Lp ℝ 2 μ) 2 :=
  ⟨referenceCosineAnalysisCoeff hf hp he, by
    apply memℓp_gen
    simpa using (referenceCosineAnalysisCoeff_hasSum_norm_sq hf hp he).summable⟩

theorem referenceCosineAnalysis_tsum_norm_sq {f : α × ℝ → ℝ}
    (hf : MemLp f 2 (μ.prod referenceAngularMeasure))
    (hp : ∀ r, Function.Periodic (fun θ => f (r, θ)) Real.pi)
    (he : ∀ r θ, f (r, -θ) = f (r, θ)) :
    (∑' n : ℕ, ‖referenceCosineAnalysis hf hp he n‖ ^ 2) = ‖hf.toLp f‖ ^ 2 :=
  (referenceCosineAnalysisCoeff_hasSum_norm_sq hf hp he).tsum_eq

end ContinuousFlexibility.Statements
