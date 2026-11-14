module

public import Mathlib.Probability.Moments.ComplexMGF
public import Mathlib.Analysis.Complex.TaylorSeries
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

/-!
# Uniqueness from actual exponential moments

Finite measures with all exponential moments are determined by their
actual polynomial integrals. The proof uses the entire complex MGF and
its Taylor expansion, followed by mathlib's measure-uniqueness theorem.
This supplies the analytic step in Hermite completeness.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal

set_option backward.isDefEq.respectTransparency false

theorem integrableExpSet_id_eq_univ
    {μ : Measure ℝ} (hμ : ∀ t : ℝ, Integrable (fun x : ℝ => exp (t * x)) μ) :
    integrableExpSet id μ = univ := by
  ext t
  simp only [integrableExpSet, mem_ofPred_eq, id_eq, mem_univ, iff_true]
  exact hμ t

theorem differentiable_complexMGF_of_exponential_integrability
    {μ : Measure ℝ} (hμ : ∀ t : ℝ, Integrable (fun x : ℝ => exp (t * x)) μ) :
    Differentiable ℂ (complexMGF id μ) := by
  intro z
  apply (hasDerivAt_complexMGF (X := id) (μ := μ) (z := z) ?_).differentiableAt
  rw [integrableExpSet_id_eq_univ hμ, interior_univ]
  trivial

/-- Actual moment uniqueness, with convergence supplied by exponential
integrability and the Taylor expansion of the entire complex MGF. -/
theorem measure_eq_of_all_exponential_moments
    {μ ν : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∀ t : ℝ, Integrable (fun x : ℝ => exp (t * x)) μ)
    (hν : ∀ t : ℝ, Integrable (fun x : ℝ => exp (t * x)) ν)
    (hmom : ∀ n : ℕ, (∫ x : ℝ, x ^ n ∂μ) = ∫ x : ℝ, x ^ n ∂ν) : μ = ν := by
  have hμ0 : (0 : ℂ).re ∈ interior (integrableExpSet id μ) := by
    rw [integrableExpSet_id_eq_univ hμ, interior_univ]
    trivial
  have hν0 : (0 : ℂ).re ∈ interior (integrableExpSet id ν) := by
    rw [integrableExpSet_id_eq_univ hν, interior_univ]
    trivial
  have hd : ∀ n : ℕ, iteratedDeriv n (complexMGF id μ) 0 =
      iteratedDeriv n (complexMGF id ν) 0 := by
    intro n
    rw [iteratedDeriv_complexMGF hμ0, iteratedDeriv_complexMGF hν0]
    simp only [id_eq, zero_mul, Complex.exp_zero, mul_one]
    norm_cast
    exact hmom n
  apply Measure.ext_of_complexMGF_id_eq
  funext z
  have hsumμ := Complex.hasSum_taylorSeries_of_entire
    (differentiable_complexMGF_of_exponential_integrability hμ) 0 z
  have hsumν := Complex.hasSum_taylorSeries_of_entire
    (differentiable_complexMGF_of_exponential_integrability hν) 0 z
  simp only [hd] at hsumμ
  exact hsumμ.unique hsumν

/-- Restricting a real density to its positive part preserves any
integrable pairing. This is used for the two positive measures of a
signed, Gaussian-weighted `L²` function. -/
theorem integrable_posPart_mul_of_integrable_mul
    {F g : ℝ → ℝ} (hF : Measurable F) (hg : Measurable g)
    (hfg : Integrable (fun x => F x * g x) volume) :
    Integrable (fun x => max (F x) 0 * g x) volume := by
  apply hfg.norm.mono' ((hF.max measurable_const).mul hg).aestronglyMeasurable
  filter_upwards with x
  change ‖max (F x) 0 * g x‖ ≤ ‖F x * g x‖
  rw [norm_mul, Real.norm_of_nonneg (le_max_right (F x) 0)]
  calc
    _ ≤ ‖F x‖ * ‖g x‖ :=
      mul_le_mul_of_nonneg_right (max_le (Real.le_norm_self _) (norm_nonneg _)) (norm_nonneg _)
    _ = _ := (norm_mul _ _).symm

theorem integrable_ofRealDensity_of_integrable_mul
    {F g : ℝ → ℝ} (hF : Measurable F) (hg : Measurable g)
    (hfg : Integrable (fun x => F x * g x) volume) :
    Integrable g (volume.withDensity (fun x => ENNReal.ofReal (F x))) := by
  apply (integrable_withDensity_iff_integrable_smul' hF.ennreal_ofReal
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))).mpr
  simpa only [ENNReal.toReal_ofReal', smul_eq_mul] using
    integrable_posPart_mul_of_integrable_mul hF hg hfg

theorem integral_ofRealDensity
    {F : ℝ → ℝ} (hF : Measurable F) (g : ℝ → ℝ) :
    (∫ x : ℝ, g x ∂volume.withDensity (fun x => ENNReal.ofReal (F x))) =
      ∫ x : ℝ, max (F x) 0 * g x := by
  simpa only [ENNReal.toReal_ofReal', smul_eq_mul] using
    integral_withDensity_eq_integral_toReal_smul hF.ennreal_ofReal
      (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)) g

/-- An integrable signed density with all exponential pairings integrable
and all polynomial moments zero is zero almost everywhere. -/
theorem ae_eq_zero_of_exponential_moments
    {F : ℝ → ℝ} (hF : Measurable F) (hFi : Integrable F volume)
    (hexp : ∀ t : ℝ, Integrable (fun x => F x * exp (t * x)) volume)
    (hpow : ∀ n : ℕ, Integrable (fun x : ℝ => F x * x ^ n) volume)
    (hmom : ∀ n : ℕ, (∫ x : ℝ, F x * x ^ n) = 0) : F =ᵐ[volume] 0 := by
  let μ : Measure ℝ := volume.withDensity (fun x => ENNReal.ofReal (F x))
  let ν : Measure ℝ := volume.withDensity (fun x => ENNReal.ofReal (-F x))
  let : IsFiniteMeasure μ := isFiniteMeasure_withDensity_ofReal hFi.2
  let : IsFiniteMeasure ν := isFiniteMeasure_withDensity_ofReal hFi.neg.2
  have hneg {g : ℝ → ℝ} (hg : Integrable (fun x => F x * g x) volume) :
      Integrable (fun x => -F x * g x) volume := by
    convert hg.neg using 1
    funext x
    simp only [Pi.neg_apply]
    ring
  have hμexp : ∀ t : ℝ, Integrable (fun x : ℝ => exp (t * x)) μ := by
    intro t
    exact integrable_ofRealDensity_of_integrable_mul hF (by fun_prop) (hexp t)
  have hνexp : ∀ t : ℝ, Integrable (fun x : ℝ => exp (t * x)) ν := by
    intro t
    exact integrable_ofRealDensity_of_integrable_mul hF.neg (by fun_prop) (hneg (hexp t))
  have heq : μ = ν := by
    apply measure_eq_of_all_exponential_moments hμexp hνexp
    intro n
    rw [integral_ofRealDensity hF,
      integral_ofRealDensity (F := fun x => -F x) hF.neg]
    have hp := integrable_posPart_mul_of_integrable_mul hF (by fun_prop) (hpow n)
    have hn := integrable_posPart_mul_of_integrable_mul (F := fun x => -F x)
      hF.neg (by fun_prop) (hneg (hpow n))
    apply sub_eq_zero.mp
    rw [← integral_sub hp hn]
    calc
      _ = ∫ x : ℝ, F x * x ^ n := by
        apply integral_congr_ae
        filter_upwards with x
        by_cases hx : 0 ≤ F x
        · rw [max_eq_left hx, max_eq_right (by linarith : -F x ≤ 0)]
          ring
        · rw [max_eq_right (le_of_not_ge hx), max_eq_left (by linarith : 0 ≤ -F x)]
          ring
      _ = 0 := hmom n
  have hs : μ ⟂ₘ ν := withDensity_ofReal_mutuallySingular hF
  have hμzero : μ = 0 := by
    rw [← heq] at hs
    exact (Measure.MutuallySingular.self_iff μ).mp hs
  have hνzero : ν = 0 := heq.symm.trans hμzero
  have hp := (withDensity_eq_zero_iff hF.ennreal_ofReal.aemeasurable).mp hμzero
  have hn := (withDensity_eq_zero_iff hF.neg.ennreal_ofReal.aemeasurable).mp hνzero
  filter_upwards [hp, hn] with x hx hy
  have hxp := ENNReal.ofReal_eq_zero.mp hx
  have hxn := ENNReal.ofReal_eq_zero.mp hy
  change -F x ≤ 0 at hxn
  change F x = 0
  linarith

end ContinuousFlexibility.Radial
