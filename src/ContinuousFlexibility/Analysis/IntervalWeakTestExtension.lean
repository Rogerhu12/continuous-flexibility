import ContinuousFlexibility.Analysis.IntervalTestCompression
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Extending weak equations to tests meeting the interval endpoints

A smooth compact test whose ordinary support lies in an open interval may
have topological support meeting the endpoints. Affine compression gives
strictly interior tests. Their first two derivatives converge and remain
uniformly bounded, so dominated convergence extends the weak equation.

Only L¹ membership of the solution and forcing is used. No quantitative
flatness of either the coefficient or the test is required.
-/

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace ContinuousFlexibility.Analysis

noncomputable section

set_option backward.isDefEq.respectTransparency false

/-- Strictly interior smooth tests determine the same second-order weak
equation as all smooth compact tests with ordinary support in the interval. -/
theorem extend_secondOrder_tests_Ioo {a b : ℝ} (hab : a < b)
    {u f p q : ℝ → ℝ} (hu : IntegrableOn u (Ioo a b) volume)
    (hf : IntegrableOn f (Ioo a b) volume)
    (hp : ContinuousOn p (Icc a b)) (hq : ContinuousOn q (Icc a b))
    (hstrict : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b →
        (∫ x in Ioo a b, u x * (p x * deriv (deriv φ) x + q x * deriv φ x)) =
          ∫ x in Ioo a b, f x * φ x)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hψs : Function.support ψ ⊆ Ioo a b) :
    (∫ x in Ioo a b, u x * (p x * deriv (deriv ψ) x + q x * deriv ψ x)) =
      ∫ x in Ioo a b, f x * ψ x := by
  let μ : Measure ℝ := volume.restrict (Ioo a b)
  let ψn : ℕ → ℝ → ℝ :=
    fun n => intervalTestCompression a b (intervalCompressionScale n) ψ
  have hψn (n : ℕ) : ContDiff ℝ ∞ (ψn n) :=
    contDiff_intervalTestCompression hψ a b (intervalCompressionScale n)
  have hψn' (n : ℕ) : ContDiff ℝ ∞ (deriv (ψn n)) :=
    (contDiff_infty_iff_deriv.mp (hψn n)).2
  have hψn'' (n : ℕ) : ContDiff ℝ ∞ (deriv (deriv (ψn n))) :=
    (contDiff_infty_iff_deriv.mp (hψn' n)).2
  have hψ' : ContDiff ℝ ∞ (deriv ψ) := (contDiff_infty_iff_deriv.mp hψ).2
  have hψ'' : ContDiff ℝ ∞ (deriv (deriv ψ)) := (contDiff_infty_iff_deriv.mp hψ').2
  obtain ⟨B₀, hB₀⟩ := hψ.continuous.bounded_above_of_compact_support hψc
  obtain ⟨B₁, hB₁⟩ := hψ'.continuous.bounded_above_of_compact_support hψc.deriv
  obtain ⟨B₂, hB₂⟩ := hψ''.continuous.bounded_above_of_compact_support hψc.deriv.deriv
  obtain ⟨A, hA⟩ := isCompact_Icc.exists_bound_of_continuousOn hp
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hq
  have hA₀ : 0 ≤ A := (norm_nonneg (p a)).trans (hA a ⟨le_rfl, hab.le⟩)
  have hB₀' : 0 ≤ B := (norm_nonneg (q a)).trans (hB a ⟨le_rfl, hab.le⟩)
  have hb₀ (n : ℕ) (x : ℝ) : ‖ψn n x‖ ≤ B₀ := hB₀ _
  have hb₁ (n : ℕ) (x : ℝ) : ‖deriv (ψn n) x‖ ≤ 2 * B₁ := by
    change ‖deriv (intervalTestCompression a b (intervalCompressionScale n) ψ) x‖ ≤ _
    rw [deriv_intervalTestCompression hψ]
    change ‖intervalCompressionScale n *
      deriv ψ (intervalCompressionMap a b (intervalCompressionScale n) x)‖ ≤ _
    have hλ₀ : 0 ≤ intervalCompressionScale n :=
      (lt_trans zero_lt_one (intervalCompressionScale_bounds n).1).le
    rw [norm_mul, Real.norm_of_nonneg hλ₀]
    exact mul_le_mul (intervalCompressionScale_bounds n).2 (hB₁ _)
      (norm_nonneg _) (by norm_num)
  have hb₂ (n : ℕ) (x : ℝ) : ‖deriv (deriv (ψn n)) x‖ ≤ 4 * B₂ := by
    change ‖deriv (deriv (intervalTestCompression a b (intervalCompressionScale n) ψ)) x‖ ≤ _
    rw [secondDeriv_intervalTestCompression hψ]
    change ‖intervalCompressionScale n ^ 2 *
      deriv (deriv ψ) (intervalCompressionMap a b (intervalCompressionScale n) x)‖ ≤ _
    rw [norm_mul, Real.norm_of_nonneg (sq_nonneg (intervalCompressionScale n))]
    have hλ₀ : 0 ≤ intervalCompressionScale n :=
      (lt_trans zero_lt_one (intervalCompressionScale_bounds n).1).le
    have hλ₂ : intervalCompressionScale n ^ 2 ≤ 4 := by
      have hh := mul_le_mul (intervalCompressionScale_bounds n).2
        (intervalCompressionScale_bounds n).2 hλ₀ (by norm_num : (0 : ℝ) ≤ 2)
      nlinarith
    exact mul_le_mul hλ₂ (hB₂ _) (norm_nonneg _) (by norm_num)
  let C : ℝ := A * (4 * B₂) + B * (2 * B₁)
  let F : ℕ → ℝ → ℝ :=
    fun n x => u x * (p x * deriv (deriv (ψn n)) x + q x * deriv (ψn n) x)
  let R : ℕ → ℝ → ℝ := fun n x => f x * ψn n x
  have hui : Integrable u μ := hu
  have hfi : Integrable f μ := hf
  have hpm : AEStronglyMeasurable p μ :=
    (hp.mono Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo
  have hqm : AEStronglyMeasurable q μ :=
    (hq.mono Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo
  have hFm (n : ℕ) : AEStronglyMeasurable (F n) μ :=
    hui.aestronglyMeasurable.mul
      ((hpm.mul (hψn'' n).continuous.aestronglyMeasurable).add
        (hqm.mul (hψn' n).continuous.aestronglyMeasurable))
  have hRm (n : ℕ) : AEStronglyMeasurable (R n) μ :=
    hfi.aestronglyMeasurable.mul (hψn n).continuous.aestronglyMeasurable
  have hFbound (n : ℕ) : ∀ᵐ x ∂μ, ‖F n x‖ ≤ ‖u x‖ * C := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hx' : x ∈ Icc a b := ⟨hx.1.le, hx.2.le⟩
    change ‖u x * (p x * deriv (deriv (ψn n)) x + q x * deriv (ψn n) x)‖ ≤ _
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    calc
      ‖p x * deriv (deriv (ψn n)) x + q x * deriv (ψn n) x‖ ≤
          ‖p x * deriv (deriv (ψn n)) x‖ + ‖q x * deriv (ψn n) x‖ :=
        norm_add_le _ _
      _ ≤ C := by
        rw [norm_mul, norm_mul]
        exact add_le_add (mul_le_mul (hA x hx') (hb₂ n x) (norm_nonneg _) hA₀)
          (mul_le_mul (hB x hx') (hb₁ n x) (norm_nonneg _) hB₀')
  have hRbound (n : ℕ) : ∀ᵐ x ∂μ, ‖R n x‖ ≤ ‖f x‖ * B₀ := by
    exact Eventually.of_forall fun x => by
      change ‖f x * ψn n x‖ ≤ _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hb₀ n x) (norm_nonneg _)
  have hFlim : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop
      (𝓝 (u x * (p x * deriv (deriv ψ) x + q x * deriv ψ x))) := by
    apply Eventually.of_forall
    intro x
    exact tendsto_const_nhds.mul
      ((tendsto_const_nhds.mul (tendsto_secondDeriv_intervalTestCompression hψ a b x)).add
        (tendsto_const_nhds.mul (tendsto_deriv_intervalTestCompression hψ a b x)))
  have hRlim : ∀ᵐ x ∂μ, Tendsto (fun n => R n x) atTop (𝓝 (f x * ψ x)) :=
    Eventually.of_forall fun x =>
      tendsto_const_nhds.mul (tendsto_intervalTestCompression hψ a b x)
  have hFL := tendsto_integral_of_dominated_convergence (fun x => ‖u x‖ * C)
    hFm (hui.norm.mul_const C) hFbound hFlim
  have hRL := tendsto_integral_of_dominated_convergence (fun x => ‖f x‖ * B₀)
    hRm (hfi.norm.mul_const B₀) hRbound hRlim
  have hseq : (fun n => ∫ x, F n x ∂μ) = (fun n => ∫ x, R n x ∂μ) := by
    funext n
    exact hstrict (ψn n) (hψn n)
      (hasCompactSupport_intervalTestCompression hab (intervalCompressionScale_bounds n).1 hψs)
      (tsupport_intervalTestCompression_subset hab (intervalCompressionScale_bounds n).1 hψs)
  rw [hseq] at hFL
  exact tendsto_nhds_unique hFL hRL

private theorem weakTest_divergence_expand {w ψ : ℝ → ℝ}
    (hw : ContDiff ℝ ∞ w) (hψ : ContDiff ℝ ∞ ψ) :
    (fun x => deriv (fun y => w y * deriv ψ y) x) =
      fun x => w x * deriv (deriv ψ) x + deriv w x * deriv ψ x := by
  funext x
  have hψ' : ContDiff ℝ ∞ (deriv ψ) := (contDiff_infty_iff_deriv.mp hψ).2
  have hd := deriv_fun_mul (hw.differentiable (by simp) x)
    (hψ'.differentiable (by simp) x)
  exact hd.trans (by ring)

/-- The divergence-form specialization needed by radial mode graphs. -/
theorem extend_weak_divergence_tests_Ioo {a b : ℝ} (hab : a < b)
    {u f w : ℝ → ℝ} (hu : IntegrableOn u (Ioo a b) volume)
    (hf : IntegrableOn f (Ioo a b) volume) (hw : ContDiff ℝ ∞ w)
    (hstrict : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b →
        (∫ x in Ioo a b, u x * deriv (fun y => w y * deriv φ y) x) =
          ∫ x in Ioo a b, f x * φ x)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hψs : Function.support ψ ⊆ Ioo a b) :
    (∫ x in Ioo a b, u x * deriv (fun y => w y * deriv ψ y) x) =
      ∫ x in Ioo a b, f x * ψ x := by
  rw [weakTest_divergence_expand hw hψ]
  apply extend_secondOrder_tests_Ioo hab hu hf hw.continuous.continuousOn
    (contDiff_infty_iff_deriv.mp hw).2.continuous.continuousOn _ hψ hψc hψs
  intro φ hφ hφc hφs
  have h := hstrict φ hφ hφc hφs
  rw [weakTest_divergence_expand hw hφ] at h
  exact h

/-- Interval-integral interface, with exactly the ordinary-support test
condition appearing in `ModeLocalEquation`. -/
theorem extend_weak_divergence_tests_interval {a b : ℝ} (hab : a < b)
    {u f w : ℝ → ℝ} (hu : IntegrableOn u (Ioo a b) volume)
    (hf : IntegrableOn f (Ioo a b) volume) (hw : ContDiff ℝ ∞ w)
    (hstrict : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b →
        (∫ x in a..b, u x * deriv (fun y => w y * deriv φ y) x) =
          ∫ x in a..b, f x * φ x)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hψs : Function.support ψ ⊆ Ioo a b) :
    (∫ x in a..b, u x * deriv (fun y => w y * deriv ψ y) x) =
      ∫ x in a..b, f x * ψ x := by
  have hstrict' : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b →
        (∫ x in Ioo a b, u x * deriv (fun y => w y * deriv φ y) x) =
          ∫ x in Ioo a b, f x * φ x := by
    intro φ hφ hφc hφs
    simpa only [intervalIntegral.integral_of_le hab.le, integral_Ioc_eq_integral_Ioo] using
      hstrict φ hφ hφc hφs
  simpa only [intervalIntegral.integral_of_le hab.le, integral_Ioc_eq_integral_Ioo] using
    extend_weak_divergence_tests_Ioo hab hu hf hw hstrict' hψ hψc hψs

end

end ContinuousFlexibility.Analysis
