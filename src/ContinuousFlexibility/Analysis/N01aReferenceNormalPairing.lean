import ContinuousFlexibility.Analysis.N01aReferenceWeightedMode
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# The actual first-normal estimate as a dual estimate

The given weak normal derivative need not have been declared measurable.
The square bounds still control every actual iterated pairing, which is
enough to bound the smooth eigenfunction's derivative.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology Interval

theorem abs_radial_pairing_le_sqrt_squares {D : ReferenceData} (hab : D.a ≤ D.b)
    {f g : PolarPoint → ℝ}
    (hf : Integrable (fun p => f p ^ 2) (radialPhysicalMeasure D))
    (hg : Integrable (fun p => g p ^ 2) (radialPhysicalMeasure D)) :
    |∫ r in D.a..D.b, radialAngularMean (fun θ => f (r, θ) * g (r, θ))| ≤
      (2 * Real.pi)⁻¹ *
        (Real.sqrt (∫ p, f p ^ 2 ∂radialPhysicalMeasure D) *
          Real.sqrt (∫ p, g p ^ 2 ∂radialPhysicalMeasure D)) := by
  have hf2 := n01a_memLp_abs_of_integrable_sq hf
  have hg2 := n01a_memLp_abs_of_integrable_sq hg
  have hprod : Integrable (fun p => |f p * g p|) (radialPhysicalMeasure D) := by
    simpa only [Pi.mul_apply, abs_mul] using hf2.integrable_mul hg2
  have hraw := abs_radial_pairing_le_integral_abs hab hprod
    (ψ := fun _ => 1) (B := 1) zero_le_one (fun _ => by norm_num)
  have hholder := n01a_abs_integral_mul_le_sqrt_sq hf2 hg2
  have hprod_nonneg : 0 ≤ ∫ p, |f p| * |g p| ∂radialPhysicalMeasure D :=
    integral_nonneg fun p => mul_nonneg (abs_nonneg (f p)) (abs_nonneg (g p))
  have hi : (∫ p, |f p * g p| ∂radialPhysicalMeasure D) ≤
      Real.sqrt (∫ p, f p ^ 2 ∂radialPhysicalMeasure D) *
        Real.sqrt (∫ p, g p ^ 2 ∂radialPhysicalMeasure D) := by
    simpa only [abs_mul, sq_abs, abs_of_nonneg hprod_nonneg]
      using hholder
  apply (show |∫ r in D.a..D.b,
      radialAngularMean (fun θ => f (r, θ) * g (r, θ))| ≤
        (2 * Real.pi)⁻¹ * ∫ p, |f p * g p| ∂radialPhysicalMeasure D from by
      simpa only [mul_one] using hraw).trans
  exact mul_le_mul_of_nonneg_left hi (by positivity)

set_option backward.isDefEq.respectTransparency false in
theorem radialPartial_cosine_field {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (j : ℕ) (r θ : ℝ) :
    radialPartial (fun p : PolarPoint => ψ p.1 * Radial.cosineMode j p.2) (r, θ) =
      deriv ψ r * Radial.cosineMode j θ := by
  have hfield : ContDiff ℝ ∞
      (fun p : PolarPoint => ψ p.1 * Radial.cosineMode j p.2) := by
    unfold Radial.cosineMode
    fun_prop
  have h₁ := hasDerivAt_radial_slice (hfield.differentiable (by simp) (r, θ))
  have h₂ := ((hψ.differentiable (by simp) r).hasDerivAt).mul_const (Radial.cosineMode j θ)
  exact h₁.unique h₂

theorem normalPairing_cosine_field {D : ReferenceData} {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (u : PolarPoint → ℝ) (j : ℕ) :
    (∫ r in D.a..D.b, radialAngularMean (fun θ => u (r, θ) *
      radialPartial (fun p : PolarPoint => ψ p.1 * Radial.cosineMode j p.2) (r, θ))) =
      ∫ r in D.a..D.b, referenceMode u j r * deriv ψ r := by
  simp_rw [radialPartial_cosine_field hψ j]
  apply intervalIntegral.integral_congr
  intro r _
  dsimp only
  rw [show (fun θ => u (r, θ) * (deriv ψ r * Radial.cosineMode j θ)) =
      (fun θ => deriv ψ r * (u (r, θ) * Radial.cosineMode j θ)) by funext θ; ring]
  rw [radialAngularMean_const_mul]
  exact mul_comm _ _

theorem weakNormalDerivative_mode_pairing {D : ReferenceData}
    (hab : D.a ≤ D.b) (hphi : EndpointFlat D D.phi) {u ur : PolarPoint → ℝ}
    (hweak : WeakNormalDerivative D u ur)
    (hmode : referenceMode u 2 =ᵐ[volume.restrict (radialCore D)] D.phi)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ radialCore D) :
    (∫ r in D.a..D.b, radialAngularMean (fun θ =>
      ur (r, θ) * (ψ r * Radial.cosineMode 2 θ))) =
      ∫ r in D.a..D.b, deriv D.phi r * ψ r := by
  have h := hweak (fun p => ψ p.1 * Radial.cosineMode 2 p.2)
    (radialTest_cosine hψ hc hs 2)
  rw [normalPairing_cosine_field hψ u 2] at h
  have hmodeI : (∫ r in D.a..D.b, referenceMode u 2 r * deriv ψ r) =
      ∫ r in D.a..D.b, D.phi r * deriv ψ r := by
    have he : referenceMode u 2 =ᵐ[volume.restrict (Ioc D.a D.b)] D.phi := by
      simpa only [radialCore, restrict_Ioo_eq_restrict_Ioc] using hmode
    rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
    exact integral_congr_ae (he.mono fun r hr => by dsimp only; rw [hr])
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun r _ => (hphi.1.differentiable (by simp) r).hasDerivAt)
    (fun r _ => (hψ.differentiable (by simp) r).hasDerivAt)
    ((hphi.1.continuous_deriv (by simp)).intervalIntegrable D.a D.b)
    ((hψ.continuous_deriv (by simp)).intervalIntegrable D.a D.b)
  rw [hphi.2 D.b (Or.inr le_rfl), hphi.2 D.a (Or.inl le_rfl),
    zero_mul, zero_mul, sub_zero, zero_sub] at hparts
  rw [hmodeI, hparts] at h
  exact neg_injective h.symm

/-- Bounded interior cutoffs tend to one for ordinary radial integrable data.
No vanishing of the data at the endpoints is needed. -/
theorem tendsto_integral_cutoff_mul {D : ReferenceData} (hab : D.a ≤ D.b)
    {f : ℝ → ℝ} (hf : IntegrableOn f (Icc D.a D.b) volume) :
    Tendsto (fun n => ∫ r in D.a..D.b, Radial.intervalTestCutoff D.a D.b n r * f r)
      atTop (𝓝 (∫ r in D.a..D.b, f r)) := by
  have hi : Integrable f (volume.restrict (radialCore D)) :=
    hf.mono_set Ioo_subset_Icc_self
  have hlim : Tendsto (fun n => ∫ r, Radial.intervalTestCutoff D.a D.b n r * f r
      ∂volume.restrict (radialCore D)) atTop (𝓝 (∫ r, f r ∂volume.restrict (radialCore D))) := by
    apply tendsto_integral_of_dominated_convergence (fun r => |f r|)
    · intro n
      exact ((Radial.contDiff_intervalTestCutoff D.a D.b n).continuous.aestronglyMeasurable.mul
        hi.aestronglyMeasurable)
    · exact hi.abs
    · intro n
      exact Eventually.of_forall fun r => by
        dsimp only
        rw [Real.norm_eq_abs, abs_mul,
          abs_of_nonneg (Radial.intervalTestCutoff_nonneg D.a D.b n r)]
        exact (mul_le_mul_of_nonneg_right
          (Radial.intervalTestCutoff_le_one D.a D.b n r) (abs_nonneg _)).trans_eq (one_mul _)
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
      simpa only [one_mul] using (Radial.tendsto_intervalTestCutoff hr).mul_const (f r)
  simpa only [radialCore, restrict_Ioo_eq_restrict_Ioc,
    intervalIntegral.integral_of_le hab] using hlim

end ContinuousFlexibility.Statements
