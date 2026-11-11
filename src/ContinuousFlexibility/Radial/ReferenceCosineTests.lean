import ContinuousFlexibility.Radial.ReferenceCosineAlgebra
import ContinuousFlexibility.Radial.ReferenceSmoothGreen
import ContinuousFlexibility.Analysis.RootCompositionIntegral

/-!
# Smooth projected radial tests

Angular integration over a compact period preserves smoothness. Its actual
radial derivative is the coefficient of the actual radial partial, and
finite cosine projection preserves compact radial support.
-/

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace ContinuousFlexibility.Radial

open ContinuousFlexibility.Statements
open ContinuousFlexibility.Analysis

noncomputable section

theorem contDiff_referenceRadialCoefficient {u : PolarPoint → ℝ}
    (hu : ContDiff ℝ ∞ u) (n : ℕ) :
    ContDiff ℝ ∞ (referenceRadialCoefficient u n) := by
  have hG : ContDiff ℝ ∞ (fun x : PolarPoint => u x * referenceAngularBasis n x.2) :=
    hu.mul ((contDiff_referenceAngularBasis n).comp contDiff_snd)
  change ContDiff ℝ ∞ (fun r => (2 * Real.pi)⁻¹ *
    ∫ θ in (0 : ℝ)..2 * Real.pi, u (r, θ) * referenceAngularBasis n θ)
  exact contDiff_const.mul (contDiff_intervalIntegral_of_contDiff hG 0 (2 * Real.pi))

/-- Differentiation under the actual normalized angular integral. -/
theorem hasDerivAt_referenceRadialCoefficient {u : PolarPoint → ℝ}
    (hu : ContDiff ℝ ∞ u) (n : ℕ) (r : ℝ) :
    HasDerivAt (referenceRadialCoefficient u n)
      (referenceRadialCoefficient (radialPartial u) n r) r := by
  let G : PolarPoint → ℝ := fun x => u x * referenceAngularBasis n x.2
  have hG : ContDiff ℝ ∞ G :=
    hu.mul ((contDiff_referenceAngularBasis n).comp contDiff_snd)
  let L : ℝ → ℝ →L[ℝ] ℝ := fun θ =>
    (fderiv ℝ G (r, θ)).comp (ContinuousLinearMap.inl ℝ ℝ ℝ)
  have hLc : Continuous L :=
    (((contDiff_infty_iff_fderiv.mp hG).2.continuous.comp
      (continuous_const.prodMk continuous_id)).clm_comp continuous_const)
  have hval : (∫ θ in (0 : ℝ)..2 * Real.pi, L θ) 1 =
      ∫ θ in (0 : ℝ)..2 * Real.pi,
        radialPartial u (r, θ) * referenceAngularBasis n θ := by
    rw [ContinuousLinearMap.intervalIntegral_apply (hLc.intervalIntegrable _ _) 1]
    apply intervalIntegral.integral_congr
    intro θ _hθ
    have h₁ : HasDerivAt (fun t => G (t, θ)) (L θ 1) r := by
      have h := ((hG.differentiable (by simp)) (r, θ)).hasFDerivAt.comp r
        (hasFDerivAt_prodMk_left r θ)
      simpa only [L, Function.comp_def] using h.hasDerivAt
    have h₂ : HasDerivAt (fun t => G (t, θ))
        (radialPartial u (r, θ) * referenceAngularBasis n θ) r :=
      (hasDerivAt_radial_slice (hu.differentiable (by simp) (r, θ))).mul_const
        (referenceAngularBasis n θ)
    exact h₁.unique h₂
  have hd := (hasFDerivAt_intervalIntegral_of_contDiff hG 0 (2 * Real.pi) r).hasDerivAt.const_mul
    ((2 * Real.pi)⁻¹)
  change HasDerivAt (fun t => (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi, G (t, θ))
    ((2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi,
      radialPartial u (r, θ) * referenceAngularBasis n θ) r
  rw [← hval]
  exact hd

theorem deriv_referenceRadialCoefficient {u : PolarPoint → ℝ}
    (hu : ContDiff ℝ ∞ u) (n : ℕ) :
    deriv (referenceRadialCoefficient u n) = referenceRadialCoefficient (radialPartial u) n := by
  funext r
  exact (hasDerivAt_referenceRadialCoefficient hu n r).deriv

theorem referenceBasisProjection_contDiff {u : PolarPoint → ℝ}
    (hu : ContDiff ℝ ∞ u) (I : Finset ℕ) :
    ContDiff ℝ ∞ (referenceBasisProjection I u) := by
  change ContDiff ℝ ∞ (fun x : PolarPoint => ∑ n ∈ I,
    referenceRadialCoefficient u n x.1 * referenceAngularBasis n x.2)
  apply ContDiff.sum
  intro n _hn
  exact ((contDiff_referenceRadialCoefficient hu n).comp contDiff_fst).mul
    ((contDiff_referenceAngularBasis n).comp contDiff_snd)

theorem referenceRadialCoefficient_zero_outside {u : PolarPoint → ℝ} {K : Set ℝ}
    (hz : ∀ r ∉ K, ∀ θ, u (r, θ) = 0) (n : ℕ) {r : ℝ} (hr : r ∉ K) :
    referenceRadialCoefficient u n r = 0 := by
  simp only [referenceRadialCoefficient, referenceAngularCoefficient, radialAngularMean,
    hz r hr, zero_mul, intervalIntegral.integral_zero, mul_zero]

theorem referenceRadialCoefficient_compact_support {D : ReferenceData} {u : PolarPoint → ℝ}
    (hu : RadialTest D u) (n : ℕ) :
    HasCompactSupport (referenceRadialCoefficient u n) ∧
      tsupport (referenceRadialCoefficient u n) ⊆ radialCore D := by
  obtain ⟨K, hK, hKI, hz⟩ := hu.2.2
  have hs : Function.support (referenceRadialCoefficient u n) ⊆ K := by
    intro r hr
    by_contra hrK
    exact hr (referenceRadialCoefficient_zero_outside hz n hrK)
  exact ⟨HasCompactSupport.of_support_subset_isCompact hK hs,
    (closure_minimal hs hK.isClosed).trans hKI⟩

theorem referenceBasisProjection_test {D : ReferenceData} {u : PolarPoint → ℝ}
    (hu : RadialTest D u) (I : Finset ℕ) :
    RadialTest D (referenceBasisProjection I u) := by
  refine ⟨referenceBasisProjection_contDiff hu.1 I,
    reference_periodic_two_pi (referenceBasisProjection_periodic I u), ?_⟩
  obtain ⟨K, hK, hKI, hz⟩ := hu.2.2
  refine ⟨K, hK, hKI, ?_⟩
  intro r hr θ
  change (∑ n ∈ I, referenceRadialCoefficient u n r * referenceAngularBasis n θ) = 0
  apply Finset.sum_eq_zero
  intro n _hn
  rw [referenceRadialCoefficient_zero_outside hz n hr, zero_mul]

theorem referenceCosineProjection_test {D : ReferenceData} {u : PolarPoint → ℝ}
    (hu : RadialTest D u) (J : Finset ℕ) :
    RadialTest D (referenceCosineProjection J u) := by
  rw [referenceCosineProjection_eq_basis]
  exact referenceBasisProjection_test hu _

end

end ContinuousFlexibility.Radial
