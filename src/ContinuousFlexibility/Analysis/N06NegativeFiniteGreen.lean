import ContinuousFlexibility.Analysis.N06FiniteWeakGreen
import ContinuousFlexibility.Analysis.N06HalfPhysicalPairing

/-!
# Negative canonical principal Green formula with actual endpoint traces

The principal coefficients are the literal negative normal form `(1, 0, -y)`.
The finite field is assembled from C1 representatives with AC first derivative
and L2 second derivative. The existing weak Green formula therefore applies
without smooth radial modes or vanishing endpoint tests.

The full-circle formula uses the original unnormalized physical measure on
`(a,b) x (0,2*pi]`. Its half-circle version uses exactly the unnormalized
canonical measure on `(a,b) x (0,pi]`; both bulk and boundary integrals are
halved. Thus no additional pi factor is present in the canonical identity.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Radial ContinuousFlexibility.Statements
open scoped BigOperators ContDiff Topology

set_option backward.isDefEq.respectTransparency false

/-- The actual negative principal expression applied to a smooth test. -/
def n06NegativePrincipalTest (φ : PolarPoint → ℝ) (p : PolarPoint) : ℝ :=
  radialPartial (radialPartial φ) p - p.1 * angularPartial (angularPartial φ) p

private theorem negative_coefficient_angular (p : PolarPoint) :
    angularPartial (fun q : PolarPoint => -q.1) p = 0 := by
  have hd : HasFDerivAt (fun q : PolarPoint => -q.1)
      (-(ContinuousLinearMap.fst ℝ ℝ ℝ)) p := hasFDerivAt_fst.neg
  simp only [angularPartial, hd.fderiv]
  change -(0 : ℝ) = 0
  exact neg_zero

theorem n06_negativePrincipal_divergence {φ : PolarPoint → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (p : PolarPoint) :
    divergenceOperator ⟨fun _ => 1, fun _ => 0, fun q => -q.1⟩ φ p =
      n06NegativePrincipalTest φ p := by
  rw [divergenceOperator_expansion contDiff_const contDiff_const contDiff_fst.neg hφ]
  simp only [n06NegativePrincipalTest, radialPartial_const, angularPartial_const,
    negative_coefficient_angular, zero_mul, mul_zero, one_mul, zero_add, add_zero,
    neg_mul, sub_eq_add_neg]

private theorem negativePrincipal_contDiff {φ : PolarPoint → ℝ}
    (hφ : ContDiff ℝ ∞ φ) : ContDiff ℝ ∞ (n06NegativePrincipalTest φ) :=
  (contDiff_cylinder_radialPartial (contDiff_cylinder_radialPartial hφ)).sub
    (contDiff_fst.mul
      (contDiff_cylinder_angularPartial (contDiff_cylinder_angularPartial hφ)))

private theorem finiteMixed_periodic (s : Finset ℕ) (v : ℕ → ℝ → ℝ) (a b : ℕ) :
    Function.Periodic (n06FiniteMixedField s v a b) (0, Real.pi) := by
  intro p
  unfold n06FiniteMixedField r11bFiniteSynthesis
  simp only [Prod.fst_add, Prod.snd_add, add_zero]
  exact Finset.sum_congr rfl (fun i _ => congrArg
    (fun t => iteratedDeriv a (v i) p.1 * t)
      (circleFourier_periodic_iteratedDeriv (referenceAngularBasis_periodic i) b p.2))

/-- The full-circle weak Green identity, with its genuine endpoint
Wronskians. No matching or global weak equation is assumed. -/
theorem n06_finite_negative_principal_green {D : ReferenceData} (hab : D.a ≤ D.b)
    (s : Finset ℕ) (v : ℕ → ℝ → ℝ)
    (hC : ∀ i ∈ s, ContDiff ℝ 1 (v i))
    (hAC : ∀ i ∈ s, AbsolutelyContinuousOnInterval (deriv (v i)) D.a D.b)
    (hv : ∀ i ∈ s, MemLp (v i) 2 (volume.restrict (radialCore D)))
    (hv₁ : ∀ i ∈ s, MemLp (deriv (v i)) 2 (volume.restrict (radialCore D)))
    (hv₂ : ∀ i ∈ s, MemLp (deriv (deriv (v i))) 2 (volume.restrict (radialCore D)))
    {φ : PolarPoint → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφp : Function.Periodic φ (0, 2 * Real.pi)) :
    (∫ p, (n06FiniteMixedField s v 2 0 p - p.1 * n06FiniteMixedField s v 0 2 p) * φ p
      ∂radialPhysicalMeasure D) -
      (∫ p, r11bFiniteSynthesis s v referenceAngularBasis p * n06NegativePrincipalTest φ p
        ∂radialPhysicalMeasure D) =
      ∫ θ in (0 : ℝ)..2 * Real.pi,
        (φ (D.b, θ) * radialPartial (r11bFiniteSynthesis s v referenceAngularBasis) (D.b, θ) -
          r11bFiniteSynthesis s v referenceAngularBasis (D.b, θ) * radialPartial φ (D.b, θ)) -
        (φ (D.a, θ) * radialPartial (r11bFiniteSynthesis s v referenceAngularBasis) (D.a, θ) -
          r11bFiniteSynthesis s v referenceAngularBasis (D.a, θ) * radialPartial φ (D.a, θ)) := by
  let L : SymmetricCoefficients := ⟨fun _ => 1, fun _ => 0, fun p => -p.1⟩
  have hpa : Function.Periodic L.a (0, 2 * Real.pi) := fun _ => rfl
  have hpb : Function.Periodic L.b (0, 2 * Real.pi) := fun _ => rfl
  have hpc : Function.Periodic L.c (0, 2 * Real.pi) := by
    intro p
    simp only [L, Prod.fst_add, add_zero]
  have hg := n06_finite_weak_physical_green hab s v hC hAC hv hv₁ hv₂ L
    contDiff_const contDiff_const contDiff_fst.neg hpa hpb hpc hφ hφp
  simpa only [L, n06WeakDivergenceExpression, radialPartial_const, angularPartial_const,
    negative_coefficient_angular, zero_mul, mul_zero, one_mul, zero_add, add_zero,
    neg_mul, ← sub_eq_add_neg, n06_negativePrincipal_divergence hφ,
    greenNormalFlux, symmetricNormalFlux] using hg

/-- For a pi-periodic integrable field on any finite radial strip, the
full physical integral is twice its original half-period integral. -/
theorem n06_fullStrip_integral_eq_two_half {D : ReferenceData} (hab : D.a ≤ D.b)
    {f : PolarPoint → ℝ} (hp : Function.Periodic f (0, Real.pi))
    (hf : Integrable f (radialPhysicalMeasure D)) :
    (∫ p, f p ∂radialPhysicalMeasure D) =
      2 * ∫ p in radialCore D ×ˢ Ioc (0 : ℝ) Real.pi, f p := by
  have hμle : volume.restrict (radialCore D ×ˢ Ioc (0 : ℝ) Real.pi) ≤
      radialPhysicalMeasure D :=
    Measure.restrict_mono (Set.prod_mono subset_rfl
      (Ioc_subset_Ioc_right (by linarith [Real.pi_pos]))) le_rfl
  have hh : IntegrableOn f (radialCore D ×ˢ Ioc (0 : ℝ) Real.pi) := hf.mono_measure hμle
  have hm := n06_physicalMean_eq_halfIntegral hab hp hh
  rw [r11b_integral_angularMean_eq hab hf] at hm
  apply mul_left_cancel₀ (inv_ne_zero (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero))
  calc
    (2 * Real.pi)⁻¹ * (∫ p, f p ∂radialPhysicalMeasure D) =
        Real.pi⁻¹ * ∫ p in radialCore D ×ˢ Ioc (0 : ℝ) Real.pi, f p := hm
    _ = (2 * Real.pi)⁻¹ *
        (2 * ∫ p in radialCore D ×ˢ Ioc (0 : ℝ) Real.pi, f p) := by
      field_simp [Real.pi_ne_zero]
      <;> ring

private theorem interval_integral_two_period {f : ℝ → ℝ}
    (hp : Function.Periodic f Real.pi) (hc : Continuous f) :
    (∫ θ in (0 : ℝ)..2 * Real.pi, f θ) = 2 * ∫ θ in (0 : ℝ)..Real.pi, f θ := by
  have hs : (∫ θ in Real.pi..2 * Real.pi, f θ) = ∫ θ in (0 : ℝ)..Real.pi, f θ := by
    simpa only [zero_add, ← two_mul] using hp.intervalIntegral_add_eq Real.pi 0
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable 0 Real.pi) (hc.intervalIntegrable Real.pi (2 * Real.pi)), hs]
  ring

/-- The same actual finite Green identity in the unnormalized canonical
half-period measure. The test is unrestricted at both radial endpoints. -/
theorem n06_finite_negative_principal_green_half {D : ReferenceData} (hab : D.a ≤ D.b)
    (s : Finset ℕ) (v : ℕ → ℝ → ℝ)
    (hC : ∀ i ∈ s, ContDiff ℝ 1 (v i))
    (hAC : ∀ i ∈ s, AbsolutelyContinuousOnInterval (deriv (v i)) D.a D.b)
    (hv : ∀ i ∈ s, MemLp (v i) 2 (volume.restrict (radialCore D)))
    (hv₁ : ∀ i ∈ s, MemLp (deriv (v i)) 2 (volume.restrict (radialCore D)))
    (hv₂ : ∀ i ∈ s, MemLp (deriv (deriv (v i))) 2 (volume.restrict (radialCore D)))
    {φ : PolarPoint → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφp : Function.Periodic φ (0, Real.pi)) :
    (∫ p in radialCore D ×ˢ Ioc (0 : ℝ) Real.pi,
      (n06FiniteMixedField s v 2 0 p - p.1 * n06FiniteMixedField s v 0 2 p) * φ p) -
      (∫ p in radialCore D ×ˢ Ioc (0 : ℝ) Real.pi,
        r11bFiniteSynthesis s v referenceAngularBasis p * n06NegativePrincipalTest φ p) =
      ∫ θ in (0 : ℝ)..Real.pi,
        (φ (D.b, θ) * radialPartial (r11bFiniteSynthesis s v referenceAngularBasis) (D.b, θ) -
          r11bFiniteSynthesis s v referenceAngularBasis (D.b, θ) * radialPartial φ (D.b, θ)) -
        (φ (D.a, θ) * radialPartial (r11bFiniteSynthesis s v referenceAngularBasis) (D.a, θ) -
          r11bFiniteSynthesis s v referenceAngularBasis (D.a, θ) * radialPartial φ (D.a, θ)) := by
  let U := n06FiniteMixedField s v 0 0
  let Ur := n06FiniteMixedField s v 1 0
  let Q : PolarPoint → ℝ := fun p =>
    n06FiniteMixedField s v 2 0 p - p.1 * n06FiniteMixedField s v 0 2 p
  let J : PolarPoint → ℝ := fun p => φ p * Ur p - U p * radialPartial φ p
  have hrow := n06_finiteMixedField_physical_weakH2 hab s v hC hAC hv hv₁ hv₂
  have hU : U = r11bFiniteSynthesis s v referenceAngularBasis := by
    simp only [U, n06FiniteMixedField, iteratedDeriv_zero]
  have hQint : Integrable (fun p => Q p * φ p) (radialPhysicalMeasure D) := by
    have h₁ : Integrable (fun p => n06FiniteMixedField s v 2 0 p * φ p)
        (radialPhysicalMeasure D) :=
      hrow.radial_radial_memLp.integrable_mul (r11b_continuous_memLp hφ.continuous)
    have h₂ : Integrable (fun p => n06FiniteMixedField s v 0 2 p * (p.1 * φ p))
        (radialPhysicalMeasure D) := hrow.angular_angular_memLp.integrable_mul
      (r11b_continuous_memLp (continuous_fst.mul hφ.continuous))
    apply (h₁.sub h₂).congr
    filter_upwards with p
    simp only [Q, Pi.sub_apply]
    ring
  have hTint : Integrable (fun p => U p * n06NegativePrincipalTest φ p)
      (radialPhysicalMeasure D) :=
    hrow.value_memLp.integrable_mul (r11b_continuous_memLp (negativePrincipal_contDiff hφ).continuous)
  have hpU : Function.Periodic U (0, Real.pi) := finiteMixed_periodic s v 0 0
  have hpUr : Function.Periodic Ur (0, Real.pi) := finiteMixed_periodic s v 1 0
  have hpfst : Function.Periodic (fun p : PolarPoint => p.1) (0, Real.pi) := by
    intro p
    simp only [Prod.fst_add, add_zero]
  have hpQ : Function.Periodic Q (0, Real.pi) :=
    (finiteMixed_periodic s v 2 0).sub (hpfst.mul (finiteMixed_periodic s v 0 2))
  have hpT : Function.Periodic (n06NegativePrincipalTest φ) (0, Real.pi) :=
    (periodic_radialPartial (periodic_radialPartial hφp)).sub
      (hpfst.mul (periodic_angularPartial (periodic_angularPartial hφp)))
  have hpJ : Function.Periodic J (0, Real.pi) :=
    (hφp.mul hpUr).sub (hpU.mul (periodic_radialPartial hφp))
  have hcJ : Continuous J :=
    (hφ.continuous.mul hrow.radial_continuous).sub
      (hrow.value_continuous.mul (contDiff_cylinder_radialPartial hφ).continuous)
  have hpB : Function.Periodic (fun θ => J (D.b, θ) - J (D.a, θ)) Real.pi := by
    intro θ
    simpa only [Prod.mk_add_mk, add_zero] using
      congrArg₂ (fun x y : ℝ => x - y) (hpJ (D.b, θ)) (hpJ (D.a, θ))
  have hcB : Continuous (fun θ => J (D.b, θ) - J (D.a, θ)) :=
    (hcJ.comp (continuous_const.prodMk continuous_id)).sub
      (hcJ.comp (continuous_const.prodMk continuous_id))
  have hg := n06_finite_negative_principal_green hab s v hC hAC hv hv₁ hv₂ hφ
    (reference_periodic_two_pi hφp)
  have hboundary (p : PolarPoint) :
      φ p * radialPartial (r11bFiniteSynthesis s v referenceAngularBasis) p -
        r11bFiniteSynthesis s v referenceAngularBasis p * radialPartial φ p = J p := by
    rw [← hU, hrow.radial_value]
  simp_rw [hboundary] at hg ⊢
  rw [← hU] at hg ⊢
  change (∫ p, Q p * φ p ∂radialPhysicalMeasure D) -
    (∫ p, U p * n06NegativePrincipalTest φ p ∂radialPhysicalMeasure D) = _ at hg
  rw [n06_fullStrip_integral_eq_two_half hab (f := fun p => Q p * φ p)
      (hpQ.mul hφp) hQint,
    n06_fullStrip_integral_eq_two_half hab (f := fun p => U p * n06NegativePrincipalTest φ p)
      (hpU.mul hpT) hTint,
    interval_integral_two_period hpB hcB] at hg
  change (∫ p in radialCore D ×ˢ Ioc (0 : ℝ) Real.pi, Q p * φ p) -
    (∫ p in radialCore D ×ˢ Ioc (0 : ℝ) Real.pi, U p * n06NegativePrincipalTest φ p) = _
  linarith only [hg]

end ContinuousFlexibility.Analysis
