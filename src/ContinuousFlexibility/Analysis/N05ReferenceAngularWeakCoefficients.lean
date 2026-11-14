module

public import ContinuousFlexibility.Analysis.N05ReferenceAngularDualBasis
public import ContinuousFlexibility.Analysis.N05ReferenceAngularWeakClosure
public import ContinuousFlexibility.Radial.R11bAngularDerivativeModes

/-!
# All-order Fourier identities of actual weak angular jets

The differentiated phase is an admissible smooth periodic test. Its exact
dual derivative identifies the original source coefficients with the
coefficients of the actual weak jet. Physical L² supplies the required
radial local integrability.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal
open ContinuousFlexibility.Statements

def n05_referenceHighJetCoefficient (d : PolarPoint → ℝ) (b n : ℕ) (r : ℝ) : ℝ :=
  radialAngularMean (fun θ => d (r, θ) * n05_referenceHighJetBasis b n θ)

theorem n05_referenceHighJetCoefficient_eq_pairing
    (d : PolarPoint → ℝ) (b n : ℕ) (r : ℝ) :
    n05_referenceHighJetCoefficient d b n r =
      angularPairing (fun θ => d (r, θ)) (n05_referenceHighJetBasis b n) := by
  simp only [n05_referenceHighJetCoefficient, angularPairing,
    radialAngularMean, angularAverage, one_div]

theorem n05_referenceHighJetCoefficient_memLp {D : ReferenceData}
    {d : PolarPoint → ℝ} (hd : MemLp d 2 (radialPhysicalMeasure D)) (b n : ℕ) :
    MemLp (n05_referenceHighJetCoefficient d b n) 2
      (volume.restrict (radialCore D)) := by
  have h := (r11b_memLp_angularCoefficient hd
    (memLp_angularMeanMeasure (n05_referenceHighJetBasis_memLp b n))).1
  have he : n05_referenceHighJetCoefficient d b n =
      fun r => angularAverage (fun θ => d (r, θ) * n05_referenceHighJetBasis b n θ) := by
    funext r
    simp only [n05_referenceHighJetCoefficient, radialAngularMean, angularAverage, one_div]
  rw [he]
  exact h

theorem n05_referenceHighJetCoefficient_weak_test {D : ReferenceData}
    {u d : PolarPoint → ℝ} {b : ℕ}
    (hder : n05_weakReferenceAngularJet D u d b) (n : ℕ)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ radialCore D) :
    (∫ r in D.a..D.b, n05_referenceHighJetCoefficient d b n r * φ r) =
      (((2 * (n + 2) : ℕ) : ℝ) ^ b) *
        ∫ r in D.a..D.b, referenceRadialCoefficient u (n + 2) r * φ r := by
  have h := hder _ (r11b_radialTest_separated hφ hφc hφs
    (n05_referenceHighJetBasis_contDiff b n)
    (n05_referenceHighJetBasis_periodic b n))
  have hleft (r : ℝ) :
      radialAngularMean (fun θ => d (r, θ) * (φ r * n05_referenceHighJetBasis b n θ)) =
        n05_referenceHighJetCoefficient d b n r * φ r :=
    r11b_radialAngularMean_lift_pairing _ _ _
  have hright (r : ℝ) :
      radialAngularMean (fun θ => u (r, θ) *
        mixedDerivative 0 b
          (fun x : PolarPoint => φ x.1 * n05_referenceHighJetBasis b n x.2) (r, θ)) =
        ((-1 : ℝ) ^ b * (((2 * (n + 2) : ℕ) : ℝ) ^ b)) *
          (referenceRadialCoefficient u (n + 2) r * φ r) := by
    simp only [mixedDerivative, iteratedDeriv_zero,
      iteratedDeriv_const_mul_field, n05_referenceHighJetBasis_dual_derivative]
    have he : (fun θ => u (r, θ) * (φ r *
        (((-1 : ℝ) ^ b * (((2 * (n + 2) : ℕ) : ℝ) ^ b)) *
          referenceAngularBasis (n + 2) θ))) =
        fun θ => (u (r, θ) * referenceAngularBasis (n + 2) θ) *
          (((-1 : ℝ) ^ b * (((2 * (n + 2) : ℕ) : ℝ) ^ b)) * φ r) := by
      funext θ
      ring
    rw [he, r11b_radialAngularMean_mul_const]
    change referenceRadialCoefficient u (n + 2) r *
      (((-1 : ℝ) ^ b * (((2 * (n + 2) : ℕ) : ℝ) ^ b)) * φ r) = _
    ring
  change (∫ r in D.a..D.b, radialAngularMean (fun θ =>
    d (r, θ) * (φ r * n05_referenceHighJetBasis b n θ))) =
      (-1 : ℝ) ^ b * ∫ r in D.a..D.b, radialAngularMean (fun θ =>
        u (r, θ) * mixedDerivative 0 b
          (fun x : PolarPoint => φ x.1 * n05_referenceHighJetBasis b n x.2) (r, θ)) at h
  simp_rw [hleft, hright] at h
  rw [intervalIntegral.integral_const_mul] at h
  have hsign : (-1 : ℝ) ^ b * (-1 : ℝ) ^ b = 1 := by
    rw [← mul_pow]
    norm_num
  simpa only [← mul_assoc, hsign, one_mul] using h

theorem n05_referenceHighJetCoefficient_ae_of_locallyIntegrable
    {D : ReferenceData} (hab : D.a ≤ D.b) {u d : PolarPoint → ℝ} {b : ℕ}
    (hder : n05_weakReferenceAngularJet D u d b) (n : ℕ)
    (hu : LocallyIntegrableOn (referenceRadialCoefficient u (n + 2)) (radialCore D) volume)
    (hd : LocallyIntegrableOn (n05_referenceHighJetCoefficient d b n) (radialCore D) volume) :
    (fun r => (((2 * (n + 2) : ℕ) : ℝ) ^ b) * referenceRadialCoefficient u (n + 2) r)
      =ᵐ[volume.restrict (radialCore D)] n05_referenceHighJetCoefficient d b n := by
  have hloc : LocallyIntegrableOn (fun r =>
      (((2 * (n + 2) : ℕ) : ℝ) ^ b) * referenceRadialCoefficient u (n + 2) r -
        n05_referenceHighJetCoefficient d b n r) (radialCore D) volume := by
    have he : (((2 * (n + 2) : ℕ) : ℝ) ^ b) • referenceRadialCoefficient u (n + 2) -
        n05_referenceHighJetCoefficient d b n =
        fun r => (((2 * (n + 2) : ℕ) : ℝ) ^ b) * referenceRadialCoefficient u (n + 2) r -
          n05_referenceHighJetCoefficient d b n r := by
      funext r
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [← he]
    exact (hu.smul (((2 * (n + 2) : ℕ) : ℝ) ^ b)).sub hd
  have hzero : ∀ᵐ r ∂volume, r ∈ radialCore D →
      (((2 * (n + 2) : ℕ) : ℝ) ^ b) * referenceRadialCoefficient u (n + 2) r -
        n05_referenceHighJetCoefficient d b n r = 0 := by
    apply (show IsOpen (radialCore D) from isOpen_Ioo).ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc
    intro φ hφ hφc hφs
    have huφ := Analysis.integrable_mul_test_of_locallyIntegrableOn_Ioo
      hu hφ.continuous hφc hφs
    have hdφ := Analysis.integrable_mul_test_of_locallyIntegrableOn_Ioo
      hd hφ.continuous hφc hφs
    have ht := n05_referenceHighJetCoefficient_weak_test hder n hφ hφc hφs
    rw [r11b_intervalIntegral_mul_interior_test hab _ _ hφs,
      r11b_intervalIntegral_mul_interior_test hab _ _ hφs] at ht
    have he : (fun r => φ r •
        ((((2 * (n + 2) : ℕ) : ℝ) ^ b) * referenceRadialCoefficient u (n + 2) r -
          n05_referenceHighJetCoefficient d b n r)) =
        fun r => (((2 * (n + 2) : ℕ) : ℝ) ^ b) *
          (referenceRadialCoefficient u (n + 2) r * φ r) -
            n05_referenceHighJetCoefficient d b n r * φ r := by
      funext r
      simp only [smul_eq_mul]
      ring
    rw [he, integral_sub (huφ.const_mul _) hdφ, integral_const_mul, ← ht, sub_self]
  have hz : (fun r =>
      (((2 * (n + 2) : ℕ) : ℝ) ^ b) * referenceRadialCoefficient u (n + 2) r -
        n05_referenceHighJetCoefficient d b n r) =ᵐ[volume.restrict (radialCore D)] 0 := by
    change ∀ᵐ r ∂volume.restrict (radialCore D),
      (((2 * (n + 2) : ℕ) : ℝ) ^ b) * referenceRadialCoefficient u (n + 2) r -
        n05_referenceHighJetCoefficient d b n r = 0
    rw [ae_restrict_iff' (show MeasurableSet (radialCore D) from measurableSet_Ioo)]
    exact hzero
  filter_upwards [hz] with r hr
  exact sub_eq_zero.mp hr

theorem n05_referenceHighJetCoefficient_ae
    {D : ReferenceData} (hab : D.a ≤ D.b) {u d : PolarPoint → ℝ} {b : ℕ}
    (hu : MemLp u 2 (radialPhysicalMeasure D))
    (hd : MemLp d 2 (radialPhysicalMeasure D))
    (hder : n05_weakReferenceAngularJet D u d b) (n : ℕ) :
    (fun r => (((2 * (n + 2) : ℕ) : ℝ) ^ b) * referenceRadialCoefficient u (n + 2) r)
      =ᵐ[volume.restrict (radialCore D)] n05_referenceHighJetCoefficient d b n := by
  letI : IsFiniteMeasure (volume.restrict (radialCore D)) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact (measure_mono (show radialCore D ⊆ Icc D.a D.b from Ioo_subset_Icc_self)).trans_lt
      isCompact_Icc.measure_lt_top⟩
  have huL2 : MemLp (referenceRadialCoefficient u (n + 2)) 2
      (volume.restrict (radialCore D)) := by
    apply memLp_referenceRadialCoefficient_prod
    simpa only [radialPhysicalMeasure_eq_prod] using hu
  have huL1 := MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2) huL2
  have hdL1 := MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    (n05_referenceHighJetCoefficient_memLp hd b n)
  exact n05_referenceHighJetCoefficient_ae_of_locallyIntegrable hab hder n
    (IntegrableOn.locallyIntegrableOn huL1) (IntegrableOn.locallyIntegrableOn hdL1)

end ContinuousFlexibility.Radial
