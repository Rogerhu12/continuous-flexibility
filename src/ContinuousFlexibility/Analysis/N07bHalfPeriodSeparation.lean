import ContinuousFlexibility.Analysis.N07bHalfPeriodTests
import ContinuousFlexibility.Radial.R11bPhysicalPairing
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Local distributional separation on a physical half-period

Full-period radial tests detect every compact planar test in the open
half-period strip. The exact pairing identity below retains the angular
normalization and proves integrability before using Fubini. Consequently
the weak test pairing separates arbitrary locally integrable sources on
any open subset of that strip.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements
open scoped ContDiff

/-- A continuous compact test inside a local integrability domain gives an
actual globally integrable product. -/
theorem n07b_integrable_mul_compact_test {A : Set PolarPoint}
    {f φ : PolarPoint → ℝ} (hf : LocallyIntegrableOn f A volume)
    (hφ : Continuous φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ A) :
    Integrable (fun p => f p * φ p) volume := by
  have hi : IntegrableOn (fun p => f p * φ p) (tsupport φ) volume :=
    (hf.integrableOn_compact_subset hs hc).mul_continuousOn hφ.continuousOn hc
  apply (integrableOn_iff_integrable_of_support_subset ?_).mp hi
  intro p hp
  exact subset_tsupport φ (mul_ne_zero_iff.mp hp).2

/-- The full-period weak pairing with a periodized compact test is exactly
the ordinary planar distribution pairing, times the prescribed normalization.
The source is only assumed locally integrable where the compact test lives. -/
theorem n07b_halfPeriodTest_pairing {D : ReferenceData} (hab : D.a ≤ D.b)
    {A : Set PolarPoint} (hA : A ⊆ radialCore D ×ˢ Ioo (0 : ℝ) Real.pi)
    {f φ : PolarPoint → ℝ} (hf : LocallyIntegrableOn f A volume)
    (hφ : Continuous φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ A) :
    (∫ r in D.a..D.b, radialAngularMean (fun θ =>
      f (r, θ) * n07bFullPeriodTest φ (r, θ))) =
        (2 * Real.pi)⁻¹ * ∫ p, f p * φ p := by
  have hi := n07b_integrable_mul_compact_test hf hφ hc hs
  have hsupport : tsupport φ ⊆ (univ : Set ℝ) ×ˢ Ioo (0 : ℝ) Real.pi :=
    fun p hp => ⟨mem_univ _, (hA (hs hp)).2⟩
  have he :
      (fun p => f p * n07bFullPeriodTest φ p) =ᵐ[radialPhysicalMeasure D]
        (fun p => f p * φ p) := by
    filter_upwards [ae_restrict_mem
      (show MeasurableSet (radialCore D ×ˢ Ioc (0 : ℝ) (2 * Real.pi)) from
        measurableSet_Ioo.prod measurableSet_Ioc)] with p hp
    change f p * n07bFullPeriodTest φ p = f p * φ p
    rw [n07bFullPeriodTest_eqOn hsupport ⟨mem_univ _, hp.2⟩]
  have hip : Integrable (fun p => f p * n07bFullPeriodTest φ p)
      (radialPhysicalMeasure D) :=
    hi.integrableOn.congr he.symm
  rw [Radial.r11b_integral_angularMean_eq hab hip, integral_congr_ae he]
  congr 1
  change (∫ p in radialCore D ×ˢ Ioc (0 : ℝ) (2 * Real.pi), f p * φ p) =
    ∫ p, f p * φ p
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro p hp
  have hzero : φ p = 0 := image_eq_zero_of_notMem_tsupport (fun h => by
    have hpin := hA (hs h)
    exact hp ⟨hpin.1, ⟨hpin.2.1,
      hpin.2.2.le.trans (by linarith [Real.pi_pos])⟩⟩)
  change f p * φ p = 0
  rw [hzero, mul_zero]

/-- Compact half-period radial pairings separate a locally integrable raw
source on every open part of the physical half-period. -/
theorem n07b_ae_eq_zero_of_halfPeriod_pairing {D : ReferenceData}
    (hab : D.a ≤ D.b) {A : Set PolarPoint} (hopen : IsOpen A)
    (hA : A ⊆ radialCore D ×ˢ Ioo (0 : ℝ) Real.pi)
    {f : PolarPoint → ℝ} (hf : LocallyIntegrableOn f A volume)
    (hpair : ∀ φ : PolarPoint → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ A →
      (∫ r in D.a..D.b, radialAngularMean (fun θ =>
        f (r, θ) * n07bFullPeriodTest φ (r, θ))) = 0) :
    ∀ᵐ p ∂volume.restrict A, f p = 0 := by
  rw [ae_restrict_iff' hopen.measurableSet]
  apply hopen.ae_eq_zero_of_integral_contDiff_smul_eq_zero hf
  intro φ hφ hc hs
  have h := hpair φ hφ hc hs
  rw [n07b_halfPeriodTest_pairing hab hA hf hφ.continuous hc hs] at h
  have hnorm : (2 * Real.pi)⁻¹ ≠ 0 := inv_ne_zero (by positivity)
  have hraw : (∫ p, f p * φ p) = 0 := (mul_eq_zero.mp h).resolve_left hnorm
  simpa only [smul_eq_mul, mul_comm] using hraw

/-- Equality of the local full-period pairings determines the source a.e.
on the open half-period domain. -/
theorem n07b_ae_eq_of_halfPeriod_pairing {D : ReferenceData}
    (hab : D.a ≤ D.b) {A : Set PolarPoint} (hopen : IsOpen A)
    (hA : A ⊆ radialCore D ×ˢ Ioo (0 : ℝ) Real.pi)
    {f g : PolarPoint → ℝ} (hf : LocallyIntegrableOn f A volume)
    (hg : LocallyIntegrableOn g A volume)
    (hpair : ∀ φ : PolarPoint → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ A →
      (∫ r in D.a..D.b, radialAngularMean (fun θ =>
        f (r, θ) * n07bFullPeriodTest φ (r, θ))) =
      ∫ r in D.a..D.b, radialAngularMean (fun θ =>
        g (r, θ) * n07bFullPeriodTest φ (r, θ))) :
    f =ᵐ[volume.restrict A] g := by
  have hlocal : LocallyIntegrableOn (fun p => f p - g p) A volume := by
    simpa only [Pi.sub_apply] using hf.sub hg
  have hzero : ∀ᵐ p ∂volume, p ∈ A → f p - g p = 0 := by
    apply hopen.ae_eq_zero_of_integral_contDiff_smul_eq_zero hlocal
    intro φ hφ hc hs
    have h := hpair φ hφ hc hs
    rw [n07b_halfPeriodTest_pairing hab hA hf hφ.continuous hc hs,
      n07b_halfPeriodTest_pairing hab hA hg hφ.continuous hc hs] at h
    have hnorm : (2 * Real.pi)⁻¹ ≠ 0 := inv_ne_zero (by positivity)
    have he : (∫ p, f p * φ p) = ∫ p, g p * φ p := mul_left_cancel₀ hnorm h
    have hfi := n07b_integrable_mul_compact_test hf hφ.continuous hc hs
    have hgi := n07b_integrable_mul_compact_test hg hφ.continuous hc hs
    simp only [smul_eq_mul, mul_sub]
    calc
      (∫ p, φ p * f p - φ p * g p) =
          (∫ p, f p * φ p) - ∫ p, g p * φ p := by
        simpa only [mul_comm] using integral_sub hfi hgi
      _ = 0 := sub_eq_zero.mpr he
  change ∀ᵐ p ∂volume.restrict A, f p = g p
  rw [ae_restrict_iff' hopen.measurableSet]
  filter_upwards [hzero] with p hp hpA
  exact sub_eq_zero.mp (hp hpA)

/-- In particular, equality against every actual radial test separates raw
locally integrable sources on a physical half-period subdomain. -/
theorem n07b_ae_eq_of_radialTest_pairing {D : ReferenceData}
    (hab : D.a ≤ D.b) {A : Set PolarPoint} (hopen : IsOpen A)
    (hA : A ⊆ radialCore D ×ˢ Ioo (0 : ℝ) Real.pi)
    {f g : PolarPoint → ℝ} (hf : LocallyIntegrableOn f A volume)
    (hg : LocallyIntegrableOn g A volume)
    (hpair : ∀ φ : PolarPoint → ℝ, RadialTest D φ →
      (∫ r in D.a..D.b, radialAngularMean (fun θ => f (r, θ) * φ (r, θ))) =
      ∫ r in D.a..D.b, radialAngularMean (fun θ => g (r, θ) * φ (r, θ))) :
    f =ᵐ[volume.restrict A] g := by
  apply n07b_ae_eq_of_halfPeriod_pairing hab hopen hA hf hg
  intro φ hφ hc hs
  exact hpair (n07bFullPeriodTest φ)
    (n07bFullPeriodTest_radialTest hφ hc (hs.trans hA))

end ContinuousFlexibility.Analysis
