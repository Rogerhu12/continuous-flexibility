import ContinuousFlexibility.Analysis.N05PeriodicPhysicalL2Norm
import ContinuousFlexibility.Analysis.CylinderTestPeriodization
import ContinuousFlexibility.Radial.R11bPhysicalPairing
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Uniqueness of the actual periodic physical normal derivative

Compact planar tests can be periodized inside the physical half-period.
The full physical test pairing separates pi-periodic L² fields. Therefore
two periodic physical normal derivatives of the same field coincide in
the actual physical measure, with no additional endpoint conditions.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped ContDiff Topology
open ContinuousFlexibility.Statements

theorem n05_referenceTest_of_periodization {D : ReferenceData}
    {φ : PolarPoint → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ radialCore D ×ˢ Ioo (0 : ℝ) Real.pi) :
    RadialTest D (cylinderTestPeriodization φ) := by
  have ht := isCylinderTest_cylinderTestPeriodization hφ hc
  refine ⟨ht.1, ?_, Prod.fst '' tsupport φ, hc.image continuous_fst, ?_, ?_⟩
  · intro p
    have he : p + ((0, 2 * Real.pi) : PolarPoint) =
        (p + (0, Real.pi)) + (0, Real.pi) := by
      ext <;> simp only [Prod.fst_add, Prod.snd_add, add_zero] <;> ring
    rw [he, ht.2.1, ht.2.1]
  · rintro r ⟨p, hp, rfl⟩
    exact (hs hp).1
  · intro r hr θ
    unfold cylinderTestPeriodization
    have hz (k : ℤ) : φ (cylinderAngularShift k (r, θ)) = 0 := by
      by_contra hk
      exact hr ⟨cylinderAngularShift k (r, θ), subset_tsupport φ hk, rfl⟩
    simp only [hz, tsum_zero]

theorem n05_referencePeriodization_eq {D : ReferenceData} {φ : PolarPoint → ℝ}
    (hs : tsupport φ ⊆ radialCore D ×ˢ Ioo (0 : ℝ) Real.pi)
    (p : PolarPoint) (hp : p.2 ∈ Ioc (0 : ℝ) Real.pi) :
    cylinderTestPeriodization φ p = φ p := by
  have hz (k : ℤ) (hk : k ≠ 0) : φ (cylinderAngularShift k p) = 0 := by
    by_contra hφ
    have hθ := (hs (subset_tsupport φ hφ)).2
    change 0 < p.2 + k • Real.pi ∧ p.2 + k • Real.pi < Real.pi at hθ
    simp only [zsmul_eq_mul] at hθ
    have hk' : k ≤ -1 ∨ 1 ≤ k := by omega
    rcases hk' with hneg | hpos
    · have hneg' : (k : ℝ) ≤ -1 := by exact_mod_cast hneg
      have hm := mul_le_mul_of_nonneg_right hneg' Real.pi_pos.le
      linarith only [hθ.1, hp.2, hm]
    · have hpos' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hpos
      have hm := mul_le_mul_of_nonneg_right hpos' Real.pi_pos.le
      linarith only [hθ.2, hp.1, hm]
  calc
    cylinderTestPeriodization φ p = φ (cylinderAngularShift 0 p) := tsum_eq_single 0 hz
    _ = φ p := by
      change φ (p.1, p.2 + (0 : ℤ) • Real.pi) = φ p
      simp only [zero_zsmul, add_zero, Prod.mk.eta]

theorem n05_periodicPhysical_ae_eq_zero_of_test {D : ReferenceData}
    (hab : D.a ≤ D.b) {u : PolarPoint → ℝ}
    (hu : MemLp u 2 (radialPhysicalMeasure D))
    (hp : Function.Periodic u (0, Real.pi))
    (hz : ∀ ψ, RadialTest D ψ →
      (∫ r in D.a..D.b, radialAngularMean (fun θ => u (r, θ) * ψ (r, θ))) = 0) :
    u =ᵐ[radialPhysicalMeasure D] (0 : PolarPoint → ℝ) := by
  let μ : Measure PolarPoint := volume.restrict (radialCore D ×ˢ Ioc (0 : ℝ) Real.pi)
  let U : Set PolarPoint := radialCore D ×ˢ Ioo (0 : ℝ) Real.pi
  have hU : IsOpen U := isOpen_Ioo.prod isOpen_Ioo
  have hμ : μ = volume.restrict U := by
    have ha : (volume : Measure ℝ).restrict (Ioc (0 : ℝ) Real.pi) =
        (volume : Measure ℝ).restrict (Ioo (0 : ℝ) Real.pi) :=
      (Measure.restrict_congr_set Ioo_ae_eq_Ioc).symm
    change ((volume : Measure ℝ).prod volume).restrict
      (radialCore D ×ˢ Ioc (0 : ℝ) Real.pi) =
      ((volume : Measure ℝ).prod volume).restrict U
    dsimp only [U]
    rw [← Measure.prod_restrict, ← Measure.prod_restrict, ha]
  have hμle : μ ≤ radialPhysicalMeasure D := by
    apply Measure.restrict_mono _ le_rfl
    intro p hp'
    exact ⟨hp'.1, hp'.2.1, hp'.2.2.trans (by linarith [Real.pi_pos])⟩
  letI : IsFiniteMeasure (radialPhysicalMeasure D) := ⟨r11b_radialPhysicalMeasure_finite D⟩
  have hi : LocallyIntegrableOn u U μ :=
    ((hu.integrable (by norm_num)).mono_measure hμle).locallyIntegrable.locallyIntegrableOn U
  have hzero : ∀ᵐ p ∂μ, p ∈ U → u p = 0 := by
    apply hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero hi
    intro φ hφ hc hs
    have ht := n05_referenceTest_of_periodization hφ hc hs
    have htLp : MemLp (cylinderTestPeriodization φ) 2 (radialPhysicalMeasure D) :=
      r11b_continuous_memLp ht.1.continuous
    have htp := (isCylinderTest_cylinderTestPeriodization hφ hc).2.1
    have hperiodic : Function.Periodic
        (fun p => u p * cylinderTestPeriodization φ p) (0, Real.pi) := by
      simpa only [Pi.mul_def] using hp.mul htp
    have hfull := n05_piPeriodic_integral_fullPeriod (J := radialCore D) measurableSet_Ioo
      hperiodic (hu.integrable_mul htLp)
    have hmean : (2 * Real.pi)⁻¹ *
        ∫ p, u p * cylinderTestPeriodization φ p ∂radialPhysicalMeasure D = 0 :=
      (r11b_integral_angularMean_mul_eq hab hu htLp).symm.trans (hz _ ht)
    have hfullzero := (mul_eq_zero.mp hmean).resolve_left
      (inv_ne_zero (by positivity : (2 * Real.pi) ≠ 0))
    change (∫ p, u p * cylinderTestPeriodization φ p
      ∂volume.restrict (radialCore D ×ˢ Ioc (0 : ℝ) (2 * Real.pi))) = 0 at hfullzero
    rw [hfull] at hfullzero
    change 2 * (∫ p, u p * cylinderTestPeriodization φ p ∂μ) = 0 at hfullzero
    have hhalfzero : (∫ p, u p * cylinderTestPeriodization φ p ∂μ) = 0 := by
      linarith only [hfullzero]
    calc
      (∫ p, φ p • u p ∂μ) =
          ∫ p, u p * cylinderTestPeriodization φ p ∂μ := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)] with p hp'
        change φ p • u p = u p * cylinderTestPeriodization φ p
        rw [n05_referencePeriodization_eq hs p hp'.2]
        simp only [smul_eq_mul, mul_comm]
      _ = 0 := hhalfzero
  have hmem : ∀ᵐ p ∂μ, p ∈ U := by
    rw [hμ]
    exact ae_restrict_mem hU.measurableSet
  have hhalf : u =ᵐ[μ] (0 : PolarPoint → ℝ) := by
    filter_upwards [hzero, hmem] with p hp' hpm
    exact hp' hpm
  exact n05_piPeriodic_ae_eq_fullPeriod measurableSet_Ioo hp (fun _ => rfl) hhalf

theorem n05_weakNormalDerivative_unique_periodic {D : ReferenceData}
    (hab : D.a ≤ D.b) {u d e : PolarPoint → ℝ}
    (hdLp : MemLp d 2 (radialPhysicalMeasure D))
    (heLp : MemLp e 2 (radialPhysicalMeasure D))
    (hdp : Function.Periodic d (0, Real.pi))
    (hep : Function.Periodic e (0, Real.pi))
    (hd : WeakNormalDerivative D u d) (he : WeakNormalDerivative D u e) :
    d =ᵐ[radialPhysicalMeasure D] e := by
  have hz : d - e =ᵐ[radialPhysicalMeasure D] (0 : PolarPoint → ℝ) := by
    apply n05_periodicPhysical_ae_eq_zero_of_test hab (hdLp.sub heLp) (hdp.sub hep)
    intro ψ hψ
    have hψLp : MemLp ψ 2 (radialPhysicalMeasure D) :=
      r11b_continuous_memLp hψ.1.continuous
    have hsame :
        (∫ r in D.a..D.b, radialAngularMean (fun θ => d (r, θ) * ψ (r, θ))) =
        ∫ r in D.a..D.b, radialAngularMean (fun θ => e (r, θ) * ψ (r, θ)) := by
      linarith only [hd ψ hψ, he ψ hψ]
    rw [r11b_integral_angularMean_mul_eq hab (hdLp.sub heLp) hψLp]
    have hfun : (fun p => (d - e) p * ψ p) =
        (fun p => d p * ψ p - e p * ψ p) := by
      funext p
      simp only [Pi.sub_apply, sub_mul]
    have hdψInt : Integrable (fun p => d p * ψ p) (radialPhysicalMeasure D) :=
      hdLp.integrable_mul hψLp
    have heψInt : Integrable (fun p => e p * ψ p) (radialPhysicalMeasure D) :=
      heLp.integrable_mul hψLp
    rw [hfun, integral_sub hdψInt heψInt,
      mul_sub, ← r11b_integral_angularMean_mul_eq hab hdLp hψLp,
      ← r11b_integral_angularMean_mul_eq hab heLp hψLp, hsame, sub_self]
  filter_upwards [hz] with p hp'
  exact sub_eq_zero.mp hp'

end ContinuousFlexibility.Radial
