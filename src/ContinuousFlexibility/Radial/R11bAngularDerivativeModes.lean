import ContinuousFlexibility.Radial.R11bWeakModes
import ContinuousFlexibility.Radial.R11bAngularL2Bridge
import ContinuousFlexibility.Analysis.IntervalWeakPrimitive

/-!
# The a.e. Fourier identity of an actual weak angular derivative

The derivative is paired with sine modes. It is not required to be even or to
belong to the even source space. The fundamental lemma identifies the radial
coefficient functions themselves, after their local integrability is supplied.
-/

namespace ContinuousFlexibility.Radial

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff Topology
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

def referenceSineMode (u : PolarPoint → ℝ) (j : ℕ) (r : ℝ) : ℝ :=
  radialAngularMean (fun θ => u (r, θ) * sineMode j θ)

theorem r11b_referenceSineMode_L2_bound {D : ReferenceData} {f : PolarPoint → ℝ}
    (hf : MemLp f 2 (radialPhysicalMeasure D)) (j : ℕ) (hj : 0 < j) :
    MemLp (referenceSineMode f j) 2 (volume.restrict (radialCore D)) ∧
      (∫ r, referenceSineMode f j r ^ 2 ∂volume.restrict (radialCore D)) ≤
        (1 / (2 * Real.pi)) * ∫ z, f z ^ 2 ∂radialPhysicalMeasure D := by
  have he : MemLp (sineMode j) 2 angularMeanMeasure :=
    memLp_angularMeanMeasure (angularInterval_memLp_of_continuous (continuous_sineMode j))
  have hunit : angularAverage (fun θ => sineMode j θ ^ 2) = 1 := by
    simpa only [angularPairing, pow_two, if_pos rfl] using
      angularPairing_sineMode j j hj hj
  have h := r11b_memLp_angularCoefficient hf he
  rw [hunit, one_mul] at h
  have hmode : referenceSineMode f j =
      fun r => angularAverage (fun θ => f (r, θ) * sineMode j θ) := by
    funext r
    simp only [referenceSineMode, radialAngularMean, angularAverage, one_div]
  rw [hmode]
  exact h

theorem r11b_intervalIntegral_mul_interior_test {a b : ℝ} (hab : a ≤ b)
    (v φ : ℝ → ℝ) (hφs : tsupport φ ⊆ Ioo a b) :
    (∫ r in a..b, v r * φ r) = ∫ r, v r * φ r := by
  rw [intervalIntegral.integral_of_le hab]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro r hr
  have hzero : φ r = 0 := image_eq_zero_of_notMem_tsupport
    (fun ht => hr (Ioo_subset_Ioc_self (hφs ht)))
  rw [hzero, mul_zero]

theorem r11b_weakAngular_referenceMode_ae_of_locallyIntegrable
    {D : ReferenceData} (hab : D.a ≤ D.b) {u d : PolarPoint → ℝ}
    (hder : WeakAngularDerivative D u d) (j : ℕ)
    (hu : LocallyIntegrableOn (referenceMode u j) (radialCore D) volume)
    (hd : LocallyIntegrableOn (referenceSineMode d j) (radialCore D) volume) :
    (fun r => (j : ℝ) * referenceMode u j r)
      =ᵐ[volume.restrict (radialCore D)] (fun r => -referenceSineMode d j r) := by
  have hloc : LocallyIntegrableOn
      (fun r => (j : ℝ) * referenceMode u j r + referenceSineMode d j r)
      (radialCore D) volume := by
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using (hu.smul (j : ℝ)).add hd
  have hzero : ∀ᵐ r ∂volume, r ∈ radialCore D →
      (j : ℝ) * referenceMode u j r + referenceSineMode d j r = 0 := by
    apply (show IsOpen (radialCore D) from isOpen_Ioo).ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc
    intro φ hφ hφc hφs
    have huφ : Integrable (fun r => referenceMode u j r * φ r) :=
      Analysis.integrable_mul_test_of_locallyIntegrableOn_Ioo hu hφ.continuous hφc hφs
    have hdφ : Integrable (fun r => referenceSineMode d j r * φ r) :=
      Analysis.integrable_mul_test_of_locallyIntegrableOn_Ioo hd hφ.continuous hφc hφs
    have heq := r11b_weakAngular_sine_equation hder j hφ hφc hφs
    change (j : ℝ) * (∫ r in D.a..D.b, referenceMode u j r * φ r) =
      -(∫ r in D.a..D.b, referenceSineMode d j r * φ r) at heq
    rw [r11b_intervalIntegral_mul_interior_test hab _ _ hφs,
      r11b_intervalIntegral_mul_interior_test hab _ _ hφs] at heq
    have hpoint : (fun r => φ r • ((j : ℝ) * referenceMode u j r + referenceSineMode d j r)) =
        (fun r => (j : ℝ) * (referenceMode u j r * φ r) + referenceSineMode d j r * φ r) := by
      funext r
      simp only [smul_eq_mul]
      ring
    rw [hpoint, integral_add (huφ.const_mul (j : ℝ)) hdφ,
      integral_const_mul, heq, neg_add_cancel]
  have hz : (fun r => (j : ℝ) * referenceMode u j r + referenceSineMode d j r)
      =ᵐ[volume.restrict (radialCore D)] 0 := by
    change ∀ᵐ r ∂volume.restrict (radialCore D),
      (j : ℝ) * referenceMode u j r + referenceSineMode d j r = 0
    rw [ae_restrict_iff' (show MeasurableSet (radialCore D) from measurableSet_Ioo)]
    exact hzero
  filter_upwards [hz] with r hr
  change (j : ℝ) * referenceMode u j r + referenceSineMode d j r = 0 at hr
  change (j : ℝ) * referenceMode u j r = -referenceSineMode d j r
  linarith

/-- Actual physical L² data discharge all integrability assumptions. No
parity condition is imposed on the angular derivative. -/
theorem r11b_weakAngular_referenceMode_ae
    {D : ReferenceData} (hab : D.a ≤ D.b) {u d : PolarPoint → ℝ}
    (hu : MemLp u 2 (radialPhysicalMeasure D)) (hd : MemLp d 2 (radialPhysicalMeasure D))
    (hder : WeakAngularDerivative D u d) (j : ℕ) (hj : 0 < j) :
    (fun r => (j : ℝ) * referenceMode u j r)
      =ᵐ[volume.restrict (radialCore D)] (fun r => -referenceSineMode d j r) := by
  letI : IsFiniteMeasure (volume.restrict (radialCore D)) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact (measure_mono (show radialCore D ⊆ Icc D.a D.b from Ioo_subset_Icc_self)).trans_lt
      isCompact_Icc.measure_lt_top⟩
  have huL1 : Integrable (referenceMode u j) (volume.restrict (radialCore D)) :=
    MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2) (r11b_referenceMode_L2_bound hu j hj).1
  have hdL1 : Integrable (referenceSineMode d j) (volume.restrict (radialCore D)) :=
    MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2) (r11b_referenceSineMode_L2_bound hd j hj).1
  exact r11b_weakAngular_referenceMode_ae_of_locallyIntegrable hab hder j
    huL1.locallyIntegrableOn hdL1.locallyIntegrableOn

end

end ContinuousFlexibility.Radial
