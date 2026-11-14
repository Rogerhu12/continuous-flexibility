module

public import ContinuousFlexibility.Radial.ReferenceGraphCoefficients
public import ContinuousFlexibility.Radial.ReferenceColumnSmooth
public import ContinuousFlexibility.Analysis.IntervalWeakODE

/-!
# Smooth interior representatives of actual reference coefficients

The weak Jacobi equation is converted into a genuine scalar divergence
equation. Two integral primitives and ordinary ODE regularity produce a
smooth representative, and distributional uniqueness identifies its
ordinary derivative with the projected first-normal derivative.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace ContinuousFlexibility.Radial

open ContinuousFlexibility.Statements
open ContinuousFlexibility.Analysis

noncomputable section

theorem reference_memLp_radial_of_continuous (D : ReferenceData) {f : ℝ → ℝ}
    (hf : Continuous f) : MemLp f 2 (volume.restrict (radialCore D)) := by
  letI : IsFiniteMeasure (volume.restrict (radialCore D)) := by
    dsimp only [radialCore]
    infer_instance
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image
    (hf.norm.continuousOn (s := Icc D.a D.b))
  apply MemLp.of_bound hf.aestronglyMeasurable C
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
  exact hC ⟨r, Ioo_subset_Icc_self hr, rfl⟩

theorem reference_intervalIntegral_eq_integral {D : ReferenceData} {f : ℝ → ℝ}
    (hs : Function.support f ⊆ radialCore D) :
    (∫ r in D.a..D.b, f r) = ∫ r, f r := by
  apply intervalIntegral.integral_eq_integral_of_support_subset
  intro r hr
  exact ⟨(hs hr).1, (hs hr).2.le⟩

theorem reference_integral_mul_test_congr_ae {D : ReferenceData} {u v φ : ℝ → ℝ}
    (he : u =ᵐ[volume.restrict (radialCore D)] v)
    (hφs : tsupport φ ⊆ radialCore D) :
    (∫ r, u r * φ r) = ∫ r, v r * φ r := by
  have heq (z : ℝ → ℝ) :
      (∫ r in radialCore D, z r * φ r) = ∫ r, z r * φ r := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro r hr
    rw [image_eq_zero_of_notMem_tsupport (fun h => hr (hφs h)), mul_zero]
  rw [← heq u, ← heq v]
  exact integral_congr_ae (he.mono fun r hr => congrArg (fun z : ℝ => z * φ r) hr)

/-- Interior regularity for the genuine Jacobi expression with a smooth
forcing and an actual ordinary radial L² weak solution. -/
theorem reference_exists_smooth_of_weakJacobi {D : ReferenceData}
    (hgeom : RadialProfileGeometry D) {u f : ℝ → ℝ} (J : ℝ)
    (hu : MemLp u 2 (volume.restrict (radialCore D))) (hf : ContDiff ℝ ∞ f)
    (hweak : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ radialCore D →
        (∫ r in D.a..D.b, u r * radialJacobi J D.w φ r) =
          ∫ r in D.a..D.b, f r * φ r) :
    ∃ v : ℝ → ℝ, ContDiffOn ℝ ∞ v (radialCore D) ∧
      u =ᵐ[volume.restrict (radialCore D)] v ∧
      ∀ r ∈ radialCore D, radialJacobi J D.w v r = f r := by
  letI : IsFiniteMeasure (volume.restrict (radialCore D)) := by
    dsimp only [radialCore]
    infer_instance
  let q : ℝ → ℝ := fun r => J * deriv D.w r / r
  have hq : ContDiff ℝ ∞ q := by
    dsimp only [q]
    simp_rw [mul_div_assoc]
    exact contDiff_const.mul (reference_contDiff_flat_deriv_div hgeom.1 hgeom.2.2.1)
  have huI : IntegrableOn u (radialCore D) :=
    hu.integrable (by norm_num)
  have hquI : IntegrableOn (fun r => q r * u r) (radialCore D) :=
    (reference_memLp_radial_of_continuous D hq.continuous).integrable_mul hu
  have hfI : IntegrableOn f (radialCore D) :=
    (reference_memLp_radial_of_continuous D hf.continuous).integrable (by norm_num)
  have hdiv : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ radialCore D →
        (∫ r, u r * deriv (fun t => D.w t * deriv φ t) r) =
          ∫ r, (f r + q r * u r) * φ r := by
    intro φ hφ hφc hφs
    have hφd : ContDiff ℝ ∞ (deriv φ) := (contDiff_infty_iff_deriv.mp hφ).2
    let dφ : ℝ → ℝ := deriv (fun t => D.w t * deriv φ t)
    have hds : tsupport dφ ⊆ tsupport φ :=
      tsupport_deriv_subset.trans (tsupport_mul_subset_right.trans tsupport_deriv_subset)
    have hdφ : ContDiff ℝ ∞ dφ :=
      (contDiff_infty_iff_deriv.mp (hgeom.2.2.1.1.mul hφd)).2
    have hdc : HasCompactSupport dφ := (hφc.deriv.mul_left).deriv
    have hdI : Integrable (fun r => u r * dφ r) :=
      integrable_mul_test_of_locallyIntegrableOn_Ioo huI.locallyIntegrableOn
        hdφ.continuous hdc (hds.trans hφs)
    have hqI : Integrable (fun r => (q r * u r) * φ r) :=
      integrable_mul_test_of_locallyIntegrableOn_Ioo hquI.locallyIntegrableOn
        hφ.continuous hφc hφs
    have hfφI : Integrable (fun r => f r * φ r) :=
      integrable_mul_test_of_locallyIntegrableOn_Ioo hfI.locallyIntegrableOn
        hφ.continuous hφc hφs
    have hJs : Function.support (fun r => u r * radialJacobi J D.w φ r) ⊆ radialCore D := by
      intro r hr
      by_contra hrI
      have hzφ : φ r = 0 := image_eq_zero_of_notMem_tsupport (fun h => hrI (hφs h))
      have hzd : dφ r = 0 := image_eq_zero_of_notMem_tsupport
        (fun h => hrI (hφs (hds h)))
      apply hr
      change u r * (dφ r - q r * φ r) = 0
      rw [hzφ, hzd, mul_zero, sub_zero, mul_zero]
    have hfs : Function.support (fun r => f r * φ r) ⊆ radialCore D :=
      (Function.support_mul_subset_right f φ).trans ((subset_tsupport φ).trans hφs)
    have h := hweak φ hφ hφc hφs
    rw [reference_intervalIntegral_eq_integral hJs,
      reference_intervalIntegral_eq_integral hfs] at h
    have he : (fun r => u r * radialJacobi J D.w φ r) =
        (fun r => u r * dφ r - (q r * u r) * φ r) := by
      funext r
      dsimp only [radialJacobi, dφ, q]
      ring
    rw [he, integral_sub hdI hqI] at h
    simp_rw [add_mul]
    rw [integral_add hfφI hqI]
    linarith
  obtain ⟨v, hv, huv, heq⟩ :=
    exists_contDiffOn_ae_eq_of_weak_divergence_Ioo hgeom.2.1 hgeom.2.2.1.1
      (fun r hr => (hgeom.2.2.2.2.1 r hr).ne') hq.contDiffOn hf.contDiffOn
      huI.locallyIntegrableOn (hfI.add hquI) hdiv
  refine ⟨v, hv, huv, fun r hr => ?_⟩
  unfold radialJacobi
  rw [heq r hr]
  dsimp only [q]
  ring

def referenceCoefficientForcing (D : ReferenceData) (U : RadialUnknown)
    (F : RadialSource) (n : ℕ) (r : ℝ) : ℝ :=
  referenceRadialCoefficient F.1 n r - if n = 1 then U.2 * referenceColumn D r else 0

theorem referenceCoefficientForcing_contDiff {D : ReferenceData}
    (hgeom : RadialProfileGeometry D) (hborder : RadialTrueBorder D)
    {U : RadialUnknown} {F : RadialSource} (hF : ContDiff ℝ ∞ F.1) (n : ℕ) :
    ContDiff ℝ ∞ (referenceCoefficientForcing D U F n) := by
  unfold referenceCoefficientForcing
  by_cases hn : n = 1
  · simp only [if_pos hn]
    exact (contDiff_referenceRadialCoefficient hF n).sub
      (contDiff_const.mul (referenceColumn_contDiff hgeom hborder))
  · simpa only [if_neg hn, sub_zero] using
      contDiff_referenceRadialCoefficient hF n

/-- Every angular coefficient of a graph with a smooth source has a
genuine smooth interior representative satisfying its original equation. -/
theorem referenceGraph_exists_smooth_coefficient {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    {γ M₀ M₁ : ℝ} (hγ : 0 < γ) {U : RadialUnknown} {F : RadialSource}
    (hgraph : ReferenceGraph D γ M₀ M₁ U F) (hF : ContDiff ℝ ∞ F.1) (n : ℕ) :
    ∃ v : ℝ → ℝ, ContDiffOn ℝ ∞ v (radialCore D) ∧
      referenceRadialCoefficient U.1 n =ᵐ[volume.restrict (radialCore D)] v ∧
      ∀ r ∈ radialCore D,
        radialJacobi (((2 * n : ℕ) : ℝ) ^ 2) D.w v r = referenceCoefficientForcing D U F n r := by
  have hgeom : RadialProfileGeometry D := hD.choose_spec.1
  have huP : MemLp U.1 2 ((volume.restrict (radialCore D)).prod
      (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))) := by
    simpa only [radialPhysicalMeasure_eq_prod] using
      r11b_output_memLp hD hborder hγ hgraph.1
  apply reference_exists_smooth_of_weakJacobi hgeom _
    (memLp_referenceRadialCoefficient_prod huP n)
    (referenceCoefficientForcing_contDiff hgeom hborder hF n)
  intro φ hφ hφc hφs
  have h := referenceGraph_coefficient_equation hgeom hgraph n hφ hφc hφs
  have hfI : IntervalIntegrable
      (fun r => referenceRadialCoefficient F.1 n r * φ r) volume D.a D.b :=
    ((contDiff_referenceRadialCoefficient hF n).continuous.mul
      hφ.continuous).intervalIntegrable D.a D.b
  have hcI : IntervalIntegrable
      (fun r => referenceColumn D r * φ r) volume D.a D.b :=
    ((referenceColumn_contDiff hgeom hborder).continuous.mul
      hφ.continuous).intervalIntegrable D.a D.b
  have he :
      (∫ r in D.a..D.b, referenceCoefficientForcing D U F n r * φ r) =
        (∫ r in D.a..D.b, referenceRadialCoefficient F.1 n r * φ r) -
          U.2 * (if n = 1 then ∫ r in D.a..D.b, referenceColumn D r * φ r else 0) := by
    by_cases hn : n = 1
    · simp only [referenceCoefficientForcing, if_pos hn, sub_mul, mul_assoc]
      rw [intervalIntegral.integral_sub hfI (hcI.const_mul U.2),
        intervalIntegral.integral_const_mul]
    · simp only [referenceCoefficientForcing, if_neg hn, sub_zero, mul_zero]
  rw [he]
  linarith

/-- Identification of the ordinary derivative of a smooth representative.
The proof is distributional uniqueness, not a choice of derivative values. -/
theorem reference_coefficient_normal_eq_deriv {D : ReferenceData}
    (hab : D.a < D.b) {u d : PolarPoint → ℝ} (hd : WeakNormalDerivative D u d)
    (n : ℕ) {v : ℝ → ℝ}
    (hv : ContDiffOn ℝ ∞ v (radialCore D))
    (huv : referenceRadialCoefficient u n =ᵐ[volume.restrict (radialCore D)] v)
    (hdI : LocallyIntegrableOn (referenceRadialCoefficient d n) (radialCore D) volume) :
    referenceRadialCoefficient d n =ᵐ[volume.restrict (radialCore D)] deriv v := by
  have hv' : ContDiffOn ℝ ∞ (deriv v) (radialCore D) :=
    hv.deriv_of_isOpen isOpen_Ioo (by simp)
  have hv'I : LocallyIntegrableOn (deriv v) (radialCore D) volume :=
    hv'.continuousOn.locallyIntegrableOn measurableSet_Ioo
  have hzero : ∀ᵐ r ∂volume, r ∈ radialCore D →
      referenceRadialCoefficient d n r - deriv v r = 0 := by
    apply isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hdI.sub hv'I)
    intro φ hφ hφc hφs
    have hdφ := integrable_mul_test_of_locallyIntegrableOn_Ioo hdI hφ.continuous hφc hφs
    have hvφ := integrable_mul_test_of_locallyIntegrableOn_Ioo hv'I hφ.continuous hφc hφs
    have h := weakNormalDerivative_coefficient hd n hφ hφc hφs
    have hleftS : Function.support
        (fun r => referenceRadialCoefficient u n r * deriv φ r) ⊆ radialCore D :=
      (Function.support_mul_subset_right (referenceRadialCoefficient u n) (deriv φ)).trans
        ((subset_tsupport (deriv φ)).trans (tsupport_deriv_subset.trans hφs))
    have hrightS : Function.support
        (fun r => referenceRadialCoefficient d n r * φ r) ⊆ radialCore D :=
      (Function.support_mul_subset_right (referenceRadialCoefficient d n) φ).trans
        ((subset_tsupport φ).trans hφs)
    rw [reference_intervalIntegral_eq_integral hleftS,
      reference_intervalIntegral_eq_integral hrightS,
      reference_integral_mul_test_congr_ae huv (tsupport_deriv_subset.trans hφs)] at h
    have hIBP := integral_mul_deriv_eq_neg_of_hasDerivAt_Ioo hab
      (fun r hr => ((hv.contDiffAt (isOpen_Ioo.mem_nhds hr)).differentiableAt (by simp)).hasDerivAt)
      hv'.continuousOn hφ hφc hφs
    have he : (∫ r, referenceRadialCoefficient d n r * φ r) =
        ∫ r, deriv v r * φ r := by linarith
    have hfun : (fun r => φ r • (referenceRadialCoefficient d n r - deriv v r)) =
        (fun r => referenceRadialCoefficient d n r * φ r - deriv v r * φ r) := by
      funext r
      simp only [smul_eq_mul]
      ring
    simp only [Pi.sub_apply]
    rw [hfun, integral_sub hdφ hvφ, he, sub_self]
  filter_upwards [ae_restrict_of_ae hzero,
    ae_restrict_mem (s := radialCore D) measurableSet_Ioo] with r hr hrI
  exact sub_eq_zero.mp (hr hrI)

end

end ContinuousFlexibility.Radial
