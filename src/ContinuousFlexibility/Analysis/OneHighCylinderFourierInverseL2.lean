import ContinuousFlexibility.Analysis.OneHighCylinderFourierInverseKernel

/-!
# Square integrability of the mixed inverse

For integrable, square-integrable mixed frequency data, the actual inverse
kernel belongs to physical `L²`, with the exact norm. Circle Parseval and
Tonelli give this membership before the physical Fourier transform is used.
The actual mixed Fourier transform of the inverse then recovers the data.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform

theorem real_l2_fourierInv_ae_eq_function {g : ℝ → ℂ}
    (hg1 : Integrable g) (hg2 : MemLp g 2 (volume : Measure ℝ)) :
    ((𝓕⁻ (hg2.toLp g) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) =ᵐ[volume]
      𝓕⁻ g := by
  have hi : Integrable (hg2.toLp g : ℝ → ℂ) := hg1.congr hg2.coeFn_toLp.symm
  exact (real_l2_fourierInv_ae_eq_integral (hg2.toLp g) hi).trans
    (Eventually.of_forall fun x => Real.fourierInv_congr_ae hg2.coeFn_toLp x)

theorem real_fourierInv_memLp_two {g : ℝ → ℂ}
    (hg1 : Integrable g) (hg2 : MemLp g 2 (volume : Measure ℝ)) :
    MemLp (𝓕⁻ g) 2 (volume : Measure ℝ) :=
  (memLp_congr_ae (real_l2_fourierInv_ae_eq_function hg1 hg2)).mp
    (Lp.memLp (𝓕⁻ (hg2.toLp g)))

theorem real_l2_fourier_inverse_eq {g : ℝ → ℂ}
    (hg1 : Integrable g) (hg2 : MemLp g 2 (volume : Measure ℝ))
    (hi2 : MemLp (𝓕⁻ g) 2 (volume : Measure ℝ)) :
    𝓕 (hi2.toLp (𝓕⁻ g)) = hg2.toLp g := by
  have hl : hi2.toLp (𝓕⁻ g) = 𝓕⁻ (hg2.toLp g) := by
    apply Lp.ext
    exact hi2.coeFn_toLp.trans (real_l2_fourierInv_ae_eq_function hg1 hg2).symm
  rw [hl, FourierTransform.fourier_fourierInv_eq]

theorem real_fourierInv_eLpNorm_two {g : ℝ → ℂ}
    (hg1 : Integrable g) (hg2 : MemLp g 2 (volume : Measure ℝ)) :
    eLpNorm (𝓕⁻ g) 2 (volume : Measure ℝ) = eLpNorm g 2 (volume : Measure ℝ) := by
  have hi2 := real_fourierInv_memLp_two hg1 hg2
  apply (ENNReal.toReal_eq_toReal_iff' hi2.ne hg2.ne).mp
  have hn := (Lp.norm_fourier_eq (hi2.toLp (𝓕⁻ g))).symm.trans
    (congrArg norm (real_l2_fourier_inverse_eq hg1 hg2 hi2))
  simpa only [Lp.norm_toLp] using hn

theorem cylinderFrequency_slice_integrable {G : ℝ × ℤ → ℂ}
    (hG1 : Integrable G cylinderFrequencyMeasure) (n : ℤ) :
    Integrable (fun ξ : ℝ => G (ξ, n)) := by
  have hi : Integrable G (volume.prod Measure.count) := hG1
  exact Measure.ae_count_iff.mp hi.prod_left_ae n

theorem cylinderFrequency_slice_memLp_two {G : ℝ × ℤ → ℂ}
    (hG1 : Integrable G cylinderFrequencyMeasure)
    (hG2 : MemLp G 2 cylinderFrequencyMeasure) (n : ℤ) :
    MemLp (fun ξ : ℝ => G (ξ, n)) 2 (volume : Measure ℝ) := by
  have hi : Integrable (fun ζ : ℝ × ℤ => ‖G ζ‖ ^ 2) (volume.prod Measure.count) :=
    hG2.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  exact (memLp_two_iff_integrable_sq_norm
    (cylinderFrequency_slice_integrable hG1 n).aestronglyMeasurable).mpr
      (Measure.ae_count_iff.mp hi.prod_left_ae n)

private theorem eLpNorm_two_sq_inverse {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f : X → ℂ} (hf : AEStronglyMeasurable f μ) :
    eLpNorm f 2 μ ^ 2 = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ := by
  simpa [ENNReal.rpow_two] using
    eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0)) (by norm_num) hf

private theorem eLpNorm_two_sqrt_inverse {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f : X → ℂ} (hf : AEStronglyMeasurable f μ) :
    eLpNorm f 2 μ = (∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ) ^ (1 / (2 : ℝ)) := by
  simpa only [ENNReal.toReal_ofNat, ENNReal.rpow_two] using
    eLpNorm_eq_lintegral_rpow_enorm_toReal (p := (2 : ℝ≥0∞))
      (by norm_num) (by norm_num) hf

variable {P : ℝ} [Fact (0 < P)]

/-- The actual inverse integral preserves the complete squared integral. -/
theorem cylinderFourierInverse_lintegral_sq {G : ℝ × ℤ → ℂ}
    (hG : Measurable G) (hG1 : Integrable G cylinderFrequencyMeasure)
    (hG2 : MemLp G 2 cylinderFrequencyMeasure) :
    (∫⁻ p, ‖cylinderFourierInverse (P := P) G p‖ₑ ^ 2 ∂cylinderPhysicalMeasure P) =
      ∫⁻ ζ, ‖G ζ‖ₑ ^ 2 ∂cylinderFrequencyMeasure := by
  let f : ℝ × AddCircle P → ℂ := cylinderFourierInverse G
  have hf : Continuous f := continuous_cylinderFourierInverse hG1
  let a : ℝ × ℤ → ℂ := fun ζ => 𝓕⁻ (fun ξ : ℝ => G (ξ, ζ.2)) ζ.1
  have ha : Measurable a := measurable_from_prod_countable_left fun n =>
    (real_continuous_fourierInv_of_integrable
      (cylinderFrequency_slice_integrable hG1 n)).measurable
  have hangular (r : ℝ) :
      (∫⁻ θ : AddCircle P, ‖f (r, θ)‖ₑ ^ 2 ∂AddCircle.haarAddCircle) =
        ∫⁻ n : ℤ, ‖a (r, n)‖ₑ ^ 2 ∂Measure.count := by
    let fr : C(AddCircle P, ℂ) :=
      ⟨fun θ => f (r, θ), hf.comp (continuous_const.prodMk continuous_id)⟩
    have hp := (circle_lintegral_sq_fourierCoeff
      (ContinuousMap.memLp (p := 2) (μ := AddCircle.haarAddCircle) ℂ fr)).symm
    refine hp.trans (lintegral_congr fun n => ?_)
    have hn : fourierCoeff fr n = a (r, n) := cylinderAngularCoefficient_inverse hG1 n r
    rw [hn]
  have hmode (n : ℤ) :
      (∫⁻ r : ℝ, ‖a (r, n)‖ₑ ^ 2) = ∫⁻ ξ : ℝ, ‖G (ξ, n)‖ₑ ^ 2 := by
    change (∫⁻ r : ℝ, ‖𝓕⁻ (fun ξ : ℝ => G (ξ, n)) r‖ₑ ^ 2) = _
    have hn1 := cylinderFrequency_slice_integrable hG1 n
    have hn2 := cylinderFrequency_slice_memLp_two hG1 hG2 n
    rw [← eLpNorm_two_sq_inverse (real_continuous_fourierInv_of_integrable hn1).aestronglyMeasurable,
      ← eLpNorm_two_sq_inverse hn1.aestronglyMeasurable,
      real_fourierInv_eLpNorm_two hn1 hn2]
  calc
    _ = ∫⁻ r : ℝ, ∫⁻ θ : AddCircle P, ‖f (r, θ)‖ₑ ^ 2
        ∂AddCircle.haarAddCircle :=
      lintegral_prod _ (hf.measurable.enorm.pow_const (2 : ℕ)).aemeasurable
    _ = ∫⁻ r : ℝ, ∫⁻ n : ℤ, ‖a (r, n)‖ₑ ^ 2 ∂Measure.count :=
      lintegral_congr hangular
    _ = ∫⁻ ζ : ℝ × ℤ, ‖a ζ‖ₑ ^ 2 ∂cylinderFrequencyMeasure :=
      (lintegral_prod _ (ha.enorm.pow_const (2 : ℕ)).aemeasurable).symm
    _ = ∫⁻ n : ℤ, (∫⁻ r : ℝ, ‖a (r, n)‖ₑ ^ 2) ∂Measure.count :=
      lintegral_prod_symm _ (ha.enorm.pow_const (2 : ℕ)).aemeasurable
    _ = ∫⁻ n : ℤ, (∫⁻ ξ : ℝ, ‖G (ξ, n)‖ₑ ^ 2) ∂Measure.count :=
      lintegral_congr hmode
    _ = _ := (lintegral_prod_symm _ (hG.enorm.pow_const (2 : ℕ)).aemeasurable).symm

theorem cylinderFourierInverse_eLpNorm_two {G : ℝ × ℤ → ℂ}
    (hG : Measurable G) (hG1 : Integrable G cylinderFrequencyMeasure)
    (hG2 : MemLp G 2 cylinderFrequencyMeasure) :
    eLpNorm (cylinderFourierInverse (P := P) G) 2 (cylinderPhysicalMeasure P) =
      eLpNorm G 2 cylinderFrequencyMeasure := by
  rw [eLpNorm_two_sqrt_inverse (continuous_cylinderFourierInverse hG1).aestronglyMeasurable,
    eLpNorm_two_sqrt_inverse hG.aestronglyMeasurable,
    cylinderFourierInverse_lintegral_sq hG hG1 hG2]

/-- Physical square integrability is a conclusion of frequency membership. -/
theorem cylinderFourierInverse_memLp_two {G : ℝ × ℤ → ℂ}
    (hG : Measurable G) (hG1 : Integrable G cylinderFrequencyMeasure)
    (hG2 : MemLp G 2 cylinderFrequencyMeasure) :
    MemLp (cylinderFourierInverse (P := P) G) 2 (cylinderPhysicalMeasure P) := by
  rw [memLp_iff, cylinderFourierInverse_eLpNorm_two hG hG1 hG2]
  exact hG2

/-- Taking the actual mixed `L²` transform of the kernel inverse recovers
the prescribed measurable frequency data. -/
theorem cylinderFourier_inverse_ae {G : ℝ × ℤ → ℂ}
    (hG : Measurable G) (hG1 : Integrable G cylinderFrequencyMeasure)
    (hG2 : MemLp G 2 cylinderFrequencyMeasure) :
    cylinderFourier (cylinderFourierInverse (P := P) G)
      (continuous_cylinderFourierInverse hG1)
      (cylinderFourierInverse_memLp_two hG hG1 hG2) =ᵐ[cylinderFrequencyMeasure] G := by
  let f : ℝ × AddCircle P → ℂ := cylinderFourierInverse G
  have hf : Continuous f := continuous_cylinderFourierInverse hG1
  have hf2 : MemLp f 2 (cylinderPhysicalMeasure P) :=
    cylinderFourierInverse_memLp_two hG hG1 hG2
  have hmode (n : ℤ) : (cylinderFourierMode f hf hf2 n : ℝ → ℂ) =ᵐ[volume]
      fun ξ : ℝ => G (ξ, n) := by
    have hn1 := cylinderFrequency_slice_integrable hG1 n
    have hn2 := cylinderFrequency_slice_memLp_two hG1 hG2 n
    have hi2 := real_fourierInv_memLp_two hn1 hn2
    have hcf := cylinderAngularCoefficient_memLp hf hf2 n
    have he : cylinderAngularCoefficient f n =ᵐ[volume]
        𝓕⁻ (fun ξ : ℝ => G (ξ, n)) :=
      Eventually.of_forall fun r => cylinderAngularCoefficient_inverse hG1 n r
    have hl := hcf.toLp_congr hi2 he
    unfold cylinderFourierMode
    rw [hl, real_l2_fourier_inverse_eq hn1 hn2 hi2]
    exact hn2.coeFn_toLp
  apply (Measure.ae_prod_iff_ae_ae
    (measurableSet_eq_fun (measurable_cylinderFourier f hf hf2) hG)).mpr
  have hall : ∀ᵐ ξ : ℝ ∂volume, ∀ n : ℤ,
      cylinderFourierMode f hf hf2 n ξ = G (ξ, n) := ae_all_iff.mpr hmode
  filter_upwards [hall] with ξ hξ
  exact Eventually.of_forall hξ

end ContinuousFlexibility.Analysis
