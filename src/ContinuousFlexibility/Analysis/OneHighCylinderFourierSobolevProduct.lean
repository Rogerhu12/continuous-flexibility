module

public import ContinuousFlexibility.Analysis.OneHighCylinderFourierProducts
public import ContinuousFlexibility.Analysis.OneHighCylinderSobolevWeights
public import ContinuousFlexibility.Analysis.OneHighConvolutionYoung

/-!
# The finite-order physical cylinder Sobolev product estimate

The output Bessel weight is placed on either one of the two factors in
the genuine mixed convolution. Young's inequality gives the complete
two-factor estimate and output Sobolev membership from actual finite
input norms, without derivatives or an all-order regularity hypothesis.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory MeasureTheory.Measure Filter
open scoped ENNReal NNReal MeasureTheory

local instance : SFinite cylinderFrequencyMeasure :=
  inferInstanceAs (SFinite ((volume : Measure ℝ).prod (Measure.count : Measure ℤ)))

local instance : IsAddLeftInvariant cylinderFrequencyMeasure :=
  inferInstanceAs (IsAddLeftInvariant ((volume : Measure ℝ).prod (Measure.count : Measure ℤ)))

local instance : IsAddRightInvariant cylinderFrequencyMeasure :=
  inferInstanceAs (IsAddRightInvariant ((volume : Measure ℝ).prod (Measure.count : Measure ℤ)))

theorem cylinderFrequencyWeight_add_pow_ennreal_le (a q : ℝ) (ζ η : ℝ × ℤ) (s : ℕ) :
    ENNReal.ofReal (cylinderFrequencyWeight a q (ζ + η)) ^ s ≤
      (2 : ℝ≥0∞) ^ s * (ENNReal.ofReal (cylinderFrequencyWeight a q ζ) ^ s +
        ENNReal.ofReal (cylinderFrequencyWeight a q η) ^ s) := by
  have h := ENNReal.ofReal_le_ofReal (cylinderFrequencyWeight_add_pow_le a q ζ η s)
  have htwo : ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) := by norm_num
  simpa only [ENNReal.ofReal_pow (cylinderFrequencyWeight_pos a q (ζ + η)).le,
    ENNReal.ofReal_mul (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) s),
    ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2), htwo,
    ENNReal.ofReal_add (pow_nonneg (cylinderFrequencyWeight_pos a q ζ).le s)
      (pow_nonneg (cylinderFrequencyWeight_pos a q η).le s),
    ENNReal.ofReal_pow (cylinderFrequencyWeight_pos a q ζ).le,
    ENNReal.ofReal_pow (cylinderFrequencyWeight_pos a q η).le] using h

theorem cylinder_enorm_frequencyWeighted_nat (a q : ℝ) (s : ℕ)
    (F : ℝ × ℤ → ℂ) (ζ : ℝ × ℤ) :
    ‖frequencyWeighted (cylinderFrequencyWeight a q) (s : ℝ) F ζ‖ₑ =
      ENNReal.ofReal (cylinderFrequencyWeight a q ζ) ^ s * ‖F ζ‖ₑ := by
  rw [frequencyWeighted_enorm (cylinderFrequencyWeight_pos a q ζ), ENNReal.rpow_natCast]

private theorem cylinder_eLpNorm_weighted_enorm (a q : ℝ) (s : ℕ)
    (F : ℝ × ℤ → ℂ) (hF : Measurable F) :
    eLpNorm (fun ζ => ENNReal.ofReal (cylinderFrequencyWeight a q ζ) ^ s * ‖F ζ‖ₑ)
        2 cylinderFrequencyMeasure =
      eLpNorm (frequencyWeighted (cylinderFrequencyWeight a q) (s : ℝ) F)
        2 cylinderFrequencyMeasure := by
  have he : (fun ζ => ENNReal.ofReal (cylinderFrequencyWeight a q ζ) ^ s * ‖F ζ‖ₑ) =
      fun ζ => ‖frequencyWeighted (cylinderFrequencyWeight a q) (s : ℝ) F ζ‖ₑ :=
    funext (fun ζ => (cylinder_enorm_frequencyWeighted_nat a q s F ζ).symm)
  rw [he]
  exact eLpNorm_enorm _ (frequencyWeighted_aestronglyMeasurable
    (continuous_cylinderFrequencyWeight a q).measurable.aemeasurable hF.aestronglyMeasurable _)

/-- Distribute the actual mixed output weight inside the full convolution. -/
theorem cylinder_enorm_weighted_convolution_le (a q : ℝ) (s : ℕ)
    (F G : ℝ × ℤ → ℂ) (hF : Measurable F) (hG : Measurable G) (ζ : ℝ × ℤ) :
    ‖frequencyWeighted (cylinderFrequencyWeight a q) (s : ℝ)
        (complexConvolution cylinderFrequencyMeasure F G) ζ‖ₑ ≤
      (2 : ℝ≥0∞) ^ s *
        (((fun η => ENNReal.ofReal (cylinderFrequencyWeight a q η) ^ s * ‖F η‖ₑ)
            ⋆ₗ[cylinderFrequencyMeasure] (fun η => ‖G η‖ₑ)) ζ +
          ((fun η => ‖F η‖ₑ) ⋆ₗ[cylinderFrequencyMeasure]
            (fun η => ENNReal.ofReal (cylinderFrequencyWeight a q η) ^ s * ‖G η‖ₑ)) ζ) := by
  let w : ℝ × ℤ → ℝ≥0∞ := fun η => ENNReal.ofReal (cylinderFrequencyWeight a q η) ^ s
  have hw : Measurable w :=
    (continuous_cylinderFrequencyWeight a q).measurable.ennreal_ofReal.pow_const s
  have hshift : Measurable (fun η : ℝ × ℤ => -η + ζ) := measurable_neg.add measurable_const
  have hbase := hF.enorm.mul (hG.enorm.comp hshift)
  have hleft : Measurable (fun η => (w η * ‖F η‖ₑ) * ‖G (-η + ζ)‖ₑ) := by
    simpa only [Pi.mul_def, Function.comp_def] using
      (hw.mul hF.enorm).mul (hG.enorm.comp hshift)
  have hright : Measurable (fun η => ‖F η‖ₑ * (w (-η + ζ) * ‖G (-η + ζ)‖ₑ)) := by
    simpa only [Pi.mul_def, Function.comp_def] using
      hF.enorm.mul ((hw.comp hshift).mul (hG.enorm.comp hshift))
  have hsum : Measurable (fun η => (w η * ‖F η‖ₑ) * ‖G (-η + ζ)‖ₑ +
      ‖F η‖ₑ * (w (-η + ζ) * ‖G (-η + ζ)‖ₑ)) := by
    simpa only [Pi.add_def] using hleft.add hright
  rw [cylinder_enorm_frequencyWeighted_nat]
  apply (mul_le_mul_of_nonneg_left
    (enorm_complexConvolution_le (μ := cylinderFrequencyMeasure) F G ζ) (by positivity)).trans
  rw [lconvolution_def, lconvolution_def, lconvolution_def]
  calc
    w ζ * (∫⁻ η, ‖F η‖ₑ * ‖G (-η + ζ)‖ₑ ∂cylinderFrequencyMeasure) =
        ∫⁻ η, w ζ * (‖F η‖ₑ * ‖G (-η + ζ)‖ₑ) ∂cylinderFrequencyMeasure :=
      (lintegral_const_mul'' _ hbase.aemeasurable).symm
    _ ≤ ∫⁻ η, (2 : ℝ≥0∞) ^ s *
        ((w η * ‖F η‖ₑ) * ‖G (-η + ζ)‖ₑ +
          ‖F η‖ₑ * (w (-η + ζ) * ‖G (-η + ζ)‖ₑ)) ∂cylinderFrequencyMeasure := by
      apply lintegral_mono
      intro η
      have hweight := cylinderFrequencyWeight_add_pow_ennreal_le a q η (-η + ζ) s
      rw [show η + (-η + ζ) = ζ by abel] at hweight
      calc
        _ ≤ ((2 : ℝ≥0∞) ^ s * (w η + w (-η + ζ))) * (‖F η‖ₑ * ‖G (-η + ζ)‖ₑ) :=
          mul_le_mul_of_nonneg_right hweight (by positivity)
        _ = _ := by ring
    _ = _ := by
      rw [lintegral_const_mul'' _ hsum.aemeasurable,
        lintegral_add_left' hleft.aemeasurable]

/-- The genuine weighted mixed convolution satisfies the binary Young
bound, also when some of the norms are infinite. -/
theorem cylinder_eLpNorm_weighted_convolution_le (a q : ℝ) (s : ℕ)
    (F G : ℝ × ℤ → ℂ) (hF : Measurable F) (hG : Measurable G) :
    eLpNorm (frequencyWeighted (cylinderFrequencyWeight a q) (s : ℝ)
        (complexConvolution cylinderFrequencyMeasure F G)) 2 cylinderFrequencyMeasure ≤
      (2 : ℝ≥0∞) ^ s *
        (eLpNorm (frequencyWeighted (cylinderFrequencyWeight a q) (s : ℝ) F)
            2 cylinderFrequencyMeasure * eLpNorm G 1 cylinderFrequencyMeasure +
          eLpNorm F 1 cylinderFrequencyMeasure *
            eLpNorm (frequencyWeighted (cylinderFrequencyWeight a q) (s : ℝ) G)
              2 cylinderFrequencyMeasure) := by
  let A : ℝ × ℤ → ℝ≥0∞ :=
    (fun ζ => ENNReal.ofReal (cylinderFrequencyWeight a q ζ) ^ s * ‖F ζ‖ₑ)
      ⋆ₗ[cylinderFrequencyMeasure] (fun ζ => ‖G ζ‖ₑ)
  let B : ℝ × ℤ → ℝ≥0∞ :=
    (fun ζ => ‖F ζ‖ₑ) ⋆ₗ[cylinderFrequencyMeasure]
      (fun ζ => ENNReal.ofReal (cylinderFrequencyWeight a q ζ) ^ s * ‖G ζ‖ₑ)
  have hw : Measurable (fun ζ => ENNReal.ofReal (cylinderFrequencyWeight a q ζ) ^ s) :=
    (continuous_cylinderFrequencyWeight a q).measurable.ennreal_ofReal.pow_const s
  have hscale : (((2 : ℝ≥0) ^ s : ℝ≥0) : ℝ≥0∞) = (2 : ℝ≥0∞) ^ s := by simp
  have hscaled :
      eLpNorm (frequencyWeighted (cylinderFrequencyWeight a q) (s : ℝ)
          (complexConvolution cylinderFrequencyMeasure F G)) 2 cylinderFrequencyMeasure ≤
        (2 : ℝ≥0∞) ^ s * eLpNorm (A + B) 2 cylinderFrequencyMeasure := by
    have h := eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul'
      (μ := cylinderFrequencyMeasure) (c := (2 : ℝ≥0) ^ s) (g := A + B)
      (f := frequencyWeighted (cylinderFrequencyWeight a q) (s : ℝ)
        (complexConvolution cylinderFrequencyMeasure F G))
      (frequencyWeighted_aestronglyMeasurable
        (continuous_cylinderFrequencyWeight a q).measurable.aemeasurable
        (measurable_complexConvolution hF hG).aestronglyMeasurable _)
      (Eventually.of_forall (fun ζ => by
        simpa only [hscale, Pi.add_apply, enorm_eq_self, A, B] using
          cylinder_enorm_weighted_convolution_le a q s F G hF hG ζ)) 2
    simpa only [ENNReal.smul_def, smul_eq_mul, hscale] using h
  have hA : eLpNorm A 2 cylinderFrequencyMeasure ≤
      eLpNorm (frequencyWeighted (cylinderFrequencyWeight a q) (s : ℝ) F)
        2 cylinderFrequencyMeasure * eLpNorm G 1 cylinderFrequencyMeasure := by
    have h := lconvolution_eLpNorm_two_le' (μ := cylinderFrequencyMeasure)
      (hw.mul hF.enorm).aemeasurable hG.enorm.aemeasurable
    simpa only [Pi.mul_def, Function.comp_def, A, cylinder_eLpNorm_weighted_enorm a q s F hF,
      eLpNorm_enorm G hG.aestronglyMeasurable] using h
  have hB : eLpNorm B 2 cylinderFrequencyMeasure ≤
      eLpNorm F 1 cylinderFrequencyMeasure *
        eLpNorm (frequencyWeighted (cylinderFrequencyWeight a q) (s : ℝ) G)
          2 cylinderFrequencyMeasure := by
    have h := lconvolution_eLpNorm_two_le (μ := cylinderFrequencyMeasure)
      hF.enorm.aemeasurable (hw.mul hG.enorm).aemeasurable
    simpa only [Pi.mul_def, Function.comp_def, B, cylinder_eLpNorm_weighted_enorm a q s G hG,
      eLpNorm_enorm F hF.aestronglyMeasurable] using h
  exact hscaled.trans (mul_le_mul_of_nonneg_left
    ((eLpNorm_add_le (f := A) (g := B) (p := (2 : ℝ≥0∞)) (μ := cylinderFrequencyMeasure)
      (by norm_num)).trans (add_le_add hA hB)) (by positivity))

variable {P : ℝ} [Fact (0 < P)]

/-- Transfer the weighted convolution estimate through the proved actual
Fourier identity of the physical product. -/
theorem cylinder_eLpNorm_weighted_fourier_mul_le (s : ℕ)
    (f g : ℝ × AddCircle P → ℂ) (hf : Continuous f) (hg : Continuous g)
    (hf2 : MemLp f 2 (cylinderPhysicalMeasure P))
    (hg2 : MemLp g 2 (cylinderPhysicalMeasure P))
    (hF1 : MemLp (cylinderFourier f hf hf2) 1 cylinderFrequencyMeasure)
    (hG1 : MemLp (cylinderFourier g hg hg2) 1 cylinderFrequencyMeasure) :
    eLpNorm (frequencyWeighted
        (cylinderFrequencyWeight (2 * Real.pi) (2 * Real.pi / P)) (s : ℝ)
        (cylinderFourier (fun p => f p * g p) (hf.mul hg)
          (cylinder_mul_memLp_two f g hf hg hf2 hg2 hF1 hG1))) 2 cylinderFrequencyMeasure ≤
      (2 : ℝ≥0∞) ^ s *
        (eLpNorm (frequencyWeighted
            (cylinderFrequencyWeight (2 * Real.pi) (2 * Real.pi / P)) (s : ℝ)
            (cylinderFourier f hf hf2)) 2 cylinderFrequencyMeasure *
              eLpNorm (cylinderFourier g hg hg2) 1 cylinderFrequencyMeasure +
          eLpNorm (cylinderFourier f hf hf2) 1 cylinderFrequencyMeasure *
            eLpNorm (frequencyWeighted
              (cylinderFrequencyWeight (2 * Real.pi) (2 * Real.pi / P)) (s : ℝ)
              (cylinderFourier g hg hg2)) 2 cylinderFrequencyMeasure) := by
  have he := cylinderFourier_mul_ae f g hf hg hf2 hg2 hF1 hG1
  have hew : frequencyWeighted
      (cylinderFrequencyWeight (2 * Real.pi) (2 * Real.pi / P)) (s : ℝ)
      (cylinderFourier (fun p => f p * g p) (hf.mul hg)
        (cylinder_mul_memLp_two f g hf hg hf2 hg2 hF1 hG1)) =ᵐ[cylinderFrequencyMeasure]
      frequencyWeighted (cylinderFrequencyWeight (2 * Real.pi) (2 * Real.pi / P)) (s : ℝ)
        (complexConvolution cylinderFrequencyMeasure
          (cylinderFourier f hf hf2) (cylinderFourier g hg hg2)) := by
    filter_upwards [he] with ζ hζ
    simp only [frequencyWeighted_apply, hζ]
  rw [eLpNorm_congr_ae hew]
  exact cylinder_eLpNorm_weighted_convolution_le (2 * Real.pi) (2 * Real.pi / P) s
    (cylinderFourier f hf hf2) (cylinderFourier g hg hg2)
    (measurable_cylinderFourier f hf hf2) (measurable_cylinderFourier g hg hg2)

/-- Actual finite-order output Sobolev membership follows from the two
input Sobolev and Fourier L¹ memberships. -/
theorem cylinder_frequencyWeighted_mul_memLp (s : ℕ)
    (f g : ℝ × AddCircle P → ℂ) (hf : Continuous f) (hg : Continuous g)
    (hf2 : MemLp f 2 (cylinderPhysicalMeasure P))
    (hg2 : MemLp g 2 (cylinderPhysicalMeasure P))
    (hF1 : MemLp (cylinderFourier f hf hf2) 1 cylinderFrequencyMeasure)
    (hG1 : MemLp (cylinderFourier g hg hg2) 1 cylinderFrequencyMeasure)
    (hfs : MemLp (frequencyWeighted
      (cylinderFrequencyWeight (2 * Real.pi) (2 * Real.pi / P)) (s : ℝ)
      (cylinderFourier f hf hf2)) 2 cylinderFrequencyMeasure)
    (hgs : MemLp (frequencyWeighted
      (cylinderFrequencyWeight (2 * Real.pi) (2 * Real.pi / P)) (s : ℝ)
      (cylinderFourier g hg hg2)) 2 cylinderFrequencyMeasure) :
    MemLp (frequencyWeighted
      (cylinderFrequencyWeight (2 * Real.pi) (2 * Real.pi / P)) (s : ℝ)
      (cylinderFourier (fun p => f p * g p) (hf.mul hg)
        (cylinder_mul_memLp_two f g hf hg hf2 hg2 hF1 hG1))) 2 cylinderFrequencyMeasure := by
  apply memLp_iff.mpr
  apply (cylinder_eLpNorm_weighted_fourier_mul_le s f g hf hg hf2 hg2 hF1 hG1).trans_lt
  exact ENNReal.mul_lt_top (by simp)
    (ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top hfs hG1, ENNReal.mul_lt_top hF1 hgs⟩)

/-- The full physical H^s binary product estimate, with one high norm in
each term, from genuine finite-order hypotheses. This includes order zero. -/
theorem cylinder_frequencySobolevNorm_mul_le (s : ℕ)
    (f g : ℝ × AddCircle P → ℂ) (hf : Continuous f) (hg : Continuous g)
    (hf2 : MemLp f 2 (cylinderPhysicalMeasure P))
    (hg2 : MemLp g 2 (cylinderPhysicalMeasure P))
    (hF1 : MemLp (cylinderFourier f hf hf2) 1 cylinderFrequencyMeasure)
    (hG1 : MemLp (cylinderFourier g hg hg2) 1 cylinderFrequencyMeasure)
    (hfs : MemLp (frequencyWeighted
      (cylinderFrequencyWeight (2 * Real.pi) (2 * Real.pi / P)) (s : ℝ)
      (cylinderFourier f hf hf2)) 2 cylinderFrequencyMeasure)
    (hgs : MemLp (frequencyWeighted
      (cylinderFrequencyWeight (2 * Real.pi) (2 * Real.pi / P)) (s : ℝ)
      (cylinderFourier g hg hg2)) 2 cylinderFrequencyMeasure) :
    frequencySobolevNorm cylinderFrequencyMeasure
        (cylinderFrequencyWeight (2 * Real.pi) (2 * Real.pi / P)) (s : ℝ)
        (cylinderFourier (fun p => f p * g p) (hf.mul hg)
          (cylinder_mul_memLp_two f g hf hg hf2 hg2 hF1 hG1)) ≤
      (2 : ℝ) ^ s *
        (frequencySobolevNorm cylinderFrequencyMeasure
          (cylinderFrequencyWeight (2 * Real.pi) (2 * Real.pi / P)) (s : ℝ)
          (cylinderFourier f hf hf2) *
            frequencyL1Norm cylinderFrequencyMeasure (cylinderFourier g hg hg2) +
          frequencyL1Norm cylinderFrequencyMeasure (cylinderFourier f hf hf2) *
            frequencySobolevNorm cylinderFrequencyMeasure
              (cylinderFrequencyWeight (2 * Real.pi) (2 * Real.pi / P)) (s : ℝ)
              (cylinderFourier g hg hg2)) := by
  have hfg := ENNReal.mul_ne_top hfs.ne hG1.ne
  have hgf := ENNReal.mul_ne_top hF1.ne hgs.ne
  have hfinite := ENNReal.mul_ne_top (by simp : (2 : ℝ≥0∞) ^ s ≠ ∞)
    (ENNReal.add_ne_top.mpr ⟨hfg, hgf⟩)
  have h := ENNReal.toReal_mono hfinite
    (cylinder_eLpNorm_weighted_fourier_mul_le s f g hf hg hf2 hg2 hF1 hG1)
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_add hfg hgf,
    ENNReal.toReal_pow, ENNReal.toReal_ofNat, frequencySobolevNorm, frequencyL1Norm] using h

end ContinuousFlexibility.Analysis
