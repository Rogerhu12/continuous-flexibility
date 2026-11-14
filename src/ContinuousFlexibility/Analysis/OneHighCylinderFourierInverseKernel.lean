module

public import ContinuousFlexibility.Analysis.OneHighCylinderFourierInversion
public import ContinuousFlexibility.Analysis.OneHighCircleFourierSeries

/-!
# The actual inverse kernel on the cylinder

Integrable mixed frequency data define a continuous function on the full
cylinder. Fubini identifies its angular coefficients with the ordinary
inverse real Fourier integrals. In particular this integral reconstructs
every continuous square-integrable function with integrable actual Fourier
transform, without any physical `L¹` or support hypothesis.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory Filter
open scoped ENNReal FourierTransform

variable {P : ℝ} [Fact (0 < P)]

def cylinderInverseCharacter (p : ℝ × AddCircle P) (ζ : ℝ × ℤ) : ℂ :=
  (Real.fourierChar (ζ.1 * p.1) : ℂ) * fourier ζ.2 p.2

@[simp] theorem norm_cylinderInverseCharacter (p : ℝ × AddCircle P) (ζ : ℝ × ℤ) :
    ‖cylinderInverseCharacter p ζ‖ = 1 := by
  have h : ‖fourier ζ.2 p.2‖ = (1 : ℝ) := Circle.norm_coe _
  simp only [cylinderInverseCharacter, norm_mul, Circle.norm_coe, h, one_mul]

theorem measurable_cylinderInverseCharacter (p : ℝ × AddCircle P) :
    Measurable (cylinderInverseCharacter p) := by
  have hr : Continuous (fun ζ : ℝ × ℤ => (Real.fourierChar (ζ.1 * p.1) : ℂ)) :=
    continuous_subtype_val.comp
      (Real.continuous_fourierChar.comp (continuous_fst.mul continuous_const))
  exact hr.measurable.mul ((measurable_of_countable
    (fun n : ℤ => fourier n p.2)).comp measurable_snd)

theorem continuous_cylinderInverseCharacter (ζ : ℝ × ℤ) :
    Continuous (fun p : ℝ × AddCircle P => cylinderInverseCharacter p ζ) := by
  exact (continuous_subtype_val.comp
    (Real.continuous_fourierChar.comp (continuous_const.mul continuous_fst))).mul
      ((fourier ζ.2).continuous.comp continuous_snd)

theorem cylinderInverseCharacter_add (p : ℝ × AddCircle P) (ζ η : ℝ × ℤ) :
    cylinderInverseCharacter p (ζ + η) =
      cylinderInverseCharacter p ζ * cylinderInverseCharacter p η := by
  simp only [cylinderInverseCharacter, Prod.fst_add, Prod.snd_add, add_mul,
    AddChar.map_add_eq_mul, Circle.coe_mul, fourier_add]
  ring

/-- The mixed inverse Fourier integral, with normalized angular Haar
measure and the ordinary real Fourier convention. -/
def cylinderFourierInverse (G : ℝ × ℤ → ℂ) (p : ℝ × AddCircle P) : ℂ :=
  ∫ ζ, cylinderInverseCharacter p ζ * G ζ ∂cylinderFrequencyMeasure

theorem integrable_cylinderInverseCharacter_mul {G : ℝ × ℤ → ℂ}
    (hG : Integrable G cylinderFrequencyMeasure) (p : ℝ × AddCircle P) :
    Integrable (fun ζ => cylinderInverseCharacter p ζ * G ζ) cylinderFrequencyMeasure :=
  hG.mono ((measurable_cylinderInverseCharacter p).aestronglyMeasurable.mul
    hG.aestronglyMeasurable) (Eventually.of_forall fun ζ => by
      simp only [norm_mul, norm_cylinderInverseCharacter, one_mul, le_refl])

theorem continuous_cylinderFourierInverse {G : ℝ × ℤ → ℂ}
    (hG : Integrable G cylinderFrequencyMeasure) :
    Continuous (cylinderFourierInverse (P := P) G) := by
  apply continuous_of_dominated
    (fun p => (integrable_cylinderInverseCharacter_mul hG p).aestronglyMeasurable)
    (fun p => Eventually.of_forall fun ζ => by
      simp only [norm_mul, norm_cylinderInverseCharacter, one_mul, le_refl]) hG.norm
  exact Eventually.of_forall fun ζ =>
    (continuous_cylinderInverseCharacter ζ).mul continuous_const

theorem cylinderFourierInverse_norm_le {G : ℝ × ℤ → ℂ}
    (hG : Integrable G cylinderFrequencyMeasure) (p : ℝ × AddCircle P) :
    ‖cylinderFourierInverse G p‖ ≤ frequencyL1Norm cylinderFrequencyMeasure G := by
  calc
    _ ≤ ∫ ζ, ‖cylinderInverseCharacter p ζ * G ζ‖ ∂cylinderFrequencyMeasure :=
      norm_integral_le_integral_norm _
    _ = ∫ ζ, ‖G ζ‖ ∂cylinderFrequencyMeasure := by
      simp only [norm_mul, norm_cylinderInverseCharacter, one_mul]
    _ = frequencyL1Norm cylinderFrequencyMeasure G := by
      rw [frequencyL1Norm, toReal_eLpNorm,
        lpNorm_one_eq_integral_norm hG.aestronglyMeasurable]

theorem real_fourierInv_eq_integral_character (g : ℝ → ℂ) (r : ℝ) :
    𝓕⁻ g r = ∫ ξ : ℝ, (Real.fourierChar (ξ * r) : ℂ) * g ξ := by
  rw [Real.fourierInv_eq_fourier_neg, Real.fourier_real_eq]
  simp only [mul_neg, neg_neg, Circle.smul_def, smul_eq_mul]

theorem cylinderFourierInverse_eq_integral_modes {G : ℝ × ℤ → ℂ}
    (hG : Integrable G cylinderFrequencyMeasure) (p : ℝ × AddCircle P) :
    cylinderFourierInverse G p =
      ∫ n : ℤ, 𝓕⁻ (fun ξ : ℝ => G (ξ, n)) p.1 * fourier n p.2 ∂Measure.count := by
  change (∫ ζ, cylinderInverseCharacter p ζ * G ζ ∂volume.prod Measure.count) = _
  rw [integral_prod_symm _ (integrable_cylinderInverseCharacter_mul hG p)]
  apply integral_congr_ae
  exact Eventually.of_forall fun n => by
    dsimp only
    rw [real_fourierInv_eq_integral_character, ← integral_mul_const]
    apply integral_congr_ae
    exact Eventually.of_forall fun ξ => by
      dsimp only [cylinderInverseCharacter]
      ring

theorem integrable_cylinderInverse_modes {G : ℝ × ℤ → ℂ}
    (hG : Integrable G cylinderFrequencyMeasure) (r : ℝ) :
    Integrable (fun n : ℤ => 𝓕⁻ (fun ξ : ℝ => G (ξ, n)) r) Measure.count := by
  have hi : Integrable G (volume.prod Measure.count) := hG
  apply hi.integral_norm_prod_right.mono' (measurable_of_countable _).aestronglyMeasurable
  exact Eventually.of_forall fun n => by
    rw [real_fourierInv_eq_integral_character]
    exact (norm_integral_le_integral_norm _).trans_eq (by
      simp only [norm_mul, Circle.norm_coe, one_mul])

theorem cylinderFourierInverse_eq_series {G : ℝ × ℤ → ℂ}
    (hG : Integrable G cylinderFrequencyMeasure) (r : ℝ) (θ : AddCircle P) :
    cylinderFourierInverse G (r, θ) =
      circleFourierSeries (P := P) (fun n : ℤ => 𝓕⁻ (fun ξ : ℝ => G (ξ, n)) r) θ := by
  let a : ℤ → ℂ := fun n => 𝓕⁻ (fun ξ : ℝ => G (ξ, n)) r
  have ha : Integrable a Measure.count := integrable_cylinderInverse_modes hG r
  have hs : Summable (fun n => ‖a n‖) := integrable_count_iff.mp ha
  have hp : Integrable (fun n => a n * fourier n θ) Measure.count :=
    ha.mono (measurable_of_countable _).aestronglyMeasurable
      (Eventually.of_forall fun n => by
        have hn : ‖fourier n θ‖ = (1 : ℝ) := Circle.norm_coe _
        simp only [norm_mul, hn, mul_one, le_refl])
  have hi : (∫ n : ℤ, a n * fourier n θ ∂Measure.count) =
      ∑' n : ℤ, a n * fourier n θ := by
    simpa only [measureReal_def, Measure.count_singleton, ENNReal.toReal_one, one_smul] using
      integral_countable hp
  rw [cylinderFourierInverse_eq_integral_modes hG]
  exact hi.trans (circleFourierSeries_hasSum_apply hs θ).tsum_eq

/-- Prescribing arbitrary integrable mixed frequency data prescribes
the actual angular coefficients of the continuous inverse integral. -/
theorem cylinderAngularCoefficient_inverse {G : ℝ × ℤ → ℂ}
    (hG : Integrable G cylinderFrequencyMeasure) (n : ℤ) (r : ℝ) :
    cylinderAngularCoefficient (cylinderFourierInverse (P := P) G) n r =
      𝓕⁻ (fun ξ : ℝ => G (ξ, n)) r := by
  have he : (fun θ : AddCircle P => cylinderFourierInverse G (r, θ)) =
      (circleFourierSeries (P := P)
        (fun n : ℤ => 𝓕⁻ (fun ξ : ℝ => G (ξ, n)) r) : AddCircle P → ℂ) :=
    funext (cylinderFourierInverse_eq_series hG r)
  change fourierCoeff (fun θ : AddCircle P => cylinderFourierInverse G (r, θ)) n = _
  rw [he]
  exact circle_fourierCoeff_series
    (integrable_count_iff.mp (integrable_cylinderInverse_modes hG r)) n

/-- The kernel inverse reconstructs the original continuous cylinder
function from its actual `L²` Fourier transform whenever that transform
is integrable. -/
theorem cylinderFourierInverse_fourier (f : ℝ × AddCircle P → ℂ) (hf : Continuous f)
    (hL2 : MemLp f 2 (cylinderPhysicalMeasure P))
    (hF1 : MemLp (cylinderFourier f hf hL2) 1 cylinderFrequencyMeasure) :
    cylinderFourierInverse (cylinderFourier f hf hL2) = f := by
  funext p
  have hi := memLp_one_iff_integrable.mp hF1
  rw [cylinderFourierInverse_eq_series hi]
  have hs := circleFourierSeries_hasSum_apply
    (integrable_count_iff.mp (integrable_cylinderInverse_modes hi p.1)) p.2
  exact hs.unique (by
    simpa only [smul_eq_mul, cylinderFourier] using
      cylinder_hasSum_inverse_modes f hf hL2 hF1 p.1 p.2)

end ContinuousFlexibility.Analysis
