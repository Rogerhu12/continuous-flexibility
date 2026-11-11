import ContinuousFlexibility.Analysis.OneHighConvolutionCharacter
import ContinuousFlexibility.Analysis.OneHighCylinderFourierInverseL2

/-!
# Actual cylinder multiplication and mixed convolution

The convolution is formed from the genuine mixed Fourier transforms.
Its frequency membership, inverse construction, and pointwise inverse
identity prove physical product membership and the exact Fourier identity.
No physical radial integrability or support assumption is used.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory MeasureTheory.Measure Filter
open scoped ENNReal

local instance : SFinite cylinderFrequencyMeasure :=
  inferInstanceAs (SFinite ((volume : Measure ℝ).prod (Measure.count : Measure ℤ)))

local instance : IsAddLeftInvariant cylinderFrequencyMeasure :=
  inferInstanceAs (IsAddLeftInvariant ((volume : Measure ℝ).prod (Measure.count : Measure ℤ)))

local instance : IsAddRightInvariant cylinderFrequencyMeasure :=
  inferInstanceAs (IsAddRightInvariant ((volume : Measure ℝ).prod (Measure.count : Measure ℤ)))

variable {P : ℝ} [Fact (0 < P)]

theorem cylinderFourier_congr (f g : ℝ × AddCircle P → ℂ)
    (hf : Continuous f) (hg : Continuous g)
    (hf2 : MemLp f 2 (cylinderPhysicalMeasure P))
    (hg2 : MemLp g 2 (cylinderPhysicalMeasure P)) (he : f = g) :
    cylinderFourier f hf hf2 = cylinderFourier g hg hg2 := by
  subst g
  rfl

theorem cylinder_mul_memLp_two (f g : ℝ × AddCircle P → ℂ)
    (hf : Continuous f) (hg : Continuous g)
    (hf2 : MemLp f 2 (cylinderPhysicalMeasure P))
    (hg2 : MemLp g 2 (cylinderPhysicalMeasure P))
    (hF1 : MemLp (cylinderFourier f hf hf2) 1 cylinderFrequencyMeasure)
    (hG1 : MemLp (cylinderFourier g hg hg2) 1 cylinderFrequencyMeasure) :
    MemLp (fun p => f p * g p) 2 (cylinderPhysicalMeasure P) := by
  let F := cylinderFourier f hf hf2
  let G := cylinderFourier g hg hg2
  let H := complexConvolution cylinderFrequencyMeasure F G
  have hHm : Measurable H := measurable_complexConvolution
    (measurable_cylinderFourier f hf hf2) (measurable_cylinderFourier g hg hg2)
  have hH1 : Integrable H cylinderFrequencyMeasure :=
    memLp_one_iff_integrable.mp (complexConvolution_memLp_one hF1 hG1)
  have hH2 : MemLp H 2 cylinderFrequencyMeasure :=
    complexConvolution_memLp_two hF1 (cylinderFourier_memLp_two g hg hg2)
  have he : cylinderFourierInverse (P := P) H = fun p => f p * g p := by
    rw [show H = complexConvolution cylinderFrequencyMeasure F G from rfl,
      cylinderFourierInverse_complexConvolution
        (memLp_one_iff_integrable.mp hF1) (memLp_one_iff_integrable.mp hG1),
      cylinderFourierInverse_fourier f hf hf2 hF1,
      cylinderFourierInverse_fourier g hg hg2 hG1]
  have hm := cylinderFourierInverse_memLp_two (P := P) hHm hH1 hH2
  rwa [he] at hm

/-- Actual pointwise multiplication gives the full mixed complex convolution. -/
theorem cylinderFourier_mul_ae (f g : ℝ × AddCircle P → ℂ)
    (hf : Continuous f) (hg : Continuous g)
    (hf2 : MemLp f 2 (cylinderPhysicalMeasure P))
    (hg2 : MemLp g 2 (cylinderPhysicalMeasure P))
    (hF1 : MemLp (cylinderFourier f hf hf2) 1 cylinderFrequencyMeasure)
    (hG1 : MemLp (cylinderFourier g hg hg2) 1 cylinderFrequencyMeasure) :
    cylinderFourier (fun p => f p * g p) (hf.mul hg)
      (cylinder_mul_memLp_two f g hf hg hf2 hg2 hF1 hG1) =ᵐ[cylinderFrequencyMeasure]
      complexConvolution cylinderFrequencyMeasure
        (cylinderFourier f hf hf2) (cylinderFourier g hg hg2) := by
  let F := cylinderFourier f hf hf2
  let G := cylinderFourier g hg hg2
  let H := complexConvolution cylinderFrequencyMeasure F G
  have hHm : Measurable H := measurable_complexConvolution
    (measurable_cylinderFourier f hf hf2) (measurable_cylinderFourier g hg hg2)
  have hH1 : Integrable H cylinderFrequencyMeasure :=
    memLp_one_iff_integrable.mp (complexConvolution_memLp_one hF1 hG1)
  have hH2 : MemLp H 2 cylinderFrequencyMeasure :=
    complexConvolution_memLp_two hF1 (cylinderFourier_memLp_two g hg hg2)
  have he : cylinderFourierInverse (P := P) H = fun p => f p * g p := by
    rw [show H = complexConvolution cylinderFrequencyMeasure F G from rfl,
      cylinderFourierInverse_complexConvolution
        (memLp_one_iff_integrable.mp hF1) (memLp_one_iff_integrable.mp hG1),
      cylinderFourierInverse_fourier f hf hf2 hF1,
      cylinderFourierInverse_fourier g hg hg2 hG1]
  have hFe := cylinderFourier_congr (cylinderFourierInverse H) (fun p => f p * g p)
    (continuous_cylinderFourierInverse hH1) (hf.mul hg)
    (cylinderFourierInverse_memLp_two hHm hH1 hH2)
    (cylinder_mul_memLp_two f g hf hg hf2 hg2 hF1 hG1) he
  have hFeAE : cylinderFourier (fun p => f p * g p) (hf.mul hg)
      (cylinder_mul_memLp_two f g hf hg hf2 hg2 hF1 hG1) =ᵐ[cylinderFrequencyMeasure]
      cylinderFourier (cylinderFourierInverse H) (continuous_cylinderFourierInverse hH1)
        (cylinderFourierInverse_memLp_two hHm hH1 hH2) :=
    Eventually.of_forall fun ζ => congrFun hFe.symm ζ
  exact hFeAE.trans (cylinderFourier_inverse_ae hHm hH1 hH2)

end ContinuousFlexibility.Analysis
