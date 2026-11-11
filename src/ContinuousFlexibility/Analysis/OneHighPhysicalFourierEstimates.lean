import ContinuousFlexibility.Analysis.OneHighCircleSobolevJetsBasic
import ContinuousFlexibility.Analysis.OneHighCylinderSobolevJetsBasic
import ContinuousFlexibility.Analysis.OneHighCylinderFourierInversion
import ContinuousFlexibility.Analysis.OneHighInterpolation

/-!
# Physical circle and cylinder interpolation

These specializations use the Fourier transform of each actual input, the
physical frequencies `2*pi/P` and `2*pi`, and normalized angular Haar measure.
The segment estimate permits arbitrary real orders and includes both
endpoints. The endpoint memberships ensure that every real norm is finite.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory Set Filter
open scoped ENNReal

variable {P : ℝ} [Fact (0 < P)]

/-- Lemma 7.2(i) for the actual Fourier coefficients of circle functions. -/
theorem circle_sobolev_segment_product_le
    (f g : C(AddCircle P, ℂ)) {k l m n i j : ℝ}
    (hfk : MemLp (frequencyWeighted (circleFrequencyWeight P) k (fourierCoeff f))
      2 Measure.count)
    (hfm : MemLp (frequencyWeighted (circleFrequencyWeight P) m (fourierCoeff f))
      2 Measure.count)
    (hgl : MemLp (frequencyWeighted (circleFrequencyWeight P) l (fourierCoeff g))
      2 Measure.count)
    (hgn : MemLp (frequencyWeighted (circleFrequencyWeight P) n (fourierCoeff g))
      2 Measure.count)
    (hseg : (i, j) ∈ segment ℝ (k, l) (m, n)) :
    circleSobolevNorm i f * circleSobolevNorm j g ≤
      circleSobolevNorm k f * circleSobolevNorm l g +
        circleSobolevNorm m f * circleSobolevNorm n g :=
  frequencySobolevNorm_product_le_of_mem_segment
    (measurable_of_countable _).aemeasurable
    (Eventually.of_forall (circleFrequencyWeight_pos P)) hfk hfm hgl hgn hseg

/-- Lemma 7.2(i) for the actual mixed Fourier transforms of cylinder inputs. -/
theorem cylinder_sobolev_segment_product_le
    (f g : ℝ × AddCircle P → ℂ) (hf : Continuous f) (hg : Continuous g)
    (hf2 : MemLp f 2 (cylinderPhysicalMeasure P))
    (hg2 : MemLp g 2 (cylinderPhysicalMeasure P)) {k l m n i j : ℝ}
    (hfk : MemLp (frequencyWeighted
      (cylinderFrequencyWeight (2 * Real.pi) (2 * Real.pi / P)) k
      (cylinderFourier f hf hf2)) 2 cylinderFrequencyMeasure)
    (hfm : MemLp (frequencyWeighted
      (cylinderFrequencyWeight (2 * Real.pi) (2 * Real.pi / P)) m
      (cylinderFourier f hf hf2)) 2 cylinderFrequencyMeasure)
    (hgl : MemLp (frequencyWeighted
      (cylinderFrequencyWeight (2 * Real.pi) (2 * Real.pi / P)) l
      (cylinderFourier g hg hg2)) 2 cylinderFrequencyMeasure)
    (hgn : MemLp (frequencyWeighted
      (cylinderFrequencyWeight (2 * Real.pi) (2 * Real.pi / P)) n
      (cylinderFourier g hg hg2)) 2 cylinderFrequencyMeasure)
    (hseg : (i, j) ∈ segment ℝ (k, l) (m, n)) :
    cylinderSobolevNorm i f hf hf2 * cylinderSobolevNorm j g hg hg2 ≤
      cylinderSobolevNorm k f hf hf2 * cylinderSobolevNorm l g hg hg2 +
        cylinderSobolevNorm m f hf hf2 * cylinderSobolevNorm n g hg hg2 :=
  frequencySobolevNorm_product_le_of_mem_segment
    (continuous_cylinderFrequencyWeight _ _).measurable.aemeasurable
    (Eventually.of_forall (cylinderFrequencyWeight_pos _ _)) hfk hfm hgl hgn hseg

/-- The cylinder Fourier norm of an actual input is controlled by its
physical order-two Sobolev norm, with a constant depending only on the period. -/
theorem cylinder_fourierL1Norm_le_sobolev_two
    (f : ℝ × AddCircle P → ℂ) (hf : Continuous f)
    (hf2 : MemLp f 2 (cylinderPhysicalMeasure P))
    (hH2 : MemLp (frequencyWeighted
      (cylinderFrequencyWeight (2 * Real.pi) (2 * Real.pi / P)) 2
      (cylinderFourier f hf hf2)) 2 cylinderFrequencyMeasure) :
    frequencyL1Norm cylinderFrequencyMeasure (cylinderFourier f hf hf2) ≤
      (eLpNorm (fun ζ =>
        cylinderFrequencyWeight (2 * Real.pi) (2 * Real.pi / P) ζ ^ (-2 : ℝ))
        2 cylinderFrequencyMeasure).toReal * cylinderSobolevNorm 2 f hf hf2 :=
  cylinder_frequencyL1Norm_le_h2 (mul_pos (by norm_num) Real.pi_pos)
    (circlePhysicalFrequencyScale_pos P) hH2

end ContinuousFlexibility.Analysis
