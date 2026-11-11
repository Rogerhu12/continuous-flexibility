import ContinuousFlexibility.Analysis.OneHighCylinderSmoothJets

/-!
# Real functions in the physical cylinder Fourier representation

Real cylinder functions use their canonical complex inclusion in the existing
mixed Fourier transform. Their Sobolev and Fourier L¹ norms below are only
abbreviations for those same physical norms.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory Filter
open scoped ENNReal

variable {P : ℝ} [Fact (0 < P)]

def cylinderComplexify (f : ℝ × AddCircle P → ℝ) (p : ℝ × AddCircle P) : ℂ :=
  (f p : ℂ)

@[simp] theorem cylinderComplexify_apply (f : ℝ × AddCircle P → ℝ)
    (p : ℝ × AddCircle P) : cylinderComplexify f p = (f p : ℂ) := rfl

theorem continuous_cylinderComplexify {f : ℝ × AddCircle P → ℝ} (hf : Continuous f) :
    Continuous (cylinderComplexify f) :=
  Complex.continuous_ofReal.comp hf

theorem cylinder_eLpNorm_complexify (f : ℝ × AddCircle P → ℝ)
    (hf : Continuous f) (p : ℝ≥0∞) :
    eLpNorm (cylinderComplexify f) p (cylinderPhysicalMeasure P) =
      eLpNorm f p (cylinderPhysicalMeasure P) := by
  apply eLpNorm_congr_norm_ae (continuous_cylinderComplexify hf).aestronglyMeasurable
    hf.aestronglyMeasurable
  exact Eventually.of_forall fun x => by simp

theorem cylinderComplexify_memLp {f : ℝ × AddCircle P → ℝ}
    (hf : Continuous f) {p : ℝ≥0∞} (hfp : MemLp f p (cylinderPhysicalMeasure P)) :
    MemLp (cylinderComplexify f) p (cylinderPhysicalMeasure P) := by
  rw [memLp_iff, cylinder_eLpNorm_complexify f hf p]
  exact hfp

abbrev cylinderRealSobolevNorm (s : ℝ) (f : ℝ × AddCircle P → ℝ)
    (hf : Continuous f) (hf2 : MemLp f 2 (cylinderPhysicalMeasure P)) : ℝ :=
  cylinderSobolevNorm s (cylinderComplexify f) (continuous_cylinderComplexify hf)
    (cylinderComplexify_memLp hf hf2)

abbrev cylinderRealFourierL1Norm (f : ℝ × AddCircle P → ℝ)
    (hf : Continuous f) (hf2 : MemLp f 2 (cylinderPhysicalMeasure P)) : ℝ :=
  frequencyL1Norm cylinderFrequencyMeasure
    (cylinderFourier (cylinderComplexify f) (continuous_cylinderComplexify hf)
      (cylinderComplexify_memLp hf hf2))

theorem cylinder_real_sobolevNorm_zero_eq_l2 (f : ℝ × AddCircle P → ℝ)
    (hf : Continuous f) (hf2 : MemLp f 2 (cylinderPhysicalMeasure P)) :
    cylinderRealSobolevNorm 0 f hf hf2 =
      (eLpNorm f 2 (cylinderPhysicalMeasure P)).toReal := by
  have h := cylinder_frequencySobolevNorm_zero_eq_l2 (cylinderComplexify f)
    (continuous_cylinderComplexify hf) (cylinderComplexify_memLp hf hf2)
  rw [cylinder_eLpNorm_complexify f hf 2] at h
  exact h

/-- Finite Sobolev membership of a real jet in the same actual Fourier
representation used for complex functions. -/
def CylinderSmoothJet.MemRealSobolev (u : CylinderSmoothJet P ℝ) (s : ℕ)
    (hu2 : MemLp (u.jet 0 0) 2 (cylinderPhysicalMeasure P)) : Prop :=
  u.complexify.MemSobolev s (cylinderComplexify_memLp (u.continuous 0 0) hu2)

end ContinuousFlexibility.Analysis
