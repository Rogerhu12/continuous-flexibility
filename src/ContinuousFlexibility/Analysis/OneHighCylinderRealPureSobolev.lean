module

public import ContinuousFlexibility.Analysis.OneHighCylinderPureSobolev
public import ContinuousFlexibility.Analysis.OneHighCylinderRealSobolev
public import ContinuousFlexibility.Analysis.OneHighCylinderPureJets

/-!
# Physical Sobolev control by the actual pure derivatives of a real function

The weighted Fourier membership is obtained as a conclusion. The hypotheses
ask only for finite energy of the genuine radial and angular derivatives
through the required finite order.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory
open scoped ENNReal ContDiff

variable {P : ℝ} [Fact (0 < P)]

theorem cylinder_real_sobolev_of_pure_derivatives
    (s : ℕ) (f : ℝ × AddCircle P → ℝ) (hf : Continuous f)
    (hf2 : MemLp f 2 (cylinderPhysicalMeasure P))
    (r a : ℕ → (ℝ × AddCircle P) → ℝ)
    (hr : ∀ k, Continuous (r k)) (ha : ∀ k, Continuous (a k))
    (hr0 : r 0 = f) (ha0 : a 0 = f)
    (hdr : ∀ k (θ : AddCircle P) (x : ℝ),
      HasDerivAt (fun y : ℝ => r k (y, θ)) (r (k + 1) (x, θ)) x)
    (hda : ∀ k (x y : ℝ),
      HasDerivAt (fun z : ℝ => a k (x, (z : AddCircle P)))
        (a (k + 1) (x, (y : AddCircle P))) y)
    (hr2 : ∀ k, k ≤ s → MemLp (r k) 2 (cylinderPhysicalMeasure P))
    (ha2 : ∀ k, k ≤ s → MemLp (a k) 2 (cylinderPhysicalMeasure P)) :
    MemLp (frequencyWeighted
      (cylinderFrequencyWeight (2 * Real.pi) (2 * Real.pi / P)) (s : ℝ)
      (cylinderFourier (cylinderComplexify f) (continuous_cylinderComplexify hf)
        (cylinderComplexify_memLp hf hf2))) 2 cylinderFrequencyMeasure ∧
    cylinderRealSobolevNorm s f hf hf2 ≤ (3 : ℝ) ^ s *
      ((eLpNorm f 2 (cylinderPhysicalMeasure P)).toReal +
        (eLpNorm (r s) 2 (cylinderPhysicalMeasure P)).toReal +
          (eLpNorm (a s) 2 (cylinderPhysicalMeasure P)).toReal) := by
  have hr0c : cylinderComplexify (r 0) = cylinderComplexify f :=
    congrArg cylinderComplexify hr0
  have ha0c : cylinderComplexify (a 0) = cylinderComplexify f :=
    congrArg cylinderComplexify ha0
  have h := cylinder_sobolev_of_pure_derivatives s
    (cylinderComplexify f) (continuous_cylinderComplexify hf)
    (cylinderComplexify_memLp hf hf2)
    (fun k => cylinderComplexify (r k)) (fun k => cylinderComplexify (a k))
    (fun k => continuous_cylinderComplexify (hr k))
    (fun k => continuous_cylinderComplexify (ha k)) hr0c ha0c
    (fun k θ x => (hdr k θ x).ofReal_comp)
    (fun k x y => (hda k x y).ofReal_comp)
    (fun k hk => cylinderComplexify_memLp (hr k) (hr2 k hk))
    (fun k hk => cylinderComplexify_memLp (ha k) (ha2 k hk))
  refine ⟨h.1, ?_⟩
  have hb := h.2
  rw [cylinder_eLpNorm_complexify f hf 2,
    cylinder_eLpNorm_complexify (r s) (hr s) 2,
    cylinder_eLpNorm_complexify (a s) (ha s) 2] at hb
  exact hb

end ContinuousFlexibility.Analysis
