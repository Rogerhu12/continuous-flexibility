import ContinuousFlexibility.Analysis.OneHighCylinderFourierAngular
import ContinuousFlexibility.Analysis.OneHighCylinderFourierRadial
import ContinuousFlexibility.Analysis.OneHighCylinderSobolevWeights

/-!
# Actual mixed jets and physical cylinder Sobolev norms

The jet data record genuine coordinate derivatives and continuity. There
are no square-integrability or norm-estimate fields: finite Sobolev
regularity is supplied separately and derivative membership is proved.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory
open scoped ENNReal

/-- A continuous mixed derivative tower on the full physical cylinder. -/
structure CylinderSmoothJet (P : ℝ) (E : Type* := ℂ)
    [NormedAddCommGroup E] [NormedSpace ℝ E] where
  jet : ℕ → ℕ → (ℝ × AddCircle P) → E
  continuous : ∀ i j, Continuous (jet i j)
  radial : ∀ i j (r : ℝ) (θ : AddCircle P),
    HasDerivAt (fun x : ℝ => jet i j (x, θ)) (jet (i + 1) j (r, θ)) r
  angular : ∀ i j (r x : ℝ),
    HasDerivAt (fun y : ℝ => jet i j (r, (y : AddCircle P)))
      (jet i (j + 1) (r, (x : AddCircle P))) x

variable {P : ℝ} [Fact (0 < P)]

/-- The physical Bessel Sobolev norm of the actual cylinder Fourier transform. -/
abbrev cylinderSobolevNorm (s : ℝ) (f : ℝ × AddCircle P → ℂ) (hf : Continuous f)
    (hf2 : MemLp f 2 (cylinderPhysicalMeasure P)) : ℝ :=
  frequencySobolevNorm cylinderFrequencyMeasure
    (cylinderFrequencyWeight (2 * Real.pi) (2 * Real.pi / P)) s
      (cylinderFourier f hf hf2)

/-- Actual membership in the physical Fourier Sobolev space. -/
def CylinderSmoothJet.MemSobolev (u : CylinderSmoothJet P) (s : ℕ)
    (hu2 : MemLp (u.jet 0 0) 2 (cylinderPhysicalMeasure P)) : Prop :=
  MemLp (frequencyWeighted
    (cylinderFrequencyWeight (2 * Real.pi) (2 * Real.pi / P)) s
    (cylinderFourier (u.jet 0 0) (u.continuous 0 0) hu2)) 2 cylinderFrequencyMeasure

end ContinuousFlexibility.Analysis
