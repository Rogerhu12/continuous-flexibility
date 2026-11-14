module

public import ContinuousFlexibility.Analysis.OneHighCylinderFourierCutoff
public import ContinuousFlexibility.Analysis.OneHighCylinderFourierInverseDerivatives
public import ContinuousFlexibility.Analysis.OneHighCylinderFourierInverseL2
public import ContinuousFlexibility.Analysis.OneHighCylinderSobolevJetsBasic

/-!
# Genuine smooth cylinder approximants from finite frequency data

The cutoff is applied to the actual mixed Fourier data. Integrability of the
original data supplies every moment on bounded frequency support. Thus every
displayed jet is an actual coordinate derivative of the inverse integral.
No derivative membership of the original data is assumed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory Filter
open scoped ENNReal

variable {P : ℝ} [Fact (0 < P)]

/-- The exact physical multiplier of a cutoff mixed derivative. -/
def cylinderFrequencyCutoffJet (N : ℕ) (F : ℝ × ℤ → ℂ) (i j : ℕ) :
    ℝ × ℤ → ℂ :=
  fun ζ => cylinderDerivativeMultiplier P i j ζ * cylinderFrequencyCutoff (P := P) N F ζ

@[simp]
theorem cylinderFrequencyCutoffJet_zero_zero (N : ℕ) (F : ℝ × ℤ → ℂ) :
    cylinderFrequencyCutoffJet (P := P) N F 0 0 = cylinderFrequencyCutoff (P := P) N F := by
  funext ζ
  simp only [cylinderFrequencyCutoffJet, cylinderDerivativeMultiplier_zero_zero, one_mul]

theorem cylinderFrequencyCutoffJet_radial (N : ℕ) (F : ℝ × ℤ → ℂ) (i j : ℕ) :
    (fun ζ => cylinderDerivativeMultiplier P 1 0 ζ *
      cylinderFrequencyCutoffJet (P := P) N F i j ζ) =
        cylinderFrequencyCutoffJet (P := P) N F (i + 1) j := by
  funext ζ
  simp only [cylinderFrequencyCutoffJet, ← mul_assoc, cylinderDerivativeMultiplier_mul,
    Nat.zero_add, Nat.add_comm 1 i]

theorem cylinderFrequencyCutoffJet_angular (N : ℕ) (F : ℝ × ℤ → ℂ) (i j : ℕ) :
    (fun ζ => cylinderDerivativeMultiplier P 0 1 ζ *
      cylinderFrequencyCutoffJet (P := P) N F i j ζ) =
        cylinderFrequencyCutoffJet (P := P) N F i (j + 1) := by
  funext ζ
  simp only [cylinderFrequencyCutoffJet, ← mul_assoc, cylinderDerivativeMultiplier_mul,
    Nat.zero_add, Nat.add_comm 1 j]

theorem measurable_cylinderFrequencyCutoffJet {F : ℝ × ℤ → ℂ}
    (hF : Measurable F) (N i j : ℕ) :
    Measurable (cylinderFrequencyCutoffJet (P := P) N F i j) :=
  (measurable_cylinderDerivativeMultiplier P i j).mul
    (measurable_cylinderFrequencyCutoff (P := P) hF N)

theorem integrable_cylinderFrequencyCutoffJet {F : ℝ × ℤ → ℂ}
    (hF : Measurable F) (hF1 : Integrable F cylinderFrequencyMeasure) (N i j : ℕ) :
    Integrable (cylinderFrequencyCutoffJet (P := P) N F i j) cylinderFrequencyMeasure :=
  integrable_cylinderMultiplier_cutoff (P := P) hF hF1 N i j

theorem cylinderFrequencyCutoffJet_memLp_two {F : ℝ × ℤ → ℂ}
    (hF : Measurable F) (hF2 : MemLp F 2 cylinderFrequencyMeasure) (N i j : ℕ) :
    MemLp (cylinderFrequencyCutoffJet (P := P) N F i j) 2 cylinderFrequencyMeasure :=
  cylinderMultiplier_cutoff_memLp_two (P := P) hF hF2 N i j

/-- The complete, genuine derivative tower of the cutoff inverse. -/
def cylinderCutoffJet (F : ℝ × ℤ → ℂ) (hF : Measurable F)
    (hF1 : Integrable F cylinderFrequencyMeasure) (N : ℕ) : CylinderSmoothJet P where
  jet i j := cylinderFourierInverse (P := P) (cylinderFrequencyCutoffJet (P := P) N F i j)
  continuous i j :=
    continuous_cylinderFourierInverse (P := P) (integrable_cylinderFrequencyCutoffJet (P := P) hF hF1 N i j)
  radial i j r θ := by
    have hd : Integrable (fun ζ => cylinderDerivativeMultiplier P 1 0 ζ *
        cylinderFrequencyCutoffJet (P := P) N F i j ζ) cylinderFrequencyMeasure := by
      rw [cylinderFrequencyCutoffJet_radial]
      exact integrable_cylinderFrequencyCutoffJet (P := P) hF hF1 N (i + 1) j
    simpa only [cylinderFrequencyCutoffJet_radial] using
      cylinderFourierInverse_hasDerivAt_radial (P := P)
        (integrable_cylinderFrequencyCutoffJet (P := P) hF hF1 N i j) hd r θ
  angular i j r x := by
    have hd : Integrable (fun ζ => cylinderDerivativeMultiplier P 0 1 ζ *
        cylinderFrequencyCutoffJet (P := P) N F i j ζ) cylinderFrequencyMeasure := by
      rw [cylinderFrequencyCutoffJet_angular]
      exact integrable_cylinderFrequencyCutoffJet (P := P) hF hF1 N i (j + 1)
    simpa only [cylinderFrequencyCutoffJet_angular] using
      cylinderFourierInverse_hasDerivAt_angular (P := P)
        (integrable_cylinderFrequencyCutoffJet (P := P) hF hF1 N i j) hd r x

@[simp]
theorem cylinderCutoffJet_zero_zero (F : ℝ × ℤ → ℂ) (hF : Measurable F)
    (hF1 : Integrable F cylinderFrequencyMeasure) (N : ℕ) :
    (cylinderCutoffJet (P := P) F hF hF1 N).jet 0 0 =
      cylinderFourierInverse (P := P) (cylinderFrequencyCutoff (P := P) N F) := by
  change cylinderFourierInverse (P := P) (cylinderFrequencyCutoffJet (P := P) N F 0 0) = _
  rw [cylinderFrequencyCutoffJet_zero_zero]

theorem cylinderCutoffJet_memLp_two {F : ℝ × ℤ → ℂ} (hF : Measurable F)
    (hF1 : Integrable F cylinderFrequencyMeasure)
    (hF2 : MemLp F 2 cylinderFrequencyMeasure) (N i j : ℕ) :
    MemLp ((cylinderCutoffJet (P := P) F hF hF1 N).jet i j) 2 (cylinderPhysicalMeasure P) :=
  cylinderFourierInverse_memLp_two (P := P)
    (measurable_cylinderFrequencyCutoffJet (P := P) hF N i j)
    (integrable_cylinderFrequencyCutoffJet (P := P) hF hF1 N i j)
    (cylinderFrequencyCutoffJet_memLp_two (P := P) hF hF2 N i j)

theorem cylinderCutoffJet_fourier_ae {F : ℝ × ℤ → ℂ} (hF : Measurable F)
    (hF1 : Integrable F cylinderFrequencyMeasure)
    (hF2 : MemLp F 2 cylinderFrequencyMeasure) (N i j : ℕ) :
    cylinderFourier ((cylinderCutoffJet (P := P) F hF hF1 N).jet i j)
      ((cylinderCutoffJet (P := P) F hF hF1 N).continuous i j)
      (cylinderCutoffJet_memLp_two (P := P) hF hF1 hF2 N i j) =ᵐ[cylinderFrequencyMeasure]
        cylinderFrequencyCutoffJet (P := P) N F i j :=
  cylinderFourier_inverse_ae (P := P)
    (measurable_cylinderFrequencyCutoffJet (P := P) hF N i j)
    (integrable_cylinderFrequencyCutoffJet (P := P) hF hF1 N i j)
    (cylinderFrequencyCutoffJet_memLp_two (P := P) hF hF2 N i j)

theorem cylinderCutoffJet_memSobolev {F : ℝ × ℤ → ℂ} (hF : Measurable F)
    (hF1 : Integrable F cylinderFrequencyMeasure)
    (hF2 : MemLp F 2 cylinderFrequencyMeasure) (N s : ℕ)
    (hs : MemLp (frequencyWeighted
      (cylinderFrequencyWeight (2 * Real.pi) (2 * Real.pi / P)) (s : ℝ) F)
        2 cylinderFrequencyMeasure) :
    (cylinderCutoffJet (P := P) F hF hF1 N).MemSobolev s
      (cylinderCutoffJet_memLp_two (P := P) hF hF1 hF2 N 0 0) := by
  apply (memLp_congr_ae ?_).mpr (cylinderFrequencyCutoff_weighted_memLp (P := P) hs N)
  filter_upwards [cylinderCutoffJet_fourier_ae (P := P) hF hF1 hF2 N 0 0] with ζ hζ
  simpa only [frequencyWeighted_apply, cylinderFrequencyCutoffJet,
    cylinderDerivativeMultiplier_zero_zero, one_mul] using congrArg
      (fun z : ℂ => (cylinderFrequencyWeight (2 * Real.pi) (2 * Real.pi / P) ζ ^
        (s : ℝ) : ℝ) • z) hζ

theorem cylinderCutoffJet_sobolev_le {F : ℝ × ℤ → ℂ} (hF : Measurable F)
    (hF1 : Integrable F cylinderFrequencyMeasure)
    (hF2 : MemLp F 2 cylinderFrequencyMeasure) (N s : ℕ)
    (hs : MemLp (frequencyWeighted
      (cylinderFrequencyWeight (2 * Real.pi) (2 * Real.pi / P)) (s : ℝ) F)
        2 cylinderFrequencyMeasure) :
    cylinderSobolevNorm s ((cylinderCutoffJet (P := P) F hF hF1 N).jet 0 0)
      ((cylinderCutoffJet (P := P) F hF hF1 N).continuous 0 0)
      (cylinderCutoffJet_memLp_two (P := P) hF hF1 hF2 N 0 0) ≤
      frequencySobolevNorm cylinderFrequencyMeasure
        (cylinderFrequencyWeight (2 * Real.pi) (2 * Real.pi / P)) s F := by
  have he : frequencyWeighted
      (cylinderFrequencyWeight (2 * Real.pi) (2 * Real.pi / P)) (s : ℝ)
      (cylinderFourier ((cylinderCutoffJet (P := P) F hF hF1 N).jet 0 0)
        ((cylinderCutoffJet (P := P) F hF hF1 N).continuous 0 0)
        (cylinderCutoffJet_memLp_two (P := P) hF hF1 hF2 N 0 0)) =ᵐ[cylinderFrequencyMeasure]
      frequencyWeighted (cylinderFrequencyWeight (2 * Real.pi) (2 * Real.pi / P))
        (s : ℝ) (cylinderFrequencyCutoff (P := P) N F) := by
    filter_upwards [cylinderCutoffJet_fourier_ae (P := P) hF hF1 hF2 N 0 0] with ζ hζ
    simp only [cylinderFrequencyCutoffJet, cylinderDerivativeMultiplier_zero_zero, one_mul] at hζ
    exact congrArg (fun z : ℂ => (cylinderFrequencyWeight
      (2 * Real.pi) (2 * Real.pi / P) ζ ^ (s : ℝ) : ℝ) • z) hζ
  change (eLpNorm _ 2 cylinderFrequencyMeasure).toReal ≤ _
  rw [eLpNorm_congr_ae he]
  exact cylinderFrequencyCutoff_sobolev_le (P := P) hs N

theorem cylinderCutoffJet_fourierL1_le {F : ℝ × ℤ → ℂ} (hF : Measurable F)
    (hF1 : Integrable F cylinderFrequencyMeasure)
    (hF2 : MemLp F 2 cylinderFrequencyMeasure) (N : ℕ) :
    frequencyL1Norm cylinderFrequencyMeasure
      (cylinderFourier ((cylinderCutoffJet (P := P) F hF hF1 N).jet 0 0)
        ((cylinderCutoffJet (P := P) F hF hF1 N).continuous 0 0)
        (cylinderCutoffJet_memLp_two (P := P) hF hF1 hF2 N 0 0)) ≤
      frequencyL1Norm cylinderFrequencyMeasure F := by
  have he := cylinderCutoffJet_fourier_ae (P := P) hF hF1 hF2 N 0 0
  rw [cylinderFrequencyCutoffJet_zero_zero] at he
  change (eLpNorm _ 1 cylinderFrequencyMeasure).toReal ≤ _
  rw [eLpNorm_congr_ae he]
  exact cylinderFrequencyCutoff_fourierL1_le (P := P) (memLp_one_iff_integrable.mpr hF1) N

/-- Bounded frequency support gives all-order membership of the genuine
cutoff tower, independently of the regularity order of the original data. -/
theorem cylinderCutoffJet_memSobolev_all {F : ℝ × ℤ → ℂ} (hF : Measurable F)
    (hF1 : Integrable F cylinderFrequencyMeasure)
    (hF2 : MemLp F 2 cylinderFrequencyMeasure) (N s : ℕ) :
    (cylinderCutoffJet (P := P) F hF hF1 N).MemSobolev s
      (cylinderCutoffJet_memLp_two (P := P) hF hF1 hF2 N 0 0) := by
  apply (memLp_congr_ae ?_).mpr (cylinderFrequencyCutoff_weighted_memLp_all (P := P) hF hF2 N s)
  filter_upwards [cylinderCutoffJet_fourier_ae (P := P) hF hF1 hF2 N 0 0] with ζ hζ
  simp only [cylinderFrequencyCutoffJet, cylinderDerivativeMultiplier_zero_zero, one_mul] at hζ
  exact congrArg (fun z : ℂ => (cylinderFrequencyWeight
    (2 * Real.pi) (2 * Real.pi / P) ζ ^ (s : ℝ) : ℝ) • z) hζ

theorem cylinderCutoffJet_fourier_memLp_one {F : ℝ × ℤ → ℂ} (hF : Measurable F)
    (hF1 : Integrable F cylinderFrequencyMeasure)
    (hF2 : MemLp F 2 cylinderFrequencyMeasure) (N i j : ℕ) :
    MemLp (cylinderFourier ((cylinderCutoffJet (P := P) F hF hF1 N).jet i j)
      ((cylinderCutoffJet (P := P) F hF hF1 N).continuous i j)
      (cylinderCutoffJet_memLp_two (P := P) hF hF1 hF2 N i j)) 1 cylinderFrequencyMeasure :=
  (memLp_congr_ae (cylinderCutoffJet_fourier_ae (P := P) hF hF1 hF2 N i j)).mpr
    (memLp_one_iff_integrable.mpr (integrable_cylinderFrequencyCutoffJet (P := P) hF hF1 N i j))

end ContinuousFlexibility.Analysis
