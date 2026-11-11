import ContinuousFlexibility.Analysis.OneHighCylinderFourierCutoffJets
import ContinuousFlexibility.Analysis.OneHighCylinderFrequencyApproximation
import ContinuousFlexibility.Analysis.OneHighCylinderFourierLinearity
import ContinuousFlexibility.Analysis.OneHighCylinderSobolevJets

/-!
# Finite-order approximation of the actual physical cylinder jets

The cutoff inverse converges in physical L2 to each original mixed derivative
of total order at most the single assumed Sobolev order. This follows from
frequency dominated convergence, the genuine derivative multiplier identity,
and exact Plancherel for differences. The original function has no assumed
all-order square-integrability.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory Filter
open scoped ENNReal Topology

variable {P : ℝ} [Fact (0 < P)]

theorem cylinderCutoffJet_tendsto_derivative_l2 (u : CylinderSmoothJet P)
    (hu2 : MemLp (u.jet 0 0) 2 (cylinderPhysicalMeasure P))
    {s i j : ℕ} (hs : u.MemSobolev s hu2)
    (hF1 : Integrable (cylinderFourier (u.jet 0 0) (u.continuous 0 0) hu2)
      cylinderFrequencyMeasure) (hij : i + j ≤ s) :
    Tendsto (fun N : ℕ => (eLpNorm (fun p =>
      (cylinderCutoffJet (P := P) (cylinderFourier (u.jet 0 0) (u.continuous 0 0) hu2)
        (measurable_cylinderFourier (u.jet 0 0) (u.continuous 0 0) hu2) hF1 N).jet i j p -
          u.jet i j p) 2 (cylinderPhysicalMeasure P)).toReal) atTop (𝓝 0) := by
  let F := cylinderFourier (u.jet 0 0) (u.continuous 0 0) hu2
  have hF : Measurable F := measurable_cylinderFourier (u.jet 0 0) (u.continuous 0 0) hu2
  have hF2 : MemLp F 2 cylinderFrequencyMeasure :=
    cylinderFourier_memLp_two (u.jet 0 0) (u.continuous 0 0) hu2
  have hM2 : MemLp (fun ζ => cylinderDerivativeMultiplier P i j ζ * F ζ)
      2 cylinderFrequencyMeasure := cylinderDerivativeMultiplier_mul_memLp (P := P) hF hij hs
  have he (N : ℕ) : eLpNorm
      (fun p => (cylinderCutoffJet (P := P) F hF hF1 N).jet i j p - u.jet i j p)
        2 (cylinderPhysicalMeasure P) =
      eLpNorm (fun ζ => cylinderFrequencyCutoff (P := P) N
        (fun η => cylinderDerivativeMultiplier P i j η * F η) ζ -
          cylinderDerivativeMultiplier P i j ζ * F ζ) 2 cylinderFrequencyMeasure := by
    rw [cylinderFourier_sub_eLpNorm_two _ _
      ((cylinderCutoffJet (P := P) F hF hF1 N).continuous i j) (u.continuous i j)
      (cylinderCutoffJet_memLp_two (P := P) hF hF1 hF2 N i j) (u.memLp_derivative hu2 hs hij)]
    apply eLpNorm_congr_ae
    filter_upwards [cylinderCutoffJet_fourier_ae (P := P) hF hF1 hF2 N i j,
      u.fourier_derivative_ae hu2 hs hij] with ζ hN hU
    rw [hN, hU]
    simpa only [cylinderFrequencyCutoffJet] using congrArg
      (fun z : ℂ => z - cylinderDerivativeMultiplier P i j ζ * F ζ)
      (congrFun (cylinderFrequencyCutoff_mul_left (P := P) N
        (cylinderDerivativeMultiplier P i j) F) ζ)
  change Tendsto (fun N : ℕ => (eLpNorm
    (fun p => (cylinderCutoffJet (P := P) F hF hF1 N).jet i j p - u.jet i j p)
      2 (cylinderPhysicalMeasure P)).toReal) atTop (𝓝 0)
  simpa only [he] using (cylinderFrequencyCutoff_tendsto_l2 (P := P) hM2)

/-- Canonical bounded-frequency approximation of an actual physical jet. -/
def CylinderSmoothJet.frequencyCutoff (u : CylinderSmoothJet P)
    (hu2 : MemLp (u.jet 0 0) 2 (cylinderPhysicalMeasure P))
    (hF1 : MemLp (cylinderFourier (u.jet 0 0) (u.continuous 0 0) hu2)
      1 cylinderFrequencyMeasure) (N : ℕ) : CylinderSmoothJet P :=
  cylinderCutoffJet (P := P) (cylinderFourier (u.jet 0 0) (u.continuous 0 0) hu2)
    (measurable_cylinderFourier (u.jet 0 0) (u.continuous 0 0) hu2)
    (memLp_one_iff_integrable.mp hF1) N

theorem CylinderSmoothJet.frequencyCutoff_memLp (u : CylinderSmoothJet P)
    (hu2 : MemLp (u.jet 0 0) 2 (cylinderPhysicalMeasure P))
    (hF1 : MemLp (cylinderFourier (u.jet 0 0) (u.continuous 0 0) hu2)
      1 cylinderFrequencyMeasure) (N i j : ℕ) :
    MemLp ((u.frequencyCutoff hu2 hF1 N).jet i j) 2 (cylinderPhysicalMeasure P) :=
  cylinderCutoffJet_memLp_two (P := P)
    (measurable_cylinderFourier (u.jet 0 0) (u.continuous 0 0) hu2)
    (memLp_one_iff_integrable.mp hF1)
    (cylinderFourier_memLp_two (u.jet 0 0) (u.continuous 0 0) hu2) N i j

theorem CylinderSmoothJet.frequencyCutoff_memSobolev (u : CylinderSmoothJet P)
    (hu2 : MemLp (u.jet 0 0) 2 (cylinderPhysicalMeasure P))
    (hF1 : MemLp (cylinderFourier (u.jet 0 0) (u.continuous 0 0) hu2)
      1 cylinderFrequencyMeasure) (N s : ℕ) :
    (u.frequencyCutoff hu2 hF1 N).MemSobolev s (u.frequencyCutoff_memLp hu2 hF1 N 0 0) :=
  cylinderCutoffJet_memSobolev_all (P := P)
    (measurable_cylinderFourier (u.jet 0 0) (u.continuous 0 0) hu2)
    (memLp_one_iff_integrable.mp hF1)
    (cylinderFourier_memLp_two (u.jet 0 0) (u.continuous 0 0) hu2) N s

theorem CylinderSmoothJet.frequencyCutoff_fourier_memLp_one (u : CylinderSmoothJet P)
    (hu2 : MemLp (u.jet 0 0) 2 (cylinderPhysicalMeasure P))
    (hF1 : MemLp (cylinderFourier (u.jet 0 0) (u.continuous 0 0) hu2)
      1 cylinderFrequencyMeasure) (N i j : ℕ) :
    MemLp (cylinderFourier ((u.frequencyCutoff hu2 hF1 N).jet i j)
      ((u.frequencyCutoff hu2 hF1 N).continuous i j)
      (u.frequencyCutoff_memLp hu2 hF1 N i j)) 1 cylinderFrequencyMeasure :=
  cylinderCutoffJet_fourier_memLp_one (P := P)
    (measurable_cylinderFourier (u.jet 0 0) (u.continuous 0 0) hu2)
    (memLp_one_iff_integrable.mp hF1)
    (cylinderFourier_memLp_two (u.jet 0 0) (u.continuous 0 0) hu2) N i j

theorem CylinderSmoothJet.frequencyCutoff_sobolev_le (u : CylinderSmoothJet P)
    (hu2 : MemLp (u.jet 0 0) 2 (cylinderPhysicalMeasure P))
    {s : ℕ} (hs : u.MemSobolev s hu2)
    (hF1 : MemLp (cylinderFourier (u.jet 0 0) (u.continuous 0 0) hu2)
      1 cylinderFrequencyMeasure) (N : ℕ) :
    cylinderSobolevNorm s ((u.frequencyCutoff hu2 hF1 N).jet 0 0)
      ((u.frequencyCutoff hu2 hF1 N).continuous 0 0)
      (u.frequencyCutoff_memLp hu2 hF1 N 0 0) ≤
        cylinderSobolevNorm s (u.jet 0 0) (u.continuous 0 0) hu2 :=
  cylinderCutoffJet_sobolev_le (P := P)
    (measurable_cylinderFourier (u.jet 0 0) (u.continuous 0 0) hu2)
    (memLp_one_iff_integrable.mp hF1)
    (cylinderFourier_memLp_two (u.jet 0 0) (u.continuous 0 0) hu2) N s hs

theorem CylinderSmoothJet.frequencyCutoff_fourierL1_le (u : CylinderSmoothJet P)
    (hu2 : MemLp (u.jet 0 0) 2 (cylinderPhysicalMeasure P))
    (hF1 : MemLp (cylinderFourier (u.jet 0 0) (u.continuous 0 0) hu2)
      1 cylinderFrequencyMeasure) (N : ℕ) :
    frequencyL1Norm cylinderFrequencyMeasure
      (cylinderFourier ((u.frequencyCutoff hu2 hF1 N).jet 0 0)
        ((u.frequencyCutoff hu2 hF1 N).continuous 0 0)
        (u.frequencyCutoff_memLp hu2 hF1 N 0 0)) ≤
      frequencyL1Norm cylinderFrequencyMeasure
        (cylinderFourier (u.jet 0 0) (u.continuous 0 0) hu2) :=
  cylinderCutoffJet_fourierL1_le (P := P)
    (measurable_cylinderFourier (u.jet 0 0) (u.continuous 0 0) hu2)
    (memLp_one_iff_integrable.mp hF1)
    (cylinderFourier_memLp_two (u.jet 0 0) (u.continuous 0 0) hu2) N

/-- Every derivative permitted by the original finite Sobolev order converges
in the actual physical cylinder L2 norm. -/
theorem CylinderSmoothJet.frequencyCutoff_tendsto_derivative_l2 (u : CylinderSmoothJet P)
    (hu2 : MemLp (u.jet 0 0) 2 (cylinderPhysicalMeasure P))
    {s i j : ℕ} (hs : u.MemSobolev s hu2)
    (hF1 : MemLp (cylinderFourier (u.jet 0 0) (u.continuous 0 0) hu2)
      1 cylinderFrequencyMeasure) (hij : i + j ≤ s) :
    Tendsto (fun N : ℕ => (eLpNorm
      (fun p => (u.frequencyCutoff hu2 hF1 N).jet i j p - u.jet i j p)
        2 (cylinderPhysicalMeasure P)).toReal) atTop (𝓝 0) :=
  cylinderCutoffJet_tendsto_derivative_l2 u hu2 hs (memLp_one_iff_integrable.mp hF1) hij

end ContinuousFlexibility.Analysis
