import ContinuousFlexibility.Analysis.OneHighCylinderCutoffProducts
import ContinuousFlexibility.Analysis.OneHighCylinderFourierApproximation
import ContinuousFlexibility.Analysis.OneHighL2ProductLimit

/-!
# The full actual cylinder one-high-factor product estimate

The input functions have only the requested finite Sobolev regularity.
Genuine bounded-frequency approximants have the exact uniform product
estimate. Their actual derivatives converge in L2, and the common
almost-everywhere subsequence and Fatou lemma preserve the bound for the
original derivative product.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory Filter
open scoped ENNReal BigOperators

variable {P : ℝ} [Fact (0 < P)]

/-- The arbitrary-positive-arity, distributed mixed-derivative product
estimate on the full physical cylinder, with exact constant one in the
chosen Fourier normalization. -/
theorem cylinder_derivative_product_oneHigh (k s : ℕ)
    (u : Fin (k + 1) → CylinderSmoothJet P)
    (hu2 : ∀ i, MemLp ((u i).jet 0 0) 2 (cylinderPhysicalMeasure P))
    (hs : ∀ i, (u i).MemSobolev s (hu2 i))
    (hF1 : ∀ i, MemLp
      (cylinderFourier ((u i).jet 0 0) ((u i).continuous 0 0) (hu2 i))
        1 cylinderFrequencyMeasure)
    (a b : Fin (k + 1) → ℕ) (hab : ∑ i, (a i + b i) ≤ s) :
    MemLp (fun p : ℝ × AddCircle P => ∏ i, (u i).jet (a i) (b i) p)
      2 (cylinderPhysicalMeasure P) ∧
    (eLpNorm (fun p : ℝ × AddCircle P => ∏ i, (u i).jet (a i) (b i) p)
      2 (cylinderPhysicalMeasure P)).toReal ≤
      ∑ j, cylinderSobolevNorm s ((u j).jet 0 0) ((u j).continuous 0 0) (hu2 j) *
        ∏ i ∈ Finset.univ.erase j, frequencyL1Norm cylinderFrequencyMeasure
          (cylinderFourier ((u i).jet 0 0) ((u i).continuous 0 0) (hu2 i)) := by
  classical
  let F (i : Fin (k + 1)) : ℝ × ℤ → ℂ :=
    cylinderFourier ((u i).jet 0 0) ((u i).continuous 0 0) (hu2 i)
  have hFm (i : Fin (k + 1)) : Measurable (F i) :=
    measurable_cylinderFourier ((u i).jet 0 0) ((u i).continuous 0 0) (hu2 i)
  have hF2 (i : Fin (k + 1)) : MemLp (F i) 2 cylinderFrequencyMeasure :=
    cylinderFourier_memLp_two ((u i).jet 0 0) ((u i).continuous 0 0) (hu2 i)
  have hFs (i : Fin (k + 1)) : MemLp (frequencyWeighted
      (cylinderFrequencyWeight (2 * Real.pi) (2 * Real.pi / P)) (s : ℝ) (F i))
        2 cylinderFrequencyMeasure := hs i
  have hi (i : Fin (k + 1)) : a i + b i ≤ s :=
    (Finset.single_le_sum (f := fun i => a i + b i)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans hab
  let v : ℕ → Fin (k + 1) → (ℝ × AddCircle P) → ℂ :=
    fun N i => ((u i).frequencyCutoff (hu2 i) (hF1 i) N).jet (a i) (b i)
  have hv (N : ℕ) (i : Fin (k + 1)) :
      MemLp (v N i) 2 (cylinderPhysicalMeasure P) :=
    (u i).frequencyCutoff_memLp (hu2 i) (hF1 i) N (a i) (b i)
  have hf (i : Fin (k + 1)) :
      MemLp ((u i).jet (a i) (b i)) 2 (cylinderPhysicalMeasure P) :=
    (u i).memLp_derivative (hu2 i) (hs i) (hi i)
  have hlim (i : Fin (k + 1)) : Tendsto
      (fun N => (eLpNorm (fun p => v N i p - (u i).jet (a i) (b i) p)
        2 (cylinderPhysicalMeasure P)).toReal) atTop (𝓝 0) :=
    (u i).frequencyCutoff_tendsto_derivative_l2 (hu2 i) (hs i) (hF1 i) (hi i)
  let C : ℝ≥0∞ := ∑ j, eLpNorm (frequencyWeighted
      (cylinderFrequencyWeight (2 * Real.pi) (2 * Real.pi / P)) (s : ℝ) (F j))
        2 cylinderFrequencyMeasure *
      ∏ i ∈ Finset.univ.erase j, eLpNorm (F i) 1 cylinderFrequencyMeasure
  have hterm (j : Fin (k + 1)) : eLpNorm (frequencyWeighted
      (cylinderFrequencyWeight (2 * Real.pi) (2 * Real.pi / P)) (s : ℝ) (F j))
        2 cylinderFrequencyMeasure *
      (∏ i ∈ Finset.univ.erase j, eLpNorm (F i) 1 cylinderFrequencyMeasure) < ⊤ :=
    ENNReal.mul_lt_top (hFs j) (ENNReal.prod_lt_top (fun i _ => hF1 i))
  have hC : C < ⊤ := ENNReal.sum_lt_top.mpr (fun j _ => hterm j)
  have hbound (N : ℕ) :
      eLpNorm (fun p => ∏ i, v N i p) 2 (cylinderPhysicalMeasure P) ≤ C := by
    have h := cylinder_cutoff_derivative_product_oneHigh (P := P) k s N hFm hF1 hF2 a b hab
    simpa only [v, CylinderSmoothJet.frequencyCutoff, F, C] using h.2
  have hlimit := oneHigh_l2_product_limit (μ := cylinderPhysicalMeasure P)
    v (fun i => (u i).jet (a i) (b i)) hv hf hlim C hC hbound
  refine ⟨hlimit.1, ?_⟩
  calc
    _ ≤ C.toReal := ENNReal.toReal_mono hC.ne hlimit.2
    _ = _ := by
      dsimp only [C]
      rw [ENNReal.toReal_sum (fun j _ => (hterm j).ne)]
      simp only [ENNReal.toReal_mul, ENNReal.toReal_prod, cylinderSobolevNorm,
        frequencySobolevNorm, frequencyL1Norm, F]

end ContinuousFlexibility.Analysis
