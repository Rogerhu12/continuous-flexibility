import ContinuousFlexibility.Analysis.N07aAngularTests
import ContinuousFlexibility.Analysis.N07aAngularCutoff

/-!
# Removing radial support from the actual weak Fourier identity

Only the test functions, not the source classes, are truncated. Their
angular derivatives have the same exact multiplier for every cutoff.
Dominated convergence therefore gives the full separated Fourier
identity on each bounded canonical interval.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory ContinuousFlexibility.Analysis
open scoped ENNReal ContDiff Topology

variable {S : PhysicalSpacesData} {K : CanonicalData S}

theorem n07aAngularWeak_fourier_pairing_full (m : ℕ) (hm : K.left m < K.right m)
    {f g : CanonicalL2 S K m} {j : ℕ}
    (hfg : WeakCanonicalAngularDerivative S K m f g j)
    {η : ℝ → ℂ} (hη : ContDiff ℝ ∞ η) (n : ℤ) :
    (∫ p, n07aAngularWave η (-n) p * (g p : ℂ) ∂canonicalMeasure S K m) =
      (2 * Complex.I * (n : ℂ)) ^ j *
        ∫ p, n07aAngularWave η (-n) p * (f p : ℂ) ∂canonicalMeasure S K m := by
  let χ (k : ℕ) : ℝ → ℝ := n07aAngularIntervalCutoff (K.left m) (K.right m) hm k
  let ηk (k : ℕ) : ℝ → ℂ := fun r => (χ k r : ℂ) * η r
  have hηk (k : ℕ) : ContDiff ℝ ∞ (ηk k) :=
    (Complex.ofRealCLM.contDiff.comp
      (n07aAngularIntervalCutoff_contDiff _ _ hm k)).mul hη
  have heq (k : ℕ) :
      (∫ p, n07aAngularWave (ηk k) (-n) p * (g p : ℂ) ∂canonicalMeasure S K m) =
        (2 * Complex.I * (n : ℂ)) ^ j *
          ∫ p, n07aAngularWave (ηk k) (-n) p * (f p : ℂ) ∂canonicalMeasure S K m := by
    apply n07aAngularWeak_fourier_pairing m hfg (hηk k)
      (n07aAngularIntervalCutoff_compact _ _ hm k)
      (n07aAngularIntervalCutoff_tsupport _ _ hm k)
    intro r hr
    have hz : χ k r = 0 := image_eq_zero_of_notMem_tsupport hr
    simp only [ηk, hz, Complex.ofReal_zero, zero_mul]
  have ht (u : CanonicalL2 S K m) :
      Tendsto (fun k => ∫ p, n07aAngularWave (ηk k) (-n) p * (u p : ℂ)
        ∂canonicalMeasure S K m) atTop
        (𝓝 (∫ p, n07aAngularWave η (-n) p * (u p : ℂ) ∂canonicalMeasure S K m)) := by
    have h := n07aAngularIntervalCutoff_integral_tendsto m hm
      (n07aAngularWave_integrable_mul m hη (-n) u)
    have he (k : ℕ) :
        (fun p => n07aAngularIntervalCutoff (K.left m) (K.right m) hm k p.1 •
          (n07aAngularWave η (-n) p * (u p : ℂ))) =
        (fun p => n07aAngularWave (ηk k) (-n) p * (u p : ℂ)) := by
      funext p
      simp only [n07aAngularWave, ηk, χ, Complex.real_smul]
      ring
    simpa only [he] using h
  have ht' := (ht f).const_mul ((2 * Complex.I * (n : ℂ)) ^ j)
  exact tendsto_nhds_unique (ht g) (ht'.congr' (Eventually.of_forall fun k => (heq k).symm))

end ContinuousFlexibility.Statements
